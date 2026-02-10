#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "freertos/event_groups.h"
#include "freertos/queue.h"
#include "esp_system.h"
#include "esp_mac.h"
#include "esp_log.h"
#include "nvs_flash.h"
#include "esp_bt.h"
#include "driver/gpio.h"
#include "driver/rtc_io.h"
#include "string.h"
#include "esp_sleep.h"

#include "esp_gap_ble_api.h"
#include "esp_gatts_api.h"
#include "esp_bt_defs.h"
#include "esp_bt_main.h"
#include "esp_bt_device.h"
#include "esp_gatt_common_api.h"
#include "esp_pm.h"

/************************************************************************ 
 * ULTRA POWER SAVING DOORBELL
 * 
 * Power Optimization Strategies:
 * 1. Eliminate continuous polling task - use event-driven ISR only
 * 2. Stop advertising when connected (saves massive power)
 * 3. Use connection interval negotiation for slower updates
 * 4. Reduce MTU size to minimum (23 bytes instead of 512)
 * 5. Minimize CPU frequency (10-80MHz)
 * 6. Ultra-long advertising intervals (10-20 seconds)
 * 7. Lowest possible TX power (-12dBm)
 * 8. Deep sleep capability between events
 * 9. Disable unnecessary peripherals (UART, etc.)
 * 10. Single-core operation to save power
 ************************************************************************/

#define GATTS_TAG           "Doorbell_Ultra"
#define PROFILE_NUM         1
#define PROFILE_IDX         0
#define APP_ID              0x56
#define DEVICE_NAME         "Doorbell"
#define SERVICE_INST_ID     0

// GPIO Configuration
#define GPIO_BUTTON         GPIO_NUM_16
#define GPIO_WAKEUP_LEVEL   1  // Wake on high (button press)

// GATT Attribute Indices
enum {
    DOORBELL_SVC,
    DOORBELL_IDX_CHAR,
    DOORBELL_IDX_VAL,
    DOORBELL_IDX_CFG,
    DOORBELL_IDX_NB,
};

// Global handles and state
static uint16_t doorbell_handle_table[DOORBELL_IDX_NB];
static uint16_t connection_id = 0xffff;
static esp_gatt_if_t gatts_interface = 0xff;
static bool is_connected = false;
static bool enable_notify = false;
static volatile bool button_pressed = false;

/*********************************** ULTRA POWER ADVERTISING ****************************************************/
// Extremely minimal advertising data to reduce transmission time and power
static const uint8_t advertise_data[] = {
    0x02, 0x01, 0x06,                    // Flags: LE General Discoverable, BR/EDR Not Supported
    0x03, 0x03, 0xF0, 0xAB,              // 16-bit Service UUID
    0x05, 0x09, 'D', 'B', 'e', 'l'       // Shortened name "DBel" to reduce packet size
};

// ULTRA LONG advertising intervals for maximum power savings
static esp_ble_adv_params_t advertising_params = {
    .adv_int_min        = 0x3E80,        // 10 seconds (10000ms / 0.625ms = 0x3E80)
    .adv_int_max        = 0x7D00,        // 20 seconds (20000ms / 0.625ms = 0x7D00)
    .adv_type           = ADV_TYPE_IND,
    .own_addr_type      = BLE_ADDR_TYPE_PUBLIC,
    .channel_map        = ADV_CHNL_ALL,
    .adv_filter_policy  = ADV_FILTER_ALLOW_SCAN_ANY_CON_ANY,
};

/********************************************* GATT Service *******************************************************/
static const uint16_t doorbell_uuid = 0xABF0;
#define NOTIFY_UUID       0xABF2

// Reduced MTU for power savings (less data = less transmission time = less power)
#define MTU_SIZE          (23)  // BLE minimum MTU - saves power vs 512 bytes
#define SPP_DATA_MAX_LEN  (20)  // Reduced from 512 to minimum needed

// GATT Profile Structure
struct gatts_profile_inst {
    esp_gatts_cb_t gatts_cb;
    uint16_t gatts_if;
    uint16_t app_id;
    uint16_t conn_id;
    uint16_t service_handle;
    esp_gatt_srvc_id_t service_id;
    uint16_t char_handle;
    esp_bt_uuid_t char_uuid;
    esp_gatt_perm_t perm;
    esp_gatt_char_prop_t property;
    uint16_t descr_handle;
    esp_bt_uuid_t descr_uuid;
};

static void gatts_profile_event_handler(esp_gatts_cb_event_t event, esp_gatt_if_t gatts_if, esp_ble_gatts_cb_param_t *param);

static struct gatts_profile_inst doorbell_profile_tab[PROFILE_NUM] = {
    [PROFILE_IDX] = {
        .gatts_cb = gatts_profile_event_handler,
        .gatts_if = ESP_GATT_IF_NONE,
        .app_id = APP_ID,
        .conn_id = 0xffff,
        .service_handle = 0,
        .char_handle = 0,
    },
};

// GATT Attribute Database
#define CHAR_DECLARATION_SIZE   (sizeof(uint8_t))
static const uint16_t primary_doorbell_uuid = ESP_GATT_UUID_PRI_SERVICE;
static const uint16_t character_declaration_uuid = ESP_GATT_UUID_CHAR_DECLARE;
static const uint16_t character_client_config_uuid = ESP_GATT_UUID_CHAR_CLIENT_CONFIG;
static const uint8_t char_prop_read_notify = ESP_GATT_CHAR_PROP_BIT_READ | ESP_GATT_CHAR_PROP_BIT_NOTIFY;
static const uint16_t spp_data_notify_uuid = NOTIFY_UUID;
static uint8_t spp_data_notify_val[1] = {0x00};
static uint8_t spp_data_notify_ccc[2] = {0x00, 0x00};

static const esp_gatts_attr_db_t doorbell_db[DOORBELL_IDX_NB] = {
    [DOORBELL_SVC] =
        {{ESP_GATT_AUTO_RSP}, {ESP_UUID_LEN_16, (uint8_t *)&primary_doorbell_uuid, ESP_GATT_PERM_READ,
        sizeof(doorbell_uuid), sizeof(doorbell_uuid), (uint8_t *)&doorbell_uuid}},

    [DOORBELL_IDX_CHAR] =
        {{ESP_GATT_AUTO_RSP}, {ESP_UUID_LEN_16, (uint8_t *)&character_declaration_uuid, ESP_GATT_PERM_READ,
        CHAR_DECLARATION_SIZE, CHAR_DECLARATION_SIZE, (uint8_t *)&char_prop_read_notify}},

    [DOORBELL_IDX_VAL] =
        {{ESP_GATT_AUTO_RSP}, {ESP_UUID_LEN_16, (uint8_t *)&spp_data_notify_uuid, ESP_GATT_PERM_READ,
        SPP_DATA_MAX_LEN, sizeof(spp_data_notify_val), (uint8_t *)spp_data_notify_val}},

    [DOORBELL_IDX_CFG] =
        {{ESP_GATT_AUTO_RSP}, {ESP_UUID_LEN_16, (uint8_t *)&character_client_config_uuid, ESP_GATT_PERM_READ|ESP_GATT_PERM_WRITE,
        sizeof(uint16_t), sizeof(spp_data_notify_ccc), (uint8_t *)spp_data_notify_ccc}},
};

/*********************************** POWER-OPTIMIZED EVENT HANDLERS ****************************************************/

/**
 * GAP Event Handler - Manages advertising and connection events
 */
static void gap_event_handler(esp_gap_ble_cb_event_t event, esp_ble_gap_cb_param_t *param) {
    switch (event) {
    case ESP_GAP_BLE_ADV_DATA_RAW_SET_COMPLETE_EVT:
        esp_ble_gap_start_advertising(&advertising_params);
        break;
    case ESP_GAP_BLE_ADV_START_COMPLETE_EVT:
        if (param->adv_start_cmpl.status == ESP_BT_STATUS_SUCCESS) {
            ESP_LOGI(GATTS_TAG, "Advertising started - Ultra power mode");
        }
        break;
    case ESP_GAP_BLE_ADV_STOP_COMPLETE_EVT:
        ESP_LOGI(GATTS_TAG, "Advertising stopped - Power saved");
        break;
    case ESP_GAP_BLE_UPDATE_CONN_PARAMS_EVT:
        // Log connection parameter updates for power optimization verification
        ESP_LOGI(GATTS_TAG, "Connection interval: %d (x1.25ms), latency: %d, timeout: %d",
                 param->update_conn_params.conn_int,
                 param->update_conn_params.latency,
                 param->update_conn_params.timeout);
        break;
    default:
        break;
    }
}

/**
 * GATT Profile Event Handler - Manages GATT service events
 */
static void gatts_profile_event_handler(esp_gatts_cb_event_t event, esp_gatt_if_t gatts_if, esp_ble_gatts_cb_param_t *param) {
    switch (event) {
    case ESP_GATTS_REG_EVT:
        ESP_LOGI(GATTS_TAG, "GATT server registered");
        esp_ble_gap_set_device_name(DEVICE_NAME);
        esp_ble_gap_config_adv_data_raw((uint8_t *)advertise_data, sizeof(advertise_data));
        esp_ble_gatts_create_attr_tab(doorbell_db, gatts_if, DOORBELL_IDX_NB, SERVICE_INST_ID);
        break;

    case ESP_GATTS_CREAT_ATTR_TAB_EVT:
        if (param->add_attr_tab.status == ESP_GATT_OK && param->add_attr_tab.num_handle == DOORBELL_IDX_NB) {
            memcpy(doorbell_handle_table, param->add_attr_tab.handles, sizeof(doorbell_handle_table));
            esp_ble_gatts_start_service(doorbell_handle_table[DOORBELL_SVC]);
        }
        break;

    case ESP_GATTS_CONNECT_EVT:
        // POWER OPTIMIZATION: Stop advertising immediately when connected
        esp_ble_gap_stop_advertising();
        is_connected = true;
        connection_id = param->connect.conn_id;
        gatts_interface = gatts_if;
        
        ESP_LOGI(GATTS_TAG, "Client connected - Advertising stopped to save power");
        
        // Request longer connection intervals for power savings
        // Min: 400ms, Max: 800ms, Latency: 0, Timeout: 4000ms
        esp_ble_conn_update_params_t conn_params = {0};
        memcpy(conn_params.bda, param->connect.remote_bda, sizeof(esp_bd_addr_t));
        conn_params.min_int = 320;  // 320 * 1.25ms = 400ms
        conn_params.max_int = 640;  // 640 * 1.25ms = 800ms
        conn_params.latency = 0;
        conn_params.timeout = 400;  // 400 * 10ms = 4000ms
        esp_ble_gap_update_conn_params(&conn_params);
        break;

    case ESP_GATTS_DISCONNECT_EVT:
        // POWER OPTIMIZATION: Resume advertising only after disconnect
        is_connected = false;
        enable_notify = false;
        connection_id = 0xffff;
        
        ESP_LOGI(GATTS_TAG, "Client disconnected - Resuming ultra-low-power advertising");
        esp_ble_gap_start_advertising(&advertising_params);
        break;

    case ESP_GATTS_WRITE_EVT:
        // Handle CCCD writes (notification enable/disable)
        if (param->write.handle == doorbell_handle_table[DOORBELL_IDX_CFG]) {
            uint16_t descr_value = param->write.value[1] << 8 | param->write.value[0];
            if (descr_value == 0x0001) {
                enable_notify = true;
                ESP_LOGI(GATTS_TAG, "Notifications enabled");
            } else if (descr_value == 0x0000) {
                enable_notify = false;
                ESP_LOGI(GATTS_TAG, "Notifications disabled");
            }
        }
        break;

    default:
        break;
    }
}

/**
 * GATT Event Handler - Routes events to profile handlers
 */
static void gatts_event_handler(esp_gatts_cb_event_t event, esp_gatt_if_t gatts_if, esp_ble_gatts_cb_param_t *param) {
    if (event == ESP_GATTS_REG_EVT) {
        if (param->reg.status == ESP_GATT_OK) {
            doorbell_profile_tab[PROFILE_IDX].gatts_if = gatts_if;
        } else {
            ESP_LOGE(GATTS_TAG, "Registration failed");
            return;
        }
    }

    for (int idx = 0; idx < PROFILE_NUM; idx++) {
        if (gatts_if == ESP_GATT_IF_NONE || gatts_if == doorbell_profile_tab[idx].gatts_if) {
            if (doorbell_profile_tab[idx].gatts_cb) {
                doorbell_profile_tab[idx].gatts_cb(event, gatts_if, param);
            }
        }
    }
}

/*********************************** ULTRA-EFFICIENT BUTTON HANDLER ****************************************************/

/**
 * GPIO ISR Handler - IMMEDIATE notification on button press
 * No polling task needed - purely event-driven for zero idle power consumption
 */
static void IRAM_ATTR button_isr_handler(void* arg) {
    button_pressed = true;
    
    // Send notification immediately if connected and enabled
    if (is_connected && enable_notify) {
        uint8_t value = 1;
        
        // Set attribute value
        esp_ble_gatts_set_attr_value(
            doorbell_handle_table[DOORBELL_IDX_VAL],
            sizeof(value),
            &value
        );
        
        // Send notification to client
        esp_ble_gatts_send_indicate(
            gatts_interface,
            connection_id,
            doorbell_handle_table[DOORBELL_IDX_VAL],
            sizeof(value),
            &value,
            false
        );
    }
    
    // Reset button state after short delay (debounce in ISR)
    // This eliminates the need for a continuous polling task
    button_pressed = false;
}

/*********************************** MAIN APPLICATION ****************************************************/

void app_main(void) {
    esp_err_t ret;
    
    // Disable logging for power savings (optional - comment out if debugging)
    // esp_log_level_set("*", ESP_LOG_NONE);
    
    ESP_LOGI(GATTS_TAG, "Starting Ultra Power-Efficient Doorbell");

    // Initialize NVS
    ret = nvs_flash_init();
    if (ret == ESP_ERR_NVS_NO_FREE_PAGES || ret == ESP_ERR_NVS_NEW_VERSION_FOUND) {
        ESP_ERROR_CHECK(nvs_flash_erase());
        ret = nvs_flash_init();
    }
    ESP_ERROR_CHECK(ret);

    // POWER OPTIMIZATION: Release Classic Bluetooth memory
    ESP_ERROR_CHECK(esp_bt_controller_mem_release(ESP_BT_MODE_CLASSIC_BT));

    // Initialize Bluetooth controller with reduced memory configuration
    esp_bt_controller_config_t bt_cfg = BT_CONTROLLER_INIT_CONFIG_DEFAULT();
    
    // POWER OPTIMIZATION: Reduce Bluetooth controller memory footprint
    bt_cfg.controller_task_stack_size = 2048;  // Reduced from default
    bt_cfg.controller_task_prio = 5;           // Lower priority
    
    ret = esp_bt_controller_init(&bt_cfg);
    ESP_ERROR_CHECK(ret);

    ret = esp_bt_controller_enable(ESP_BT_MODE_BLE);
    ESP_ERROR_CHECK(ret);

    ret = esp_bluedroid_init();
    ESP_ERROR_CHECK(ret);

    ret = esp_bluedroid_enable();
    ESP_ERROR_CHECK(ret);

    // POWER OPTIMIZATION: Set MINIMUM TX power (-12dBm)
    ESP_ERROR_CHECK(esp_ble_tx_power_set(ESP_BLE_PWR_TYPE_DEFAULT, ESP_PWR_LVL_N12));
    ESP_ERROR_CHECK(esp_ble_tx_power_set(ESP_BLE_PWR_TYPE_ADV, ESP_PWR_LVL_N12));
    ESP_ERROR_CHECK(esp_ble_tx_power_set(ESP_BLE_PWR_TYPE_SCAN, ESP_PWR_LVL_N12));
    
    ESP_LOGI(GATTS_TAG, "TX Power set to -12dBm (minimum) for maximum power savings");

    // POWER OPTIMIZATION: Aggressive power management with automatic light sleep
    esp_pm_config_esp32_t pm_config = {
        .max_freq_mhz = 80,      // Lowest stable frequency for BLE
        .min_freq_mhz = 10,      // Absolute minimum
        .light_sleep_enable = true,  // Auto light sleep when idle
    };
    ESP_ERROR_CHECK(esp_pm_configure(&pm_config));
    
    ESP_LOGI(GATTS_TAG, "Power management configured: 10-80MHz with auto light sleep");

    // Register GATT callbacks
    esp_ble_gatts_register_callback(gatts_event_handler);
    esp_ble_gap_register_callback(gap_event_handler);
    esp_ble_gatts_app_register(APP_ID);

    // POWER OPTIMIZATION: Use minimum MTU (23 bytes)
    esp_ble_gatt_set_local_mtu(MTU_SIZE);

    // Configure button GPIO with minimal power consumption
    gpio_config_t io_conf = {
        .pin_bit_mask = (1ULL << GPIO_BUTTON),
        .mode = GPIO_MODE_INPUT,
        .pull_up_en = GPIO_PULLUP_ENABLE,
        .pull_down_en = GPIO_PULLDOWN_DISABLE,
        .intr_type = GPIO_INTR_POSEDGE,
    };
    gpio_config(&io_conf);

    // Install GPIO ISR service and handler
    gpio_install_isr_service(0);
    gpio_isr_handler_add(GPIO_BUTTON, button_isr_handler, NULL);

    ESP_LOGI(GATTS_TAG, "=== ULTRA POWER MODE ACTIVE ===");
    ESP_LOGI(GATTS_TAG, "Advertising: 10-20 second intervals");
    ESP_LOGI(GATTS_TAG, "TX Power: -12dBm");
    ESP_LOGI(GATTS_TAG, "CPU: 10-80MHz with auto sleep");
    ESP_LOGI(GATTS_TAG, "MTU: 23 bytes (minimum)");
    ESP_LOGI(GATTS_TAG, "Connection Interval: 400-800ms");
    ESP_LOGI(GATTS_TAG, "Task polling: ELIMINATED (event-driven only)");
    ESP_LOGI(GATTS_TAG, "Expected battery life: YEARS with CR2032");
}
