#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "freertos/event_groups.h"
#include "esp_system.h"
#include "esp_mac.h"
#include "ESP_LOG.h"
#include "nvs_flash.h"
#include "esp_bt.h"
#include "driver/uart.h"
#include "driver/gpio.h"
#include "string.h"

#include "esp_spp_api.h"
#include "esp_gap_ble_api.h"
#include "esp_gatts_api.h"
#include "esp_bt_defs.h"
#include "esp_bt_main.h"
#include "esp_bt_device.h"
#include "esp_gatt_common_api.h"
#include "esp_timer.h"
#include "esp_pm.h"

/************************************************************************ Bluetooth ***************************************************************************/

enum{
    DOORBELL_SVC,
    DOORBELL_IDX_CHAR,
    DOORBELL_IDX_VAL,
    DOORBELL_IDX_CFG,
    DOORBELL_IDX_NB,
};

/******************************** PROFILE DESCRIPTION *************************************/
#define GATTS_TAG           "Doorbell"  //Tag for ESP_LOGI/ESP_LOGE logging messages
#define PROFILE_NUM         1           //Number of GATT profiles to register
#define PROFILE_IDX         0           //Index of the profile to be used: 0 since there is no other profiles
#define APP_ID              0x56        //Application ID for GATT server registration
#define DEVICE_NAME         "Doorbell"    //BLE device name displayed during advertising
#define SERVICE_INST_ID	    0           //Service instance identifier for the doorbell service

/*********************** HANDLE TABLE ********************************************/
static uint16_t doorbell_handle_table[DOORBELL_IDX_NB]; //Attribute handles for the doorbell GATT service

/*********************************** ADVERTISING DATA ****************************************************/
static const uint8_t advertise_data[17] = {
    // Length: 0x02 - 2 bytes, Type: 0x01 - Flags, Value: 0x06 - LE General Discoverable Mode, BR/EDR Not Supported
    0x02,0x01,0x06,
    // Length: 0x03 - 3 bytes, Type: 0x03 - Complete List of 16-bit Service Class UUIDs, Value: 0xF0,0xAB - SPP Service UUID
    0x03,0x03,0xF0,0xAB,
    // Length: 0x09 - 9 bytes, Type: 0x09 - Complete Local Name, Value: 'D', 'O', 'O', 'R', 'B', 'E', 'L', 'L'
    0x09,0x09, 'D', 'O', 'O', 'R', 'B', 'E', 'L', 'L'
};

/******************************* ADVERTISING PARAMATERS ****************************************/
static esp_ble_adv_params_t advertising_params = {
    //Advertising interval in units of 0.625ms
    //Increased to 2000-4000ms to significantly reduce power consumption when not connected
    .adv_int_min        = 0xC80, //0xC80 * 0.625ms = 2000ms (2 seconds)
    .adv_int_max        = 0x1900, //0x1900 * 0.625ms = 4000ms (4 seconds)
    .adv_type           = ADV_TYPE_IND, //Connectable and scannable advertising
    .own_addr_type      = BLE_ADDR_TYPE_PUBLIC, //Use public device address
    .channel_map        = ADV_CHNL_ALL, //Use all three BLE advertising channels (37, 38, 39)
    .adv_filter_policy  = ADV_FILTER_ALLOW_SCAN_ANY_CON_ANY, //Accept scan and connection requests from any device
};

/********************************************* Doorbell GATT Service *******************************************************/
static const uint16_t doorbell_uuid = 0xABF0; //UUID for the doorbell GATT service

/**************************************** Notify characteristic ******************************************/
#define NOTIFY_UUID       0xABF2 //UUID for the notify characteristic


/**************************************** Packet limitations *******************************************/
#define MTU_SIZE          (512) //Maximum Transmission Unit size: 512 bytes
#define SPP_DATA_MAX_LEN  (512) //Maximum data length for characteristic value 

static uint16_t connection_id = 0xffff;
static esp_gatt_if_t gatts_interface = 0xff; //GATT server interface ID

/***************************** CLIENT CONFIGURATION *******************************/
static bool enable_notify = false; //Flag indicating if client has enabled notifications
static bool is_connected = false; //Flag indicating if a client is currently connected
static esp_bd_addr_t spp_remote_bda = {0x0,}; //Bluetooth device address of the connected client

/**
 * Structure containing GATT server profile information and configuration
 */
struct gatts_profile_inst {
    esp_gatts_cb_t gatts_cb; //Callback function for GATT server events
    uint16_t gatts_if; //GATT interface ID assigned to this profile
    uint16_t app_id; //Application ID used to register this profile
    uint16_t conn_id; //Connection ID for the active client connection
    uint16_t service_handle; //Service handle assigned by GATT server
    esp_gatt_srvc_id_t service_id; //Service ID structure (UUID and instance)
    uint16_t char_handle; //Characteristic handle assigned by GATT server
    esp_bt_uuid_t char_uuid; //Characteristic UUID
    esp_gatt_perm_t perm; //Permission bits for the characteristic
    esp_gatt_char_prop_t property; //Property bits for the characteristic
    uint16_t descr_handle; //Descriptor handle assigned by GATT server
    esp_bt_uuid_t descr_uuid; //Descriptor UUID
};

//GATT server event handler function for processing all GATT events
static void gatts_profile_event_handler(esp_gatts_cb_event_t event, esp_gatt_if_t gatts_if, esp_ble_gatts_cb_param_t *param);

/******************************* GATTS PROFILE INITIALIZATION *****************************************/
/* GATT profile table - one profile per application ID, initialized with ESP_GATT_IF_NONE until registration */
static struct gatts_profile_inst doorbell_profile_tab[PROFILE_NUM] = {
    [PROFILE_IDX] = {
        .gatts_cb = gatts_profile_event_handler,
        .gatts_if = ESP_GATT_IF_NONE,       /* Set to ESP_GATT_IF_NONE until assigned during registration */
        .app_id = APP_ID,
        .conn_id = 0xffff,
        .service_handle = 0,
        .char_handle = 0,
    },
};

/*
 ****************************************************************************************
 *  SPP PROFILE ATTRIBUTES
 ****************************************************************************************
 */

#define CHAR_DECLARATION_SIZE   (sizeof(uint8_t)) //Size of characteristic declaration attribute (1 byte)
static const uint16_t primary_doorbell_uuid = ESP_GATT_UUID_PRI_SERVICE; //Standard UUID for primary service declaration (0x2800)
static const uint16_t character_declaration_uuid = ESP_GATT_UUID_CHAR_DECLARE; //Standard UUID for characteristic declaration (0x2803)
static const uint16_t character_client_config_uuid = ESP_GATT_UUID_CHAR_CLIENT_CONFIG; //Standard UUID for CCCD (0x2902)

static const uint8_t char_prop_read_notify = ESP_GATT_CHAR_PROP_BIT_READ|ESP_GATT_CHAR_PROP_BIT_NOTIFY; //Property bits: readable and notifiable

///Doorbell Service - data notify characteristic, supports notify and read operations
static const uint16_t spp_data_notify_uuid = NOTIFY_UUID; //UUID for the notify characteristic (0xABF2)
static uint8_t  spp_data_notify_val[1] = {0x00}; //Initial value for notify characteristic
static uint8_t  spp_data_notify_ccc[2] = {0x00, 0x00}; //CCCD value (notifications disabled by default)

///Doorbell GATT Attribute Database - defines all attributes in the service
static const esp_gatts_attr_db_t doorbell_db[DOORBELL_IDX_NB] =
{
    //Doorbell Service Declaration
    [DOORBELL_SVC] =
        {{ESP_GATT_AUTO_RSP}, {ESP_UUID_LEN_16, (uint8_t *)&primary_doorbell_uuid, ESP_GATT_PERM_READ,
        sizeof(doorbell_uuid), sizeof(doorbell_uuid), (uint8_t *)&doorbell_uuid}},

    //Doorbell -  data notify characteristic Declaration
    [DOORBELL_IDX_CHAR] =
        {{ESP_GATT_AUTO_RSP}, {ESP_UUID_LEN_16, (uint8_t *)&character_declaration_uuid, ESP_GATT_PERM_READ,
        CHAR_DECLARATION_SIZE, CHAR_DECLARATION_SIZE, (uint8_t *)&char_prop_read_notify}},

    //Doorbell -  data notify characteristic Value
    [DOORBELL_IDX_VAL] =
        {{ESP_GATT_AUTO_RSP}, {ESP_UUID_LEN_16, (uint8_t *)&spp_data_notify_uuid, ESP_GATT_PERM_READ,
        SPP_DATA_MAX_LEN, sizeof(spp_data_notify_val), (uint8_t *)spp_data_notify_val}},

    //Doorbell -  data notify characteristic - Client Characteristic Configuration Descriptor
    [DOORBELL_IDX_CFG] =
        {{ESP_GATT_AUTO_RSP}, {ESP_UUID_LEN_16, (uint8_t *)&character_client_config_uuid, ESP_GATT_PERM_READ|ESP_GATT_PERM_WRITE,
        sizeof(uint16_t), sizeof(spp_data_notify_ccc), (uint8_t *)spp_data_notify_ccc}},
};

static void gap_event_handler(esp_gap_ble_cb_event_t event, esp_ble_gap_cb_param_t *param)
{
    switch (event) {
    case ESP_GAP_BLE_ADV_DATA_RAW_SET_COMPLETE_EVT:
        esp_ble_gap_start_advertising(&advertising_params);
        break;
    case ESP_GAP_BLE_ADV_START_COMPLETE_EVT:
        //Verify advertising started successfully
        if(param->adv_start_cmpl.status != ESP_BT_STATUS_SUCCESS) {
            //ESP_LOGE(GATTS_TAG, "Advertising start failed, status %d", param->adv_start_cmpl.status);
            break;
        }
        //ESP_LOGI(GATTS_TAG, "Advertising started successfully");
        break;
    case ESP_GAP_BLE_ADV_STOP_COMPLETE_EVT:
        //Verify advertising stopped successfully
        if(param->adv_stop_cmpl.status != ESP_BT_STATUS_SUCCESS) {
            //ESP_LOGE(GATTS_TAG, "Advertising stop failed, status %d", param->adv_stop_cmpl.status);
            break;
        }
        //ESP_LOGI(GATTS_TAG, "Advertising stopped successfully");
        break;
    case ESP_GAP_BLE_UPDATE_CONN_PARAMS_EVT:
         //ESP_LOGI(GATTS_TAG, "Connection params update, status %d, conn_int %d, latency %d, timeout %d",
                //    param->update_conn_params.status,
                //    param->update_conn_params.conn_int,
                //    param->update_conn_params.latency,
                //    param->update_conn_params.timeout);
        break;
    default:
        break;
    }
}

static void gatts_profile_event_handler(esp_gatts_cb_event_t event, esp_gatt_if_t gatts_if, esp_ble_gatts_cb_param_t *param)
{
    esp_ble_gatts_cb_param_t *p_data = (esp_ble_gatts_cb_param_t *) param;
    //uint8_t res = 0xff;

    switch (event) {
    	case ESP_GATTS_REG_EVT:
    	    //ESP_LOGI(GATTS_TAG, "GATT server regiser, status %d, app_id %d, gatts_if %d", param->reg.status, param->reg.app_id, gatts_if);
        	esp_ble_gap_set_device_name(DEVICE_NAME);
        	esp_ble_gatts_create_attr_tab(doorbell_db, gatts_if, DOORBELL_IDX_NB, SERVICE_INST_ID);
             
        	//esp_ble_gap_config_adv_data_raw((uint8_t *)advertise_data, sizeof(advertise_data));
       	break;
        case ESP_GATTS_CONNECT_EVT:
            //ESP_LOGI(GATTS_TAG, "Connected, conn_id %u, remote "ESP_BD_ADDR_STR"",
                 //param->connect.conn_id, ESP_BD_ADDR_HEX(param->connect.remote_bda));
    	    connection_id = p_data->connect.conn_id;
    	    gatts_interface = gatts_if;
    	    is_connected = true;

    	    memcpy(&spp_remote_bda,&p_data->connect.remote_bda,sizeof(esp_bd_addr_t));
            
            // Stop advertising to save power while connected
            esp_ble_gap_stop_advertising();
            
            // Update connection parameters for power efficiency
            esp_ble_conn_update_params_t conn_params = {0};
            memcpy(conn_params.bda, p_data->connect.remote_bda, sizeof(esp_bd_addr_t));
            conn_params.min_int = 0x10; // 20ms (16 * 1.25ms)
            conn_params.max_int = 0x20; // 40ms (32 * 1.25ms)
            conn_params.latency = 50;   // Allow 50 connection events to be skipped
            conn_params.timeout = 400;  // 4000ms timeout (400 * 10ms)
            esp_ble_gap_update_conn_params(&conn_params);
    	    break;
    	case ESP_GATTS_DISCONNECT_EVT:
            //ESP_LOGI(GATTS_TAG, "Disconnected, remote "ESP_BD_ADDR_STR", reason 0x%02x",
                // ESP_BD_ADDR_HEX(param->disconnect.remote_bda), param->disconnect.reason);
    	    is_connected = false;
    	    enable_notify = false;
            connection_id = 0xFFFF;
            
    	    esp_ble_gap_start_advertising(&advertising_params);
    	    break;
    	case ESP_GATTS_CREAT_ATTR_TAB_EVT:{
    	    ////ESP_LOGI(GATTS_TAG, "The number handle %x",param->add_attr_tab.num_handle);
    	    if (param->add_attr_tab.status != ESP_GATT_OK) {
    	        //////ESP_LOGE(GATTS_TAG, "Create attribute table failed, error code 0x%x", param->add_attr_tab.status);
    	    }
    	    else if (param->add_attr_tab.num_handle != DOORBELL_IDX_NB) {
    	        //////ESP_LOGE(GATTS_TAG, "Create attribute table abnormally, num_handle (%d) doesn't equal to HRS_IDX_NB(%d)", param->add_attr_tab.num_handle, DOORBELL_IDX_NB);
    	    }
    	    else {
    	        memcpy(doorbell_handle_table, param->add_attr_tab.handles, sizeof(doorbell_handle_table));
                esp_err_t sret = esp_ble_gatts_start_service(doorbell_handle_table[DOORBELL_SVC]);
                if (sret != ESP_OK) {
                    //ESP_LOGE(GATTS_TAG, "start_service failed: %d", sret);
                } else {
                    vTaskDelay(150 / portTICK_PERIOD_MS);

                    // Configure and start advertising AFTER service started
                    esp_ble_gap_config_adv_data_raw((uint8_t *)advertise_data, sizeof(advertise_data));
                    // Note: gap_event_handler will start advertising on ADV_DATA_RAW_SET_COMPLETE_EVT
                }
    	    }
    	    break;
    	}
        case ESP_GATTS_WRITE_EVT: {
            if (param->write.handle == doorbell_handle_table[DOORBELL_IDX_CFG]) {
                if (param->write.len == 2) {
                    uint16_t descr_value = param->write.value[1] << 8 | param->write.value[0];
                    if (descr_value == 0x0001) {
                        enable_notify = true;
                        //ESP_LOGI(GATTS_TAG, "Notifications ENABLED");
                    } else if (descr_value == 0x0000) {
                        enable_notify = false;
                        //ESP_LOGI(GATTS_TAG, "Notifications DISABLED");
                    }
                }
            }
            break;
        }
    	default:
    	    break;
    }
}

static void gatts_event_handler(esp_gatts_cb_event_t event, esp_gatt_if_t gatts_if, esp_ble_gatts_cb_param_t *param)
{
    /* If event is register event, store the gatts_if for each profile */
    if (event == ESP_GATTS_REG_EVT) {
        if (param->reg.status == ESP_GATT_OK) {
            doorbell_profile_tab[PROFILE_IDX].gatts_if = gatts_if;
        } else {
            //ESP_LOGI(GATTS_TAG, "Reg app failed, app_id %04x, status %d",param->reg.app_id, param->reg.status);
            return;
        }
    }

    do {
        int idx;
        for (idx = 0; idx < PROFILE_NUM; idx++) {
            if (gatts_if == ESP_GATT_IF_NONE || /* ESP_GATT_IF_NONE, not specify a certain gatt_if, need to call every profile cb function */
                    gatts_if == doorbell_profile_tab[idx].gatts_if) {
                if (doorbell_profile_tab[idx].gatts_cb) {
                    doorbell_profile_tab[idx].gatts_cb(event, gatts_if, param);
                }
            }
        }
    } while (0);
}


/************************************************************** Doorbell **************************************************************************/
// GPIO pin assignments
#define GPIO_BUTTON GPIO_NUM_16 //Doorbell button input pin
#define GPIO_LED    GPIO_NUM_17 //LED output pin (currently unused)

TaskHandle_t Click_handler = NULL; //FreeRTOS task handle for button click processing
QueueHandle_t myQueue = NULL; //Queue for passing button state from ISR to task

uint8_t curr_state = 0; //Current button state (1 = pressed, 0 = not pressed)

/**
 * Button click handler task - processes button presses and sends notifications to connected clients
 */
void CLICK_Task() {
    while(1) {
        //Wait indefinitely for button state from ISR queue
        if(xQueueReceive(myQueue, &curr_state, portMAX_DELAY)) {
            //If button was pressed, update characteristic value and send notification
            if (curr_state == 1) {
                //Set the characteristic value to the button state
                esp_ble_gatts_set_attr_value(
                    doorbell_handle_table[DOORBELL_IDX_VAL],
                    sizeof(curr_state),
                    &curr_state
                    );
                    
                //Send indication to connected client
                esp_ble_gatts_send_indicate(
                    gatts_interface,
                    connection_id,
                    doorbell_handle_table[DOORBELL_IDX_VAL],
                    sizeof(curr_state),
                    &curr_state,
                    false
                    );
            }
            //Reset button state to 0
            // (Commented code below was for sending a second notification with value 0)
            // temp = 0;
            // esp_ble_gatts_set_attr_value(
            //     doorbell_handle_table[DOORBELL_IDX_VAL],
            //     sizeof(temp),
            //     &temp
            //     );
                
            // esp_ble_gatts_send_indicate(
            //     gatts_interface,
            //     connection_id,
            //     doorbell_handle_table[DOORBELL_IDX_VAL],
            //     sizeof(temp),
            //     &temp,
            //     false
            // );
        }
        //Reset button state after processing
        curr_state = 0;
        //Delay for 2 seconds for power efficiency - reduces CPU wake-ups significantly
        vTaskDelay(2000 / portTICK_PERIOD_MS);

        //gpio_set_level(GPIO_LED, led_state); //LED control (currently unused)
    }
}

/**
 * GPIO interrupt service routine - triggered on button press (rising edge)
 * Sends button state to CLICK_Task via queue
 */
static void IRAM_ATTR button_isr_handler(void* arg) {
    //Set button state to pressed
    curr_state = 1;
    //Send state to processing task via queue
    xQueueSendFromISR(myQueue, &curr_state, NULL);
}

/**
 * Main application entry point - initializes Bluetooth, GPIO, and starts tasks
 */
void app_main(void)
{
    esp_err_t ret;
    esp_bt_controller_config_t bt_cfg = BT_CONTROLLER_INIT_CONFIG_DEFAULT();

    //Initialize Non-Volatile Storage (required for Bluetooth stack)
    ret = nvs_flash_init();
    //Check if NVS partition was truncated or has incompatible version
    if (ret == ESP_ERR_NVS_NO_FREE_PAGES || ret == ESP_ERR_NVS_NEW_VERSION_FOUND) { 
        ESP_ERROR_CHECK(nvs_flash_erase()); //Erase NVS partition (will crash if erase fails)
        ret = nvs_flash_init(); //Reinitialize NVS after erase
    }
    ESP_ERROR_CHECK( ret ); //Crash if NVS initialization failed

    //Release memory allocated for Classic Bluetooth (not needed for BLE-only operation)
    ESP_ERROR_CHECK(esp_bt_controller_mem_release(ESP_BT_MODE_CLASSIC_BT));

    //Initialize Bluetooth controller with default configuration
    ret = esp_bt_controller_init(&bt_cfg);
    if (ret) {
        //ESP_LOGE(GATTS_TAG, "%s init controller failed: %s", __func__, esp_err_to_name(ret));
        return;
    }

    //Enable Bluetooth controller in BLE-only mode
    ret = esp_bt_controller_enable(ESP_BT_MODE_BLE);
    if (ret) {
        //ESP_LOGE(GATTS_TAG, "%s enable controller failed: %s", __func__, esp_err_to_name(ret));
        return;
    }

    //ESP_LOGI(GATTS_TAG, "%s init bluetooth", __func__);

    //Initialize Bluedroid Bluetooth stack
    ret = esp_bluedroid_init();
    if (ret) {
        //ESP_LOGE(GATTS_TAG, "%s init bluetooth failed: %s", __func__, esp_err_to_name(ret));
        return;
    }
    //Enable Bluedroid Bluetooth stack
    ret = esp_bluedroid_enable();
    if (ret) {
        //ESP_LOGE(GATTS_TAG, "%s enable bluetooth failed: %s", __func__, esp_err_to_name(ret));
        return;
    }

    //Set BLE transmit power to -12dBm for maximum power savings
    //Using ESP_PWR_LVL_N12 provides excellent power efficiency for short-range applications
    //Reduced from default to achieve 10-20x power savings during transmission
    esp_err_t power_ret = esp_ble_tx_power_set(ESP_BLE_PWR_TYPE_DEFAULT, ESP_PWR_LVL_N12);
    if (power_ret != ESP_OK) {
        //Log error if TX power setting failed
        ESP_LOGE(GATTS_TAG, "Failed to set default TX power, error %d", ret);
        ESP_LOGE(GATTS_TAG, "Error string: %s", esp_err_to_name(ret));
    }
    
    //Set advertising-specific TX power to -12dBm for power efficiency
    esp_ble_tx_power_set(ESP_BLE_PWR_TYPE_ADV, ESP_PWR_LVL_N12);
    power_ret = esp_ble_tx_power_set(ESP_BLE_PWR_TYPE_ADV, ESP_PWR_LVL_N12);
    if (power_ret != ESP_OK) {
        //Log error if advertising TX power setting failed
        ESP_LOGE(GATTS_TAG, "Failed to set advertising TX power, error %d", ret);
        ESP_LOGE(GATTS_TAG, "Error string: %s", esp_err_to_name(ret));
    }

    //Configure automatic power management for maximum power efficiency
    //Enables dynamic frequency scaling and light sleep mode
    esp_pm_config_esp32_t pm_config = {
        .max_freq_mhz = 160,    //Max CPU frequency: 160MHz (reduced from 240MHz for power savings)
        .min_freq_mhz = 40,     //Min CPU frequency: 40MHz (reduced from 80MHz for deeper power savings)
        .light_sleep_enable = true,  //Enable automatic light sleep when idle
    };
    esp_pm_configure(&pm_config);

    //Register GATT server event callback
    esp_ble_gatts_register_callback(gatts_event_handler);
    //Register GAP event callback
    esp_ble_gap_register_callback(gap_event_handler);
    //Register GATT application
    esp_ble_gatts_app_register(APP_ID);

    //Set local MTU size
    esp_err_t local_mtu_ret = esp_ble_gatt_set_local_mtu(MTU_SIZE);
        if (local_mtu_ret){
        //Log error if MTU setting failed
        //////ESP_LOGE(GATTS_TAG, "set local  MTU failed, error code = %x", local_mtu_ret);
    }

    //Configure button GPIO pin
    esp_rom_gpio_pad_select_gpio(GPIO_BUTTON);
    gpio_set_direction(GPIO_BUTTON, GPIO_MODE_INPUT);

    // LED GPIO configuration (currently commented out - unused)
    // esp_rom_gpio_pad_select_gpio(GPIO_LED);
    // gpio_set_direction(GPIO_LED, GPIO_MODE_OUTPUT);

    //Enable internal pull-up resistor on button pin
    gpio_pullup_en(GPIO_BUTTON);
    gpio_pulldown_dis(GPIO_BUTTON);

    //Configure interrupt on rising edge (button press)
    gpio_set_intr_type(GPIO_BUTTON, GPIO_INTR_POSEDGE);

    //Install GPIO ISR service
    gpio_install_isr_service(0);
    //Add button ISR handler
    gpio_isr_handler_add(GPIO_BUTTON, button_isr_handler, NULL);
    //Enable button interrupt
    gpio_intr_enable(GPIO_BUTTON);
    
    //Create queue for button state messages (capacity: 3 messages, size: 1 byte each)
    myQueue = xQueueCreate(3, sizeof(char));
    
    //Create button processing task pinned to core 1
    xTaskCreatePinnedToCore(CLICK_Task, "CLICK", 4096, NULL, 10, &Click_handler, 1);
}
