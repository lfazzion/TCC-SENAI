/*
 * Jiga de Teste de Relés - Versão Final
 * Combina hardware real do miliohmimetrov2.ino com comunicação BLE do
 * espsolo.ino
 *
 * MELHORIAS DE PERFORMANCE DE MEMÓRIA IMPLEMENTADAS:
 * - Substituição de objetos String por char arrays para reduzir uso de heap
 * - Uso de buffers estáticos com tamanhos padronizados e seguros
 * - Função auxiliar para conversão padronizada de resistência para string
 * - Validação de tamanho de strings com terminação nula garantida
 * - Uso de strncpy() e snprintf() para operações seguras de string
 * - Redução significativa da fragmentação de memória heap
 *
 * MELHORIAS DE PRECISÃO NAS MEDIÇÕES:
 * - Implementação de Média Aparada Rápida (6 amostras, descarta 15% dos
 * extremos)
 * - Eliminação automática de valores extremos (ruído) das medições
 * - Melhor precisão e confiabilidade nas medições de resistência
 * - Consistência entre calibração e teste usando mesmo método estatístico
 *
 * MÉDIA APARADA (TRIMMED MEAN):
 * - Ordena as amostras em ordem crescente
 * - Descarta percentual configurado dos valores extremos (mais altos e baixos)
 * - Calcula média com os valores centrais restantes
 * - Reduz significativamente a influência de picos de ruído
 *
 * Referências:
 * - Documentação da biblioteca ADS1X15: https://github.com/RobTillaart/ADS1X15
 * - Manipulação String -> Array:
 * https://arduino.stackexchange.com/questions/77125/convert-string-to-array
 */

// --- Bibliotecas ---
#include <ArduinoJson.h>
#include <BLE2902.h>
#include <BLEDevice.h>
#include <BLEServer.h>
#include <BLEUtils.h>
#include <Wire.h>
#include <math.h>

#include "ADS1X15.h"

// --- Definições de Hardware ---
#define LED_CONT 4
#define RGB_RED 14
#define RGB_GREEN 27
#define RGB_BLUE 26
#define RELAY_DC 2
#define RELAY_AC 12
#define BUTTON 15

// --- Constantes de Medição ---
#define MEAN 20
#define res_ref 99.781
#define LIMITE_RESISTENCIA_ABERTO 100.0  // Padronizado para 100 Ω

// --- Configuração de Medição ---
// Usa média aparada rápida com 6 amostras e descarte de 15% dos extremos
// Oferece boa precisão com velocidade adequada para testes em produção

// --- Constantes para Medição de Tempo de Acionamento ---
#define TIMEOUT_ACIONAMENTO 5000000    // 5 segundos máximo (em microssegundos)
#define THRESHOLD_MUDANCA_ESTADO 10.0  // Limiar em Ω para detectar mudança

// --- Configurações Otimizadas do ADC ---
#define ADC_TAXA_NORMAL 3  // 128 SPS para medições normais
#define ADC_TAXA_RAPIDA 7  // 860 SPS para medição de tempo (máxima velocidade)

// --- Critérios de Avaliação Melhorados ---
#define LIMITE_BAIXA_RESISTENCIA 15.0    // Aumentado de 10.0 para 15.0 Ω
#define LIMITE_RESISTENCIA_MINIMA 100.0  // Mínimo para considerar "aberto"
#define TOLERANCIA_NEGATIVA 20.0         // Tolerância para valores negativos

// --- Tamanhos de Buffers ---
#define BUFFER_SIZE_COMANDO 512
#define BUFFER_SIZE_MENSAGEM 128
#define BUFFER_SIZE_CONTATO 16
#define BUFFER_SIZE_RESISTENCIA 16
#define BUFFER_SIZE_DEBUG 64

// --- Controle de Debug ---
#define DEBUG_ENABLED 0  // 0 = Desabilitado, 1 = Habilitado

// Macro para debug condicional
#if DEBUG_ENABLED
#define DEBUG_PRINT(x) Serial.print(x)
#define DEBUG_PRINTLN(x) Serial.println(x)
#else
#define DEBUG_PRINT(x)
#define DEBUG_PRINTLN(x)
#endif

// --- UUIDs para o Serviço BLE ---
#define BLE_SERVICE_UUID "4fafc201-1fb5-459e-8fcc-c5c9c331914b"
#define BLE_RECEIVE_CHARACTERISTIC_UUID \
    "beb5483e-36e1-4688-b7f5-ea07361b26a8"  // WebApp -> ESP32
#define BLE_SEND_CHARACTERISTIC_UUID \
    "a4d23253-2778-436c-9c23-2c1b50d87635"  // ESP32 -> WebApp

// --- Objetos e Variáveis Globais ---
ADS1115 ADS(0x48);
BLECharacteristic* pSendCharacteristic;
BLEServer* pServer;
bool deviceConnected = false;
bool oldDeviceConnected = false;

// Variáveis para comunicação assíncrona e controle de fluxo
volatile bool g_comandoRecebidoFlag = false;
volatile bool g_aguardandoConfirmacao = false;
char g_comandoJson[BUFFER_SIZE_COMANDO];

// --- Funções Auxiliares para Estatística ---
/**
 * @brief Ordena um array de floats em ordem crescente (bubble sort
 * simplificado)
 * @param arr Array a ser ordenado
 * @param n Tamanho do array
 */
void ordenarArray(float arr[], int n) {
    for (int i = 0; i < n - 1; i++) {
        for (int j = 0; j < n - i - 1; j++) {
            if (arr[j] > arr[j + 1]) {
                float temp = arr[j];
                arr[j] = arr[j + 1];
                arr[j + 1] = temp;
            }
        }
    }
}

/**
 * @brief Calcula a média aparada (trimmed mean) de um array
 * @param valores Array de valores
 * @param n Número de valores
 * @param percentual_descarte Percentual de valores a descartar (ex: 0.1 para
 * 10%)
 * @return Média aparada
 */
float calcularMediaAparada(float valores[], int n, float percentual_descarte) {
    if (n < 3) {
        // Para arrays muito pequenos, usa média simples
        float soma = 0.0;
        for (int i = 0; i < n; i++) {
            soma += valores[i];
        }
        return soma / n;
    }

    // Cria uma cópia do array para não modificar o original
    // Usa buffer estático para evitar problemas com arrays de tamanho variável
    const int MAX_AMOSTRAS = 50;  // Limite máximo de amostras
    float valoresOrdenados[MAX_AMOSTRAS];

    // Limita o número de valores ao tamanho do buffer
    int valores_efetivos = (n > MAX_AMOSTRAS) ? MAX_AMOSTRAS : n;

    for (int i = 0; i < valores_efetivos; i++) {
        valoresOrdenados[i] = valores[i];
    }

    // Ordena os valores
    ordenarArray(valoresOrdenados, valores_efetivos);

    // Calcula quantos valores descartar de cada extremo
    int valores_descarte = (int)(valores_efetivos * percentual_descarte);
    if (valores_descarte < 1)
        valores_descarte = 1;

    // Garante que sobrem pelo menos 2 valores
    if (valores_descarte * 2 >= valores_efetivos) {
        valores_descarte = (valores_efetivos - 2) / 2;
    }

    // Calcula a média dos valores centrais
    float soma = 0.0;
    int inicio = valores_descarte;
    int fim = valores_efetivos - valores_descarte;
    int valores_usados = fim - inicio;

    for (int i = inicio; i < fim; i++) {
        soma += valoresOrdenados[i];
    }

    return soma / valores_usados;
}

/**
 * @brief Versão otimizada da função get_res() para calibração com máxima
 * precisão Usa taxa de amostragem mais baixa (16 SPS) para melhor rejeição de
 * ruído
 * @return Valor de resistência em ohms ou -1.0 em caso de erro
 */
float get_res_calibracao() {
    if (!ADS.isConnected()) {
        DEBUG_PRINTLN("get_res_calibracao: ADS1115 não conectado");
        return -1.0;
    }

    // Configuração para máxima precisão (16 SPS para melhor rejeição de ruído)
    ADS.setDataRate(0);  // 0 = 8 SPS, 1 = 16 SPS (mais precisão)
    ADS.setGain(1);      // Reconfirma o ganho

    // Aguarda estabilização após mudança de configuração
    delay(100);

    // Teste rápido para detecção de circuito aberto
    delay(50);  // Delay maior para estabilização
    int16_t test_val_01 = ADS.readADC_Differential_0_1();
    delay(50);  // Delay maior entre leituras
    int16_t test_val_13 = ADS.readADC_Differential_1_3();

    float test_volts_ref = ADS.toVoltage(test_val_01);
    float test_volts = ADS.toVoltage(test_val_13);

    // Detecção de circuito aberto
    if (abs(test_volts_ref) < 0.001 && abs(test_volts) < 0.001) {
        DEBUG_PRINTLN("get_res_calibracao: circuito aberto detectado");
        return 10000.0;
    }

    if (abs(test_volts_ref) < 0.0001 && abs(test_volts) > 0.01) {
        DEBUG_PRINTLN(
            "get_res_calibracao: volts_ref muito pequeno - circuito aberto");
        return 10000.0;
    }

    // Aumenta o número de leituras para calibração (mais precisão)
    const int NUM_LEITURAS = 10;
    float soma = 0.0;
    int leituras_validas = 0;

    for (int i = 0; i < NUM_LEITURAS; i++) {
        delay(100);  // Delay maior entre leituras para estabilização

        int16_t val_01 = ADS.readADC_Differential_0_1();
        delay(20);  // Delay entre canais
        int16_t val_13 = ADS.readADC_Differential_1_3();

        float volts_ref = ADS.toVoltage(val_01);
        float volts = ADS.toVoltage(val_13);

        // Validação rigorosa dos valores
        if (isnan(volts_ref) || isnan(volts) || isinf(volts_ref) ||
            isinf(volts)) {
            continue;
        }

        // Detecção de problemas de leitura
        if (abs(volts_ref) < 0.00001 || abs(volts) < 0.0001) {
            return 10000.0;
        }

        float resistencia = (res_ref * volts) / volts_ref;

        // Validação do resultado
        if (isnan(resistencia) || isinf(resistencia)) {
            continue;
        }

        if (resistencia > 50000.0 || resistencia < -1000.0) {
            continue;
        }

        soma += resistencia;
        leituras_validas++;
    }

    // Restaura configuração original do ADC
    ADS.setDataRate(ADC_TAXA_NORMAL);  // Volta para 128 SPS

    if (leituras_validas < NUM_LEITURAS / 2) {
        DEBUG_PRINT("get_res_calibracao: leituras insuficientes: ");
        DEBUG_PRINTLN(leituras_validas);
        return -1.0;
    }

    float media = soma / leituras_validas;

    return media;
}

// Variáveis para estabilidade da conexão
unsigned long lastHeartbeat = 0;
const unsigned long HEARTBEAT_INTERVAL =
    5000;  // 5 segundos - reduzido para manter conexão
unsigned long lastConnectionCheck = 0;
const unsigned long CONNECTION_CHECK_INTERVAL =
    1000;  // 1 segundo - mais frequente durante medições
bool connectionLost = false;

// Variáveis para monitoramento de performance
unsigned long totalReconnections = 0;
unsigned long lastSuccessfulOperation = 0;
unsigned long connectionStartTime = 0;

// Variáveis para otimização BLE
unsigned long lastDataSent = 0;
const unsigned long MIN_DATA_INTERVAL =
    20;  // Mínimo 20ms entre envios para melhor fluidez
uint8_t retryCount = 0;
const uint8_t MAX_RETRY_COUNT = 5;  // Mais tentativas

// === SISTEMA DE COMUNICAÇÃO MELHORADO ===

// Controle de fluxo adaptativo
unsigned long adaptiveInterval = 20;  // Intervalo adaptativo
uint8_t consecutiveFailures = 0;
const uint8_t MAX_CONSECUTIVE_FAILURES = 3;

// Sistema de Message ID e ACK
uint32_t messageIdCounter = 0;
char currentMessageId[32] = {0};
bool awaitingAck = false;
unsigned long ackTimeout = 0;

// Estados de comunicação
enum CommState {
    COMM_IDLE,
    COMM_SENDING,
    COMM_WAITING_ACK,
    COMM_PROCESSING,
    COMM_ERROR
};

CommState commState = COMM_IDLE;

// === CONTROLE DE ESTADO DO DISPOSITIVO ===
enum DeviceState {
    DEVICE_IDLE,
    DEVICE_CALIBRATING,
    DEVICE_TESTING,
    DEVICE_WAITING_BUTTON,
    DEVICE_ERROR
};

DeviceState currentDeviceState = DEVICE_IDLE;
char currentModule[64] = {0};
int currentTestStep = -1;
unsigned long lastClientPing = 0;
const unsigned long CLIENT_PING_TIMEOUT = 30000;  // 30 segundos

// Controle de heartbeat inteligente
bool heartbeatPaused = false;
unsigned long heartbeatPauseUntil = 0;
unsigned long heartbeatResumeTime = 0;
unsigned long currentHeartbeatInterval = 5000;  // 5 segundos padrão

// Buffer para reduzir fragmentação
char jsonBuffer[512];

// Variáveis de medição
float res[2][8] = {0.0};
float res_cal = 0.0;
int value = 0;
int num = 0;
bool relay_state = false;

// Variáveis para medição de tempo de acionamento
float ultimo_tempo_acionamento =
    0.0;  // Em milissegundos (convertido de microssegundos)
bool medicao_tempo_habilitada = false;

// Estrutura para armazenar a configuração do teste recebida da WebApp
struct TestConfig {
    char tipoAcionamento[16];  // "TIPO_DC" ou "TIPO_AC"
    int quantidadeContatos;    // Número total de contatos a testar (NF + NA)
    JsonArrayConst calibracao;
};

// Declarações forward das funções que usam TestConfig
void executarTesteEspecialUmContato(const TestConfig& config);
void executarTesteConfiguravel(const TestConfig& config);

// =================================================================
// FUNÇÕES AUXILIARES PARA CONVERSÃO DE DADOS
// =================================================================

/**
 * @brief Gera um ID único para mensagens
 */
void generateMessageId() {
    snprintf(currentMessageId, sizeof(currentMessageId), "esp_%lu_%lu",
             millis(), ++messageIdCounter);
}

/**
 * @brief Controla o heartbeat inteligente
 */
void pauseHeartbeat(unsigned long duration) {
    heartbeatPaused = true;
    heartbeatPauseUntil = millis() + duration;
    heartbeatResumeTime = millis() + duration;
    DEBUG_PRINTLN("Heartbeat pausado para operação crítica");
}

void resumeHeartbeat() {
    heartbeatPaused = false;
    heartbeatPauseUntil = 0;
    heartbeatResumeTime = 0;
    DEBUG_PRINTLN("Heartbeat reativado");
}

bool isHeartbeatPaused() {
    if (heartbeatPaused && millis() > heartbeatPauseUntil) {
        resumeHeartbeat();
    }
    return heartbeatPaused;
}

/**
 * @brief Controle de fluxo adaptativo
 */
void updateAdaptiveInterval(bool success) {
    if (success) {
        consecutiveFailures = 0;
        // Diminui intervalo em caso de sucesso
        if (adaptiveInterval > 15) {
            adaptiveInterval = max(15UL, adaptiveInterval - 2);
        }
    } else {
        consecutiveFailures++;
        // Aumenta intervalo em caso de falha
        if (consecutiveFailures > MAX_CONSECUTIVE_FAILURES) {
            adaptiveInterval = min(200UL, adaptiveInterval + 20);
        }
    }
}

bool canSendMessage() {
    unsigned long now = millis();
    return (now - lastDataSent) >= adaptiveInterval;
}

/**
 * @brief Envia ACK para uma mensagem recebida
 */
void sendAck(const char* messageId) {
    if (!messageId || strlen(messageId) == 0)
        return;

    StaticJsonDocument<200> ackDoc;
    ackDoc["status"] = "ack";
    ackDoc["messageId"] = messageId;
    ackDoc["timestamp"] = millis();

    sendJsonResponse(ackDoc);
}

/**
 * @brief Converte valor de resistência para string padronizada
 * @param resistencia Valor da resistência em ohms
 * @param buffer Buffer de destino para a string
 * @param bufferSize Tamanho do buffer
 */
void resistenciaParaString(float resistencia, char* buffer, size_t bufferSize) {
    if (resistencia == -1.0) {
        // Caso especial: erro na medição
        strncpy(buffer, "ERRO", bufferSize - 1);
        DEBUG_PRINTLN("ERRO");
    } else if (resistencia > LIMITE_RESISTENCIA_ABERTO) {
        // Resistência muito alta - circuito aberto
        strncpy(buffer, "ABERTO", bufferSize - 1);
        DEBUG_PRINTLN("ABERTO");
    } else if (resistencia < -TOLERANCIA_NEGATIVA) {
        // Resistência muito negativa - possível erro
        strncpy(buffer, "ERRO", bufferSize - 1);
        DEBUG_PRINTLN("ERRO (negativo)");
    } else {
        // Resistência válida (incluindo valores pequenos e negativos normais)
        snprintf(buffer, bufferSize, "%.3f", resistencia);
        DEBUG_PRINTLN(buffer);
    }
    buffer[bufferSize - 1] = '\0';  // Garante terminação nula
}

// =================================================================
// FUNÇÕES DE HARDWARE
// =================================================================

void reset_output() {
    digitalWrite(RGB_RED, 0);
    digitalWrite(RGB_GREEN, 0);
    digitalWrite(RGB_BLUE, 0);
    digitalWrite(RELAY_DC, 0);
    digitalWrite(RELAY_AC, 0);
}

void state_RGB(char state) {
    switch (state) {
        case 'O':  // Azul - Aguardando
            digitalWrite(RGB_RED, 0);
            digitalWrite(RGB_GREEN, 0);
            digitalWrite(RGB_BLUE, 1);
            break;
        case 'B':  // Verde - Pronto/Sucesso
            digitalWrite(RGB_RED, 0);
            digitalWrite(RGB_GREEN, 1);
            digitalWrite(RGB_BLUE, 0);
            break;
        case 'R':  // Vermelho - Erro/Falha
            digitalWrite(RGB_RED, 1);
            digitalWrite(RGB_GREEN, 0);
            digitalWrite(RGB_BLUE, 0);
            break;
        default:
            reset_output();
            break;
    }
}

float get_res() {
    if (!ADS.isConnected()) {
        DEBUG_PRINTLN("get_res: ADS1115 não conectado");
        return -1.0;
    }

    // Configuração otimizada para medições mais estáveis
    ADS.setDataRate(ADC_TAXA_NORMAL);  // 128 SPS - mais estável
    ADS.setGain(1);                    // Reconfirma o ganho

    // Teste rápido para detecção de circuito aberto
    delay(10);
    int16_t test_val_01 = ADS.readADC_Differential_0_1();
    delay(5);
    int16_t test_val_13 = ADS.readADC_Differential_1_3();

    float test_volts_ref = ADS.toVoltage(test_val_01);
    float test_volts = ADS.toVoltage(test_val_13);

    // Se ambos os valores são muito pequenos, provavelmente é circuito aberto
    if (abs(test_volts_ref) < 0.001 && abs(test_volts) < 0.001) {
        DEBUG_PRINTLN(
            "get_res: ambos os valores muito pequenos - circuito aberto");
        return 10000.0;
    }

    // Se volts_ref é muito pequeno comparado a volts, é circuito aberto
    if (abs(test_volts_ref) < 0.0001 && abs(test_volts) > 0.01) {
        DEBUG_PRINTLN("get_res: volts_ref muito pequeno - circuito aberto");
        return 10000.0;
    }

    // Aumenta o número de leituras para aplicar a média aparada
    const int NUM_LEITURAS = 6;
    float resistencias[NUM_LEITURAS];
    int leituras_validas = 0;

    for (int i = 0; i < NUM_LEITURAS; i++) {
        delay(5);  // Delay menor para velocidade

        int16_t val_01 = ADS.readADC_Differential_0_1();
        delay(2);
        int16_t val_13 = ADS.readADC_Differential_1_3();

        float volts_ref = ADS.toVoltage(val_01);
        float volts = ADS.toVoltage(val_13);

        // Validação simples dos valores lidos
        if (isnan(volts_ref) || isnan(volts) || isinf(volts_ref) ||
            isinf(volts)) {
            continue;  // Pula esta leitura
        }

        // Verifica se volts_ref é muito pequeno (possível problema)
        if (abs(volts_ref) < 0.00001) {
            DEBUG_PRINTLN(
                "get_res: volts_ref muito pequeno - possível circuito aberto");
            // Retorna um valor alto para indicar circuito aberto
            return 10000.0;  // 10k ohms - bem acima do limite de 100 ohms
        }

        // Para circuitos abertos, volts pode ser muito pequeno
        // Neste caso, a resistência calculada será muito baixa (incorreta)
        // Vamos detectar esta situação
        if (abs(volts) < 0.0001) {
            DEBUG_PRINTLN(
                "get_res: volts muito pequeno - possível circuito aberto");
            // Retorna um valor alto para indicar circuito aberto
            return 10000.0;  // 10k ohms - bem acima do limite de 100 ohms
        }

        float resistencia = (res_ref * volts) / volts_ref;

        // Validação simples do resultado
        if (isnan(resistencia) || isinf(resistencia)) {
            DEBUG_PRINTLN(
                "get_res: resultado NaN ou infinito - possível circuito "
                "aberto");
            return 10000.0;  // Retorna valor alto indicando circuito aberto
        }

        // Se a resistência calculada é muito alta, pode ser circuito aberto
        if (resistencia > 50000.0) {
            DEBUG_PRINTLN(
                "get_res: resistência muito alta - circuito aberto detectado");
            return 10000.0;  // Retorna valor alto mas finito
        }

        // Se a resistência calculada é negativa e muito baixa, pode ser
        // problema de leitura
        if (resistencia < -1000.0) {
            DEBUG_PRINTLN(
                "get_res: resistência muito negativa - possível problema de "
                "leitura");
            return 10000.0;  // Trata como circuito aberto
        }

        resistencias[leituras_validas] = resistencia;
        leituras_validas++;
    }

    if (leituras_validas <
        4) {  // Precisa de pelo menos 4 leituras válidas para média aparada
        return 10000.0;  // Assume circuito aberto
    }

    // Aplica média aparada com 15% de descarte (adaptado para 6 amostras)
    float media_aparada =
        calcularMediaAparada(resistencias, leituras_validas, 0.15);
    return media_aparada;
}

/**
 * @brief Mede o tempo de acionamento do relé em teste
 * Monitora a mudança de resistência para detectar quando o relé efetivamente
 * comuta
 * @return Tempo de acionamento em milissegundos ou -1.0 em caso de erro/timeout
 */
float medirTempoAcionamento() {
    if (!ADS.isConnected()) {
        DEBUG_PRINTLN("ERRO: ADS não conectado durante medição de tempo");
        return -1.0;
    }

    // Configuração para máxima velocidade
    ADS.setDataRate(ADC_TAXA_RAPIDA);  // 860 SPS para máxima resolução temporal
    ADS.setGain(1);                    // Reconfirma o ganho

    // Aguarda estabilização mínima
    delayMicroseconds(500);

    // Lê o estado inicial
    float resistencia_inicial = -1.0;
    int tentativas_inicial = 0;
    const int MAX_TENTATIVAS_INICIAL = 2;  // Reduzido para otimizar velocidade

    while (resistencia_inicial < 0 &&
           tentativas_inicial < MAX_TENTATIVAS_INICIAL) {
        int16_t val_01 = ADS.readADC_Differential_0_1();
        int16_t val_13 = ADS.readADC_Differential_1_3();

        float volts_ref = ADS.toVoltage(val_01);
        float volts = ADS.toVoltage(val_13);

        // Verifica se as leituras são válidas
        if (abs(volts_ref) > 0.0001) {
            resistencia_inicial = (volts / volts_ref) * res_ref - res_cal;
            break;
        }
        tentativas_inicial++;
        delayMicroseconds(200);  // Delay mínimo entre tentativas
    }

    if (resistencia_inicial < 0) {
        DEBUG_PRINTLN(
            "ERRO: Não foi possível ler estado inicial para medição de tempo");
        // Restaura configuração antes de retornar
        ADS.setDataRate(ADC_TAXA_NORMAL);
        return -1.0;
    }

    DEBUG_PRINT("Resistência inicial: ");
    DEBUG_PRINTLN(resistencia_inicial);
    DEBUG_PRINTLN("Iniciando medição de tempo otimizada...");

    // Marca o início da medição usando microssegundos
    unsigned long inicio_medicao = micros();
    unsigned long tempo_acionamento_us = 0;
    bool mudanca_detectada = false;

    // Loop de monitoramento otimizado - SEM delays desnecessários
    while ((micros() - inicio_medicao) < TIMEOUT_ACIONAMENTO &&
           !mudanca_detectada) {
        // Remove delay(INTERVALO_LEITURA_ADC) - deixa o ADC determinar a
        // velocidade

        // Lê valores atuais
        int16_t val_01 = ADS.readADC_Differential_0_1();
        int16_t val_13 = ADS.readADC_Differential_1_3();

        float volts_ref = ADS.toVoltage(val_01);
        float volts = ADS.toVoltage(val_13);

        // Verifica se a leitura é válida
        if (abs(volts_ref) > 0.0001) {
            float resistencia_atual = (volts / volts_ref) * res_ref - res_cal;

            // Detecta mudança significativa de estado
            float diferenca = abs(resistencia_atual - resistencia_inicial);

            // Critério de mudança: diferença maior que o threshold OU
            // mudança de estado fechado<->aberto
            bool mudanca_significativa = (diferenca > THRESHOLD_MUDANCA_ESTADO);
            bool mudanca_estado_aberto =
                (resistencia_inicial < 50.0 && resistencia_atual > 500.0) ||
                (resistencia_inicial > 500.0 && resistencia_atual < 50.0);

            if (mudanca_significativa || mudanca_estado_aberto) {
                tempo_acionamento_us = micros() - inicio_medicao;
                mudanca_detectada = true;

                DEBUG_PRINT("Mudança detectada! Resistência: ");
                DEBUG_PRINT(resistencia_inicial);
                DEBUG_PRINT(" -> ");
                DEBUG_PRINTLN(resistencia_atual);
                DEBUG_PRINT("Tempo de acionamento: ");
                DEBUG_PRINT(tempo_acionamento_us);
                DEBUG_PRINTLN(" us");
                break;
            }
        }
    }

    // Restaura configuração normal do ADC
    ADS.setDataRate(ADC_TAXA_NORMAL);  // Volta para 128 SPS

    if (!mudanca_detectada) {
        DEBUG_PRINTLN("TIMEOUT: Mudança de estado não detectada");
        return -1.0;
    }

    // Converte de microssegundos para milissegundos
    float tempo_ms = tempo_acionamento_us / 1000.0;

    DEBUG_PRINT("Tempo final: ");
    DEBUG_PRINT(tempo_ms);
    DEBUG_PRINTLN(" ms");

    return tempo_ms;
}

/**
 * @brief Mede o tempo de acionamento após o relé já ter sido acionado
 * Versão otimizada com resolução de microssegundos e ADC em máxima velocidade
 * @return Tempo de acionamento em milissegundos ou -1.0 em caso de erro/timeout
 */
float medirTempoAcionamentoAposAcionamento() {
    if (!ADS.isConnected()) {
        DEBUG_PRINTLN("ERRO: ADS não conectado durante medição de tempo");
        return -1.0;
    }

    // Configura ADC para máxima velocidade (860 SPS = ~1.16ms por leitura)
    ADS.setDataRate(ADC_TAXA_RAPIDA);  // 860 SPS para máxima resolução temporal
    ADS.setGain(1);

    // Aguarda estabilização mínima (reduzido para otimizar timing)
    delayMicroseconds(500);  // 0.5ms em vez de 5ms

    DEBUG_PRINTLN("Iniciando medição de tempo OTIMIZADA...");

    // Marca o início da medição usando microssegundos para máxima precisão
    unsigned long inicio_medicao = micros();
    unsigned long tempo_acionamento_us = 0;
    bool mudanca_detectada = false;

    // Lê o estado inicial com menos tentativas para otimizar velocidade
    float resistencia_inicial = -1.0;
    for (int tentativa = 0; tentativa < 2; tentativa++) {
        int16_t val_01 = ADS.readADC_Differential_0_1();
        int16_t val_13 = ADS.readADC_Differential_1_3();

        float volts_ref = ADS.toVoltage(val_01);
        float volts = ADS.toVoltage(val_13);

        if (abs(volts_ref) > 0.0001) {
            resistencia_inicial = (volts / volts_ref) * res_ref - res_cal;
            break;
        }
        delayMicroseconds(200);  // Delay mínimo entre tentativas
    }

    if (resistencia_inicial < 0) {
        DEBUG_PRINTLN("ERRO: Não foi possível ler estado inicial");
        // Restaura configuração normal antes de retornar
        ADS.setDataRate(ADC_TAXA_NORMAL);
        return -1.0;
    }

    DEBUG_PRINT("Resistência inicial: ");
    DEBUG_PRINTLN(resistencia_inicial);

    // Loop de monitoramento otimizado - SEM delays desnecessários
    // A velocidade é limitada apenas pela taxa do ADC (860 SPS = ~1.16ms)
    while ((micros() - inicio_medicao) < TIMEOUT_ACIONAMENTO &&
           !mudanca_detectada) {
        // Remove delay(INTERVALO_LEITURA_ADC) - deixa o ADC determinar a
        // velocidade

        // Lê valores atuais
        int16_t val_01 = ADS.readADC_Differential_0_1();
        int16_t val_13 = ADS.readADC_Differential_1_3();

        float volts_ref = ADS.toVoltage(val_01);
        float volts = ADS.toVoltage(val_13);

        // Verifica se a leitura é válida
        if (abs(volts_ref) > 0.0001) {
            float resistencia_atual = (volts / volts_ref) * res_ref - res_cal;

            // Detecta mudança significativa de estado
            float diferenca = abs(resistencia_atual - resistencia_inicial);

            bool mudanca_significativa = (diferenca > THRESHOLD_MUDANCA_ESTADO);
            bool mudanca_estado_aberto =
                (resistencia_inicial < 50.0 && resistencia_atual > 500.0) ||
                (resistencia_inicial > 500.0 && resistencia_atual < 50.0);

            if (mudanca_significativa || mudanca_estado_aberto) {
                tempo_acionamento_us = micros() - inicio_medicao;
                mudanca_detectada = true;

                DEBUG_PRINT("Mudança detectada! Resistência: ");
                DEBUG_PRINT(resistencia_inicial);
                DEBUG_PRINT(" -> ");
                DEBUG_PRINTLN(resistencia_atual);
                DEBUG_PRINT("Tempo de acionamento: ");
                DEBUG_PRINT(tempo_acionamento_us);
                DEBUG_PRINTLN(" us");
                break;
            }
        }
    }

    // Restaura configuração normal do ADC
    ADS.setDataRate(ADC_TAXA_NORMAL);

    if (!mudanca_detectada) {
        DEBUG_PRINTLN("TIMEOUT: Mudança de estado não detectada");
        return -1.0;
    }

    // Converte de microssegundos para milissegundos com alta precisão
    float tempo_ms = tempo_acionamento_us / 1000.0;

    DEBUG_PRINT("Tempo final: ");
    DEBUG_PRINT(tempo_ms);
    DEBUG_PRINTLN(" ms");

    return tempo_ms;
}

void action_relay(int relay_action) {
    relay_state = !relay_state;
    digitalWrite(relay_action, relay_state);

    // Usar arrays de caracteres para debug
    char relay_type[8];
    strcpy(relay_type, (relay_action == RELAY_DC) ? "DC" : "AC");

    char relay_status[16];
    strcpy(relay_status, relay_state ? "ENERGIZADO" : "DESENERGIZADO");

    DEBUG_PRINT("Relé ");
    DEBUG_PRINT(relay_type);
    DEBUG_PRINT(" ");
    DEBUG_PRINTLN(relay_status);
}

/**
 * @brief Aciona o relé com medição de tempo de acionamento
 * @param relay_pin Pino do relé (RELAY_DC ou RELAY_AC)
 * @param estado_desejado true para energizar, false para desenergizar
 * @param medir_tempo true para medir o tempo de acionamento
 * @return Tempo de acionamento em ms (se medir_tempo=true) ou 0.0
 */
float acionarReleComTempo(int relay_pin, bool estado_desejado,
                          bool medir_tempo = false) {
    float tempo_acionamento = 0.0;

    // Debug do estado atual
    char relay_type[8];
    strcpy(relay_type, (relay_pin == RELAY_DC) ? "DC" : "AC");

    char estado_str[16];
    strcpy(estado_str, estado_desejado ? "ENERGIZAR" : "DESENERGIZAR");

    DEBUG_PRINT("Acionando relé ");
    DEBUG_PRINT(relay_type);
    DEBUG_PRINT(" para ");
    DEBUG_PRINTLN(estado_str);

    // Se deve medir tempo e o relé está mudando de estado
    if (medir_tempo && (digitalRead(relay_pin) != estado_desejado)) {
        // Configura o ADC para leituras rápidas antes de acionar
        if (ADS.isConnected()) {
            ADS.setDataRate(ADC_TAXA_RAPIDA);  // 860 SPS para máxima velocidade
            ADS.setGain(1);
            delayMicroseconds(500);  // Aguarda estabilização mínima
        }

        // Aciona o relé e simultaneamente inicia a medição
        digitalWrite(relay_pin, estado_desejado);
        tempo_acionamento = medirTempoAcionamentoAposAcionamento();
        ultimo_tempo_acionamento = tempo_acionamento;
    } else {
        // Aciona o relé normalmente sem medição
        digitalWrite(relay_pin, estado_desejado);
    }

    // Atualiza estado global se necessário
    if ((relay_pin == RELAY_DC && estado_desejado) ||
        (relay_pin == RELAY_AC && estado_desejado)) {
        relay_state = true;
    } else if ((relay_pin == RELAY_DC && !estado_desejado) ||
               (relay_pin == RELAY_AC && !estado_desejado)) {
        relay_state = false;
    }

    return tempo_acionamento;
}

// =================================================================
// FUNÇÕES DE COMUNICAÇÃO BLE
// =================================================================

bool sendJsonResponse(const JsonDocument& doc) {
    if (!deviceConnected || !pSendCharacteristic) {
        return false;
    }

    // Verifica se é uma mensagem crítica
    const char* status = doc["status"];
    bool isCritical =
        status &&
        (strcmp(status, "prompt") == 0 || strcmp(status, "test_current") == 0 ||
         strcmp(status, "calibration_init") == 0 ||
         strcmp(status, "calibration_processing") == 0 ||
         strcmp(status, "test_init") == 0 ||
         strcmp(status, "test_starting") == 0 ||
         strcmp(status, "test_complete") == 0 ||
         strcmp(status, "button_pressed") == 0 || strcmp(status, "error") == 0);

    // Verifica se pode enviar baseado no controle de fluxo (apenas para
    // mensagens não-críticas)
    if (!isCritical && !canSendMessage()) {
        DEBUG_PRINTLN("Mensagem rejeitada - controle de fluxo");
        return false;
    }

    // Controle de taxa de envio mais conservador
    unsigned long currentTime = millis();
    if (currentTime - lastDataSent < MIN_DATA_INTERVAL) {
        if (isCritical) {
            delay(MIN_DATA_INTERVAL - (currentTime - lastDataSent));
        } else {
            return false;  // Rejeita mensagens não-críticas
        }
    }

    // Serializa JSON e verifica validade
    size_t jsonSize = serializeJson(doc, jsonBuffer, sizeof(jsonBuffer));
    if (jsonSize == 0 || jsonSize >= sizeof(jsonBuffer)) {
        DEBUG_PRINTLN("Erro: JSON inválido ou muito grande");
        return false;
    }

    // Envio único sem retry para evitar sobrecarga
    // Verifica conexão uma última vez antes de enviar
    if (!deviceConnected) {
        return false;
    }

    // Envia dados com verificação de sucesso
    pSendCharacteristic->setValue((uint8_t*)jsonBuffer, jsonSize);
    pSendCharacteristic->notify();

    lastDataSent = millis();
    lastSuccessfulOperation = millis();

    // Pequeno delay para estabilizar após envio crítico
    if (status && strcmp(status, "test_complete") == 0) {
        delay(50);  // Aguarda um pouco após test_complete
    }

    updateAdaptiveInterval(true);
    return true;
}

/**
 * @brief Envia mensagem crítica com ACK
 */
bool sendCriticalMessage(const JsonDocument& doc, bool requiresAck = true) {
    if (!deviceConnected || !pSendCharacteristic) {
        return false;
    }

    // Gera ID único para a mensagem
    generateMessageId();

    // Cria documento modificado com messageId
    StaticJsonDocument<600> modifiedDoc;

    // Copia o documento original usando serializeJson/deserializeJson
    String jsonString;
    serializeJson(doc, jsonString);
    deserializeJson(modifiedDoc, jsonString);

    if (requiresAck) {
        modifiedDoc["messageId"] = currentMessageId;
        modifiedDoc["requiresAck"] = true;

        // Pausa heartbeat para operação crítica
        pauseHeartbeat(10000);  // 10 segundos
    }

    // Envia usando a função padrão
    bool success = sendJsonResponse(modifiedDoc);

    if (success && requiresAck) {
        // Configura timeout para ACK
        awaitingAck = true;
        ackTimeout = millis() + 5000;  // 5 segundos timeout
        commState = COMM_WAITING_ACK;
    }

    return success;
}
bool sendCriticalPrompt(const JsonDocument& doc) {
    // Para prompts, não exige ACK - apenas envia como mensagem crítica
    return sendCriticalMessage(doc, false);
}

void sendError(const char* message) {
    StaticJsonDocument<200> doc;
    doc["status"] = "error";
    doc["message"] = message;
    sendCriticalMessage(doc, true);  // Erros também são críticos
}

void sendHeartbeat() {
    // Só envia heartbeat se não enviou dados recentemente E não está em
    // operação crítica
    if (millis() - lastDataSent > HEARTBEAT_INTERVAL &&
        !g_aguardandoConfirmacao) {
        StaticJsonDocument<150> doc;
        doc["status"] = "heartbeat";
        doc["timestamp"] = millis();
        doc["freeHeap"] = ESP.getFreeHeap();  // Diagnóstico de memória
        doc["uptime"] = millis() - connectionStartTime;  // Tempo de conexão
        doc["reconnections"] = totalReconnections;       // Número de reconexões
        sendJsonResponse(doc);
    }
}

void sendDeviceStatus() {
    StaticJsonDocument<400> doc;
    doc["status"] = "device_status";
    doc["timestamp"] = millis();

    // Mapeia o estado do dispositivo para string
    const char* stateStr = "idle";
    switch (currentDeviceState) {
        case DEVICE_IDLE:
            stateStr = "idle";
            break;
        case DEVICE_CALIBRATING:
            stateStr = "calibrating";
            break;
        case DEVICE_TESTING:
            stateStr = "testing";
            break;
        case DEVICE_WAITING_BUTTON:
            stateStr = "waiting_for_button";
            break;
        case DEVICE_ERROR:
            stateStr = "error";
            break;
    }

    doc["currentState"] = stateStr;
    doc["commState"] = commState;
    doc["freeHeap"] = ESP.getFreeHeap();
    doc["uptime"] = millis();

    // Adiciona informações do teste atual se disponível
    if (currentTestStep >= 0) {
        doc["currentStep"] = currentTestStep;
    }

    if (strlen(currentModule) > 0) {
        doc["currentModule"] = currentModule;
    }

    sendJsonResponse(doc);
}

bool checkConnection() {
    unsigned long currentTime = millis();

    // Verifica se a conexão mudou de estado
    if (deviceConnected != oldDeviceConnected) {
        if (deviceConnected) {
            DEBUG_PRINTLN("Conexão estabelecida");
            state_RGB('B');  // Verde - conectado
            connectionLost = false;
            retryCount = 0;  // Reset contador de tentativas
        } else {
            DEBUG_PRINTLN("Conexão perdida");
            reset_output();
            connectionLost = true;
        }
        oldDeviceConnected = deviceConnected;
    }

    // Envia heartbeat periodicamente (somente se necessário)
    if (deviceConnected && (currentTime - lastHeartbeat > HEARTBEAT_INTERVAL)) {
        // Verifica se realmente precisa enviar heartbeat
        if (currentTime - lastDataSent > HEARTBEAT_INTERVAL / 2) {
            sendHeartbeat();
        }
        lastHeartbeat = currentTime;
    }

    return deviceConnected;
}

/**
 * @brief Aguarda o usuário pressionar o botão físico na jiga
 * Envia status para o WebApp e aguarda confirmação física
 */
void aguardarBotaoJiga(const char* mensagem = "") {
    // Atualiza estado do dispositivo
    currentDeviceState = DEVICE_WAITING_BUTTON;

    // Envia prompt para a WebApp usando função crítica
    StaticJsonDocument<300> promptDoc;
    promptDoc["status"] = "prompt";
    if (strlen(mensagem) > 0) {
        promptDoc["message"] = mensagem;
    } else {
        promptDoc["message"] = "Pressione o botão na jiga para continuar";
    }

    if (!sendCriticalPrompt(promptDoc)) {
        DEBUG_PRINTLN("ERRO: Falha ao enviar prompt - conexão instável");
        return;
    } else {
        DEBUG_PRINTLN("SUCCESS: Prompt enviado com sucesso para WebApp");
    }

    // Acende LED indicativo
    digitalWrite(LED_CONT, 1);
    state_RGB('O');  // Azul - aguardando

    // Aguarda botão ser pressionado com timeout e verificação de conexão
    unsigned long startTime = millis();
    const unsigned long TIMEOUT = 120000;  // 2 minutos timeout

    while (digitalRead(BUTTON) == 0) {
        // Verifica timeout
        if (millis() - startTime > TIMEOUT) {
            DEBUG_PRINTLN("TIMEOUT: Aguardando botão da jiga");
            digitalWrite(LED_CONT, 0);
            reset_output();
            sendError("Timeout aguardando botão da jiga");
            return;
        }

        delay(50);

        // Verifica conexão menos frequentemente (a cada 2 segundos)
        if ((millis() - startTime) % 2000 == 0) {
            if (!checkConnection()) {
                DEBUG_PRINTLN("ERRO: Conexão perdida durante aguardo do botão");
                digitalWrite(LED_CONT, 0);
                reset_output();
                return;
            }
        }
    }

    DEBUG_PRINTLN("SUCCESS: Botão pressionado!");
    // Botão pressionado - confirma para WebApp
    digitalWrite(LED_CONT, 0);
    state_RGB('B');  // Verde - confirmado

    StaticJsonDocument<100> confirmDoc;
    confirmDoc["status"] = "button_pressed";

    if (!sendJsonResponse(confirmDoc)) {
        DEBUG_PRINTLN("Falha ao enviar confirmação do botão");
    }

    delay(500);  // Debounce
    DEBUG_PRINTLN(">>> Botão pressionado! Continuando...");
}

/**
 * @brief Aguarda confirmação da WebApp (usado em alguns casos específicos)
 */
void aguardarConfirmacaoWebApp() {
    DEBUG_PRINTLN(">>> Aguardando confirmação da WebApp...");
    g_aguardandoConfirmacao = true;

    unsigned long startTime = millis();
    while (g_aguardandoConfirmacao) {
        delay(50);

        // Timeout de 30 segundos
        if (millis() - startTime > 30000) {
            DEBUG_PRINTLN("Timeout aguardando confirmação da WebApp");
            g_aguardandoConfirmacao = false;
            return;
        }

        // Verifica conexão
        if (!checkConnection()) {
            DEBUG_PRINTLN("Conexão perdida durante aguardo de confirmação");
            g_aguardandoConfirmacao = false;
            return;
        }
    }

    DEBUG_PRINTLN(">>> Confirmação recebida! Continuando...");
}

// =================================================================
// FUNÇÕES DE MEDIÇÃO E CALIBRAÇÃO
// =================================================================

void calibrate() {
    // Atualiza estado do dispositivo
    currentDeviceState = DEVICE_CALIBRATING;
    currentTestStep = -1;
    memset(currentModule, 0, sizeof(currentModule));
    strcpy(currentModule, "calibration");

    // Envia status inicial
    StaticJsonDocument<200> statusDoc;
    statusDoc["status"] = "calibration_init";
    statusDoc["message"] = "Iniciando calibração aprimorada...";
    sendJsonResponse(statusDoc);

    aguardarBotaoJiga(
        "Calibração: Conecte os fios de medição em curto-circuito e pressione "
        "o botão na jiga");

    if (!deviceConnected)
        return;

    // Verifica conexão
    if (!checkConnection()) {
        DEBUG_PRINTLN("Conexão perdida durante calibração");
        return;
    }

    // Número de verificações de calibração
    const int NUM_VERIFICACOES = 4;
    const float TOLERANCIA_VARIACAO =
        0.05;  // 5% de variação máxima entre medições

    float medicoes_cal[NUM_VERIFICACOES];
    int medicoes_validas = 0;

    // Envia status de processamento
    statusDoc["status"] = "calibration_processing";
    statusDoc["message"] = "Realizando múltiplas verificações de calibração...";
    sendJsonResponse(statusDoc);

    state_RGB('R');  // Vermelho - processando
    delay(500);      // Aguarda estabilização

    // Realiza múltiplas verificações de calibração
    for (int i = 0; i < NUM_VERIFICACOES; i++) {
        // Aguarda entre verificações para garantir estabilidade
        if (i > 0) {
            delay(1000);
        }

        // Usa a função de medição otimizada para calibração
        float medicao = get_res_calibracao();

        if (medicao == -1.0) {
            continue;
        }

        // Verifica se a medição está dentro de uma faixa razoável para
        // calibração
        if (medicao >
            100.0) {  // Muito alta para uma calibração (curto-circuito)
            continue;
        }

        medicoes_cal[medicoes_validas] = medicao;
        medicoes_validas++;

        // Feedback visual
        digitalWrite(LED_CONT, !digitalRead(LED_CONT));
    }

    // Verifica se obtivemos medições suficientes
    if (medicoes_validas < 2) {
        state_RGB('R');  // Vermelho - erro

        StaticJsonDocument<200> errorDoc;
        errorDoc["status"] = "calibration_error";
        errorDoc["message"] =
            "Falha na calibração - medições insuficientes. Verifique o "
            "curto-circuito.";
        sendJsonResponse(errorDoc);

        delay(2000);
        reset_output();
        return;
    }

    // Calcula estatísticas das medições
    float soma = 0.0;
    float valor_min = medicoes_cal[0];
    float valor_max = medicoes_cal[0];

    for (int i = 0; i < medicoes_validas; i++) {
        soma += medicoes_cal[i];
        if (medicoes_cal[i] < valor_min)
            valor_min = medicoes_cal[i];
        if (medicoes_cal[i] > valor_max)
            valor_max = medicoes_cal[i];
    }

    float media = soma / medicoes_validas;
    float variacao = (valor_max - valor_min) / media;

    // Verifica se a variação entre medições é aceitável
    if (variacao > TOLERANCIA_VARIACAO) {
        state_RGB('R');  // Vermelho - erro

        StaticJsonDocument<200> errorDoc;
        errorDoc["status"] = "calibration_warning";
        errorDoc["message"] =
            "Variação alta entre medições. Verifique a estabilidade do "
            "contato.";
        sendJsonResponse(errorDoc);

        // Prossegue com a calibração mas com aviso
        delay(2000);
    }

    // Aplica média aparada nas medições de calibração se tiver amostras
    // suficientes
    if (medicoes_validas >= 3) {
        res_cal = calcularMediaAparada(medicoes_cal, medicoes_validas, 0.1);
        DEBUG_PRINTLN("Calibração usando média aparada");
    } else {
        res_cal = media;
        DEBUG_PRINTLN("Calibração usando média simples");
    }

    // Validação final do resultado
    if (isnan(res_cal) || isinf(res_cal)) {
        state_RGB('R');  // Vermelho - erro

        StaticJsonDocument<200> errorDoc;
        errorDoc["status"] = "calibration_error";
        errorDoc["message"] = "Valor de calibração inválido - tente novamente";
        sendJsonResponse(errorDoc);

        delay(2000);
        reset_output();
        return;
    }

    state_RGB('B');  // Verde - sucesso

    char res_cal_str[32];
    snprintf(res_cal_str, sizeof(res_cal_str), "%.6f", res_cal);

    // Envia resultado da calibração
    StaticJsonDocument<200> calDoc;
    calDoc["status"] = "calibration_complete";
    calDoc["valor"] = res_cal;
    calDoc["verificacoes"] = medicoes_validas;
    calDoc["variacao_percentual"] = variacao * 100;
    calDoc["message"] = "Calibração concluída com sucesso!";
    sendJsonResponse(calDoc);

    delay(1000);
    reset_output();

    // Retorna ao estado idle
    currentDeviceState = DEVICE_IDLE;
    currentTestStep = -1;
    memset(currentModule, 0, sizeof(currentModule));
}

float medirResistencia() {
    state_RGB('R');  // Vermelho - medindo

    DEBUG_PRINTLN("=== Iniciando medição de resistência com média aparada ===");

    // Aguarda estabilização após mudança de estado do relé
    delay(100);

    // Teste rápido para detecção imediata de circuito aberto
    DEBUG_PRINTLN("Fazendo teste rápido para detectar circuito aberto...");
    float teste_rapido = get_res();

    if (teste_rapido >= 5000.0) {
        DEBUG_PRINTLN("Circuito aberto detectado no teste rápido!");
        digitalWrite(LED_CONT, 0);
        state_RGB('B');
        delay(300);
        reset_output();
        return teste_rapido;
    }

    // Coleta as amostras para aplicar média aparada
    float amostras[MEAN];
    int leituras_validas = 0;
    int tentativas_max = MEAN * 3;  // Permite mais tentativas
    int tentativas = 0;

    // Coleta as amostras
    while (leituras_validas < MEAN && tentativas < tentativas_max) {
        float leitura = get_res();
        tentativas++;

        if (leitura >= 0.0) {
            // Detecção de circuito aberto durante a coleta
            if (leitura >= 5000.0) {
                DEBUG_PRINTLN(
                    "Circuito aberto detectado - interrompendo coleta");
                digitalWrite(LED_CONT, 0);
                state_RGB('B');
                delay(300);
                reset_output();
                return leitura;
            }

            amostras[leituras_validas] = leitura;
            leituras_validas++;

            // Feedback visual
            if (leituras_validas % 5 == 0) {
                digitalWrite(LED_CONT, !digitalRead(LED_CONT));
            }
        }

        delay(10);
    }

    // Verifica se coletou amostras suficientes
    int minimo_leituras = (MEAN * 6) / 10;  // 60% das amostras
    if (leituras_validas < minimo_leituras) {
        digitalWrite(LED_CONT, 0);
        state_RGB('R');
        delay(500);
        reset_output();
        return -1.0;
    }

    // Aplica média aparada (descarta 10% dos valores extremos)
    float resistencia_bruta =
        calcularMediaAparada(amostras, leituras_validas, 0.1);

    // Aplica calibração
    float resistencia;
    if (resistencia_bruta > 5000.0) {
        // Circuito aberto - não aplicar calibração
        resistencia = resistencia_bruta;
        DEBUG_PRINTLN("Circuito aberto detectado - calibração não aplicada");
    } else {
        // Resistência normal - aplicar calibração
        resistencia = resistencia_bruta - res_cal;
    }

    digitalWrite(LED_CONT, 0);
    state_RGB('B');
    delay(300);
    reset_output();

    return resistencia;
}
// =================================================================
// ROTINAS DE TESTE
// =================================================================

/**
 * @brief Executa teste especial para apenas 1 contato
 * Como não sabemos se o usuário vai testar NF ou NA, medimos COM-N# nos dois
 * estados sem avaliar se passou ou falhou, apenas registramos os valores
 */
void executarTesteEspecialUmContato(const TestConfig& config) {
    // Envia status inicial
    StaticJsonDocument<200> statusDoc;
    statusDoc["status"] = "test_special_init";
    statusDoc["message"] = "Iniciando teste especial para 1 contato...";
    sendJsonResponse(statusDoc);

    int totalTestes = 2;
    int testeAtual = 0;

    // Envia mensagem inicial
    StaticJsonDocument<200> initDoc;
    initDoc["status"] = "test_init";
    initDoc["totalTests"] = totalTestes;
    sendJsonResponse(initDoc);

    // --- TESTE 1: ESTADO DESENERGIZADO ---
    // Sinaliza teste atual
    StaticJsonDocument<200> testingDoc;
    testingDoc["status"] = "test_current";
    testingDoc["testIndex"] = testeAtual;
    testingDoc["pair"] = 0;
    testingDoc["state"] = "DESENERGIZADO";
    sendJsonResponse(testingDoc);

    // Atualiza o passo atual do teste
    currentTestStep = testeAtual;

    aguardarBotaoJiga(
        "TESTE Contato #1 - COM-N#: Relé DESENERGIZADO. Conecte o "
        "multímetro entre COM e o contato N# (NF ou NA) e pressione o botão");

    if (!deviceConnected)
        return;

    // Realiza medição
    float resDesenergizado = medirResistencia();

    // Converte resistência para string usando função auxiliar
    char res_str[BUFFER_SIZE_RESISTENCIA];
    resistenciaParaString(resDesenergizado, res_str, sizeof(res_str));

    // Envia resultado sem avaliação de aprovação
    StaticJsonDocument<200> resultDoc;
    resultDoc["status"] = "test_result";
    resultDoc["testIndex"] = testeAtual;
    resultDoc["contato"] = "COM-N# 1";
    resultDoc["estado"] = "DESENERGIZADO";
    resultDoc["resistencia"] = res_str;
    resultDoc["esperado"] = "VARIÁVEL";
    resultDoc["passou"] = true;  // Sempre passa no teste especial
    sendJsonResponse(resultDoc);

    testeAtual++;

    // --- ACIONAMENTO DO RELÉ COM MEDIÇÃO DE TEMPO ---
    float tempo_acionamento = 0.0;

    if (strcmp(config.tipoAcionamento, "TIPO_DC") == 0) {
        tempo_acionamento = acionarReleComTempo(RELAY_DC, true, true);
        state_RGB('O');  // Azul - energizado
    } else {             // TIPO_AC
        tempo_acionamento = acionarReleComTempo(RELAY_AC, true, true);
        state_RGB('O');  // Azul - energizado
    }

    delay(500);  // Tempo para estabilização

    // --- TESTE 2: ESTADO ENERGIZADO ---
    testingDoc["testIndex"] = testeAtual;
    testingDoc["pair"] = 0;
    testingDoc["state"] = "ENERGIZADO";
    sendJsonResponse(testingDoc);

    aguardarBotaoJiga(
        "TESTE Contato #1 - COM-N#: Relé ENERGIZADO. Conecte o multímetro "
        "entre COM e o contato N# (NF ou NA) e pressione o botão");

    if (!deviceConnected)
        return;

    // Realiza medição
    float resEnergizado = medirResistencia();

    // Reutiliza o buffer res_str já declarado
    resistenciaParaString(resEnergizado, res_str, sizeof(res_str));

    // Envia resultado sem avaliação de aprovação
    resultDoc["status"] = "test_result";
    resultDoc["testIndex"] = testeAtual;
    resultDoc["contato"] = "COM-N# 1";
    resultDoc["estado"] = "ENERGIZADO";
    resultDoc["resistencia"] = res_str;
    resultDoc["esperado"] = "VARIÁVEL";
    resultDoc["passou"] = true;  // Sempre passa no teste especial

    // Adiciona tempo de acionamento se foi medido
    if (tempo_acionamento >= 0) {
        resultDoc["tempo_acionamento_ms"] = tempo_acionamento;

        char tempo_str[32];
        if (tempo_acionamento >= 0) {
            snprintf(tempo_str, sizeof(tempo_str), "%.1f ms",
                     tempo_acionamento);
        } else {
            strcpy(tempo_str, "ERRO");
        }
        resultDoc["tempo_acionamento_str"] = tempo_str;
    }
    sendJsonResponse(resultDoc);

    // Aguarda um pouco para garantir que o resultado foi enviado
    delay(100);

    // --- FINALIZAÇÃO ---
    if (strcmp(config.tipoAcionamento, "TIPO_DC") == 0) {
        digitalWrite(RELAY_DC, 0);
    } else {  // TIPO_AC
        digitalWrite(RELAY_AC, 0);
    }

    reset_output();

    // Aguarda um pouco antes de enviar o status final
    delay(500);  // Aumentado para dar tempo para a conexão se estabilizar

    StaticJsonDocument<200> completeDoc;
    completeDoc["status"] = "test_complete";
    completeDoc["message"] = "Teste especial finalizado com sucesso";
    sendJsonResponse(completeDoc);

    // Retorna ao estado idle
    currentDeviceState = DEVICE_IDLE;
    currentTestStep = -1;
    memset(currentModule, 0, sizeof(currentModule));
}

/**
 * @brief Executa teste configurável para múltiplos contatos
 *
 * Nova sequência alternada para um relé de 5 terminais (2 contatos):
 * 1. COM-NF1 DESENERGIZADO (deve ter baixa resistência ~0Ω)
 * 2. COM-NF1 ENERGIZADO (deve estar aberto ~∞Ω)
 * 3. COM-NA1 DESENERGIZADO (deve estar aberto ~∞Ω)
 * 4. COM-NA1 ENERGIZADO (deve ter baixa resistência ~0Ω)
 * 5. COM-NF2 DESENERGIZADO (deve ter baixa resistência ~0Ω)
 * 6. COM-NF2 ENERGIZADO (deve estar aberto ~∞Ω)
 * 7. COM-NA2 DESENERGIZADO (deve estar aberto ~∞Ω)
 * 8. COM-NA2 ENERGIZADO (deve ter baixa resistência ~0Ω)
 *
 * Ordem alternada: testa completamente cada contato (des/ene) antes de passar
 * ao próximo Benefício: menos trocas de contatos, mais prático para o operador
 */
void executarTesteConfiguravel(const TestConfig& config) {
    // Atualiza estado do dispositivo
    currentDeviceState = DEVICE_TESTING;
    currentTestStep = 0;
    strcpy(currentModule, "testing");

    // Envia status inicial do teste
    StaticJsonDocument<200> statusDoc;
    statusDoc["status"] = "test_starting";
    statusDoc["message"] = "Iniciando teste do módulo...";
    sendJsonResponse(statusDoc);

    // Verifica se é o caso especial de apenas 1 contato
    if (config.quantidadeContatos == 1) {
        DEBUG_PRINTLN("=== EXECUTANDO TESTE ESPECIAL (1 CONTATO) ===");
        executarTesteEspecialUmContato(config);
        return;
    }

    // Calcula quantos contatos NF e NA temos
    // Se o usuário inseriu 2 contatos = 1 NF + 1 NA
    // Se o usuário inseriu 4 contatos = 2 NF + 2 NA
    // Se o usuário inseriu 6 contatos = 3 NF + 3 NA
    int numContatosNF = config.quantidadeContatos / 2;
    int numContatosNA = config.quantidadeContatos / 2;
    int totalTestes =
        config.quantidadeContatos * 2;  // Cada contato testado em 2 estados
    int testeAtual = 0;

    char debug_str[BUFFER_SIZE_DEBUG];
    snprintf(debug_str, sizeof(debug_str), "Número de contatos NF: %d",
             numContatosNF);
    DEBUG_PRINTLN(debug_str);

    snprintf(debug_str, sizeof(debug_str), "Número de contatos NA: %d",
             numContatosNA);
    DEBUG_PRINTLN(debug_str);

    snprintf(debug_str, sizeof(debug_str), "Total de testes: %d", totalTestes);
    DEBUG_PRINTLN(debug_str);

    // Envia mensagem inicial
    StaticJsonDocument<200> initDoc;
    initDoc["status"] = "test_init";
    initDoc["totalTests"] = totalTestes;
    sendJsonResponse(initDoc);

    // --- ORDEM ALTERNADA: TESTA CADA CONTATO COMPLETAMENTE ---
    // Calcula o número máximo de contatos para iterar
    int maxContatos =
        (numContatosNF > numContatosNA) ? numContatosNF : numContatosNA;

    for (int i = 0; i < maxContatos; i++) {
        if (!deviceConnected)
            return;

        // --- CONTATO NF DESENERGIZADO ---
        if (i < numContatosNF) {
            StaticJsonDocument<200> testingDoc;
            testingDoc["status"] = "test_current";
            testingDoc["testIndex"] = testeAtual;
            testingDoc["pair"] = i;
            testingDoc["state"] = "DESENERGIZADO";
            sendJsonResponse(testingDoc);

            char contato_str[BUFFER_SIZE_CONTATO];
            snprintf(contato_str, sizeof(contato_str), "COM-NF%d", i + 1);

            char mensagem_str[BUFFER_SIZE_MENSAGEM];
            snprintf(mensagem_str, sizeof(mensagem_str),
                     "TESTE %s: Relé DESENERGIZADO. Conecte o multímetro entre "
                     "COM e NF%d e pressione o botão",
                     contato_str, i + 1);

            aguardarBotaoJiga(mensagem_str);

            if (!deviceConnected)
                return;

            // Realiza medição
            float resistencia = medirResistencia();

            // Verifica se houve erro na medição
            if (resistencia == -1.0) {
                // Em vez de parar o teste, marca como erro e continua
                StaticJsonDocument<200> resultDoc;
                resultDoc["status"] = "test_result";
                resultDoc["testIndex"] = testeAtual;
                resultDoc["contato"] = contato_str;
                resultDoc["estado"] = "DESENERGIZADO";
                resultDoc["resistencia"] = "ERRO";
                resultDoc["esperado"] = "BAIXA";
                resultDoc["passou"] = false;
                sendJsonResponse(resultDoc);

            } else {
                // Converte resistência para string usando função auxiliar
                char res_str[BUFFER_SIZE_RESISTENCIA];
                resistenciaParaString(resistencia, res_str, sizeof(res_str));

                // Envia resultado - NF desenergizado deve ter baixa resistência
                StaticJsonDocument<200> resultDoc;
                resultDoc["status"] = "test_result";
                resultDoc["testIndex"] = testeAtual;
                resultDoc["contato"] = contato_str;
                resultDoc["estado"] = "DESENERGIZADO";
                resultDoc["resistencia"] = res_str;
                resultDoc["esperado"] = "BAIXA";
                resultDoc["passou"] = (resistencia >= -TOLERANCIA_NEGATIVA &&
                                       resistencia <= LIMITE_BAIXA_RESISTENCIA);
                sendJsonResponse(resultDoc);
            }
            testeAtual++;
        }

        // --- CONTATO NF ENERGIZADO ---
        if (i < numContatosNF) {
            // Aciona o relé antes do teste energizado com medição de tempo
            float tempo_acionamento = 0.0;
            if (strcmp(config.tipoAcionamento, "TIPO_DC") == 0) {
                tempo_acionamento = acionarReleComTempo(RELAY_DC, true, true);
                state_RGB('O');  // Azul - energizado
            } else {
                tempo_acionamento = acionarReleComTempo(RELAY_AC, true, true);
                state_RGB('O');  // Azul - energizado
            }
            delay(500);  // Tempo para estabilização

            StaticJsonDocument<200> testingDoc;
            testingDoc["status"] = "test_current";
            testingDoc["testIndex"] = testeAtual;
            testingDoc["pair"] = i;
            testingDoc["state"] = "ENERGIZADO";
            sendJsonResponse(testingDoc);

            char contato_str[BUFFER_SIZE_CONTATO];
            snprintf(contato_str, sizeof(contato_str), "COM-NF%d", i + 1);

            char mensagem_str[BUFFER_SIZE_MENSAGEM];
            snprintf(mensagem_str, sizeof(mensagem_str),
                     "TESTE %s: Relé ENERGIZADO. Conecte o multímetro entre "
                     "COM e NF%d e pressione o botão",
                     contato_str, i + 1);

            aguardarBotaoJiga(mensagem_str);

            if (!deviceConnected)
                return;

            // Realiza medição
            float resistencia = medirResistencia();

            // Verifica se houve erro na medição
            if (resistencia == -1.0) {
                // Em vez de parar o teste, marca como erro e continua
                StaticJsonDocument<200> resultDoc;
                resultDoc["status"] = "test_result";
                resultDoc["testIndex"] = testeAtual;
                resultDoc["contato"] = contato_str;
                resultDoc["estado"] = "ENERGIZADO";
                resultDoc["resistencia"] = "ERRO";
                resultDoc["esperado"] = "ABERTO";
                resultDoc["passou"] = false;
                sendJsonResponse(resultDoc);

            } else {
                // Converte resistência para string usando função auxiliar
                char res_str[BUFFER_SIZE_RESISTENCIA];
                resistenciaParaString(resistencia, res_str, sizeof(res_str));

                // Envia resultado - NF energizado deve estar aberto
                StaticJsonDocument<200> resultDoc;
                resultDoc["status"] = "test_result";
                resultDoc["testIndex"] = testeAtual;
                resultDoc["contato"] = contato_str;
                resultDoc["estado"] = "ENERGIZADO";
                resultDoc["resistencia"] = res_str;
                resultDoc["esperado"] = "ABERTO";
                resultDoc["passou"] = (resistencia > LIMITE_RESISTENCIA_MINIMA);

                // Adiciona tempo de acionamento se foi medido
                if (tempo_acionamento >= 0) {
                    resultDoc["tempo_acionamento_ms"] = tempo_acionamento;

                    char tempo_str[32];
                    if (tempo_acionamento >= 0) {
                        snprintf(tempo_str, sizeof(tempo_str), "%.1f ms",
                                 tempo_acionamento);
                    } else {
                        strcpy(tempo_str, "ERRO");
                    }
                    resultDoc["tempo_acionamento_str"] = tempo_str;
                }

                sendJsonResponse(resultDoc);
            }

            testeAtual++;

            // Desaciona o relé após o teste
            if (strcmp(config.tipoAcionamento, "TIPO_DC") == 0) {
                digitalWrite(RELAY_DC, 0);
            } else {
                digitalWrite(RELAY_AC, 0);
            }
            reset_output();
            delay(500);  // Tempo para estabilização
        }

        // --- CONTATO NA DESENERGIZADO ---
        if (i < numContatosNA) {
            StaticJsonDocument<200> testingDoc;
            testingDoc["status"] = "test_current";
            testingDoc["testIndex"] = testeAtual;
            testingDoc["pair"] = i;
            testingDoc["state"] = "DESENERGIZADO";
            sendJsonResponse(testingDoc);

            char contato_str[BUFFER_SIZE_CONTATO];
            snprintf(contato_str, sizeof(contato_str), "COM-NA%d", i + 1);

            char mensagem_str[BUFFER_SIZE_MENSAGEM];
            snprintf(mensagem_str, sizeof(mensagem_str),
                     "TESTE %s: Relé DESENERGIZADO. Conecte o multímetro entre "
                     "COM e NA%d e pressione o botão",
                     contato_str, i + 1);

            aguardarBotaoJiga(mensagem_str);

            if (!deviceConnected)
                return;

            // Realiza medição
            float resistencia = medirResistencia();

            // Verifica se houve erro na medição
            if (resistencia == -1.0) {
                // Em vez de parar o teste, marca como erro e continua
                StaticJsonDocument<200> resultDoc;
                resultDoc["status"] = "test_result";
                resultDoc["testIndex"] = testeAtual;
                resultDoc["contato"] = contato_str;
                resultDoc["estado"] = "DESENERGIZADO";
                resultDoc["resistencia"] = "ERRO";
                resultDoc["esperado"] = "ABERTO";
                resultDoc["passou"] = false;
                sendJsonResponse(resultDoc);

            } else {
                // Converte resistência para string usando função auxiliar
                char res_str[BUFFER_SIZE_RESISTENCIA];
                resistenciaParaString(resistencia, res_str, sizeof(res_str));

                // Envia resultado - NA desenergizado deve estar aberto
                StaticJsonDocument<200> resultDoc;
                resultDoc["status"] = "test_result";
                resultDoc["testIndex"] = testeAtual;
                resultDoc["contato"] = contato_str;
                resultDoc["estado"] = "DESENERGIZADO";
                resultDoc["resistencia"] = res_str;
                resultDoc["esperado"] = "ABERTO";
                resultDoc["passou"] = (resistencia > LIMITE_RESISTENCIA_MINIMA);
                sendJsonResponse(resultDoc);
            }

            testeAtual++;
        }

        // --- CONTATO NA ENERGIZADO ---
        if (i < numContatosNA) {
            // Aciona o relé antes do teste energizado com medição de tempo
            float tempo_acionamento_na = 0.0;
            if (strcmp(config.tipoAcionamento, "TIPO_DC") == 0) {
                tempo_acionamento_na =
                    acionarReleComTempo(RELAY_DC, true, true);
                state_RGB('O');  // Azul - energizado
            } else {
                tempo_acionamento_na =
                    acionarReleComTempo(RELAY_AC, true, true);
                state_RGB('O');  // Azul - energizado
            }
            delay(500);  // Tempo para estabilização

            StaticJsonDocument<200> testingDoc;
            testingDoc["status"] = "test_current";
            testingDoc["testIndex"] = testeAtual;
            testingDoc["pair"] = i;
            testingDoc["state"] = "ENERGIZADO";
            sendJsonResponse(testingDoc);

            char contato_str[BUFFER_SIZE_CONTATO];
            snprintf(contato_str, sizeof(contato_str), "COM-NA%d", i + 1);

            char mensagem_str[BUFFER_SIZE_MENSAGEM];
            snprintf(mensagem_str, sizeof(mensagem_str),
                     "TESTE %s: Relé ENERGIZADO. Conecte o multímetro entre "
                     "COM e NA%d e pressione o botão",
                     contato_str, i + 1);

            aguardarBotaoJiga(mensagem_str);

            if (!deviceConnected)
                return;

            // Realiza medição
            float resistencia = medirResistencia();

            // Verifica se houve erro na medição
            if (resistencia == -1.0) {
                // Em vez de parar o teste, marca como erro e continua
                StaticJsonDocument<200> resultDoc;
                resultDoc["status"] = "test_result";
                resultDoc["testIndex"] = testeAtual;
                resultDoc["contato"] = contato_str;
                resultDoc["estado"] = "ENERGIZADO";
                resultDoc["resistencia"] = "ERRO";
                resultDoc["esperado"] = "BAIXA";
                resultDoc["passou"] = false;
                sendJsonResponse(resultDoc);

            } else {
                // Converte resistência para string usando função auxiliar
                char res_str[BUFFER_SIZE_RESISTENCIA];
                resistenciaParaString(resistencia, res_str, sizeof(res_str));

                // Envia resultado - NA energizado deve ter baixa resistência
                StaticJsonDocument<200> resultDoc;
                resultDoc["status"] = "test_result";
                resultDoc["testIndex"] = testeAtual;
                resultDoc["contato"] = contato_str;
                resultDoc["estado"] = "ENERGIZADO";
                resultDoc["resistencia"] = res_str;
                resultDoc["esperado"] = "BAIXA";
                resultDoc["passou"] = (resistencia >= -TOLERANCIA_NEGATIVA &&
                                       resistencia <= LIMITE_BAIXA_RESISTENCIA);

                // Adiciona tempo de acionamento se foi medido
                if (tempo_acionamento_na >= 0) {
                    resultDoc["tempo_acionamento_ms"] = tempo_acionamento_na;

                    char tempo_str[32];
                    if (tempo_acionamento_na >= 0) {
                        snprintf(tempo_str, sizeof(tempo_str), "%.1f ms",
                                 tempo_acionamento_na);
                    } else {
                        strcpy(tempo_str, "ERRO");
                    }
                    resultDoc["tempo_acionamento_str"] = tempo_str;
                }

                sendJsonResponse(resultDoc);
            }

            testeAtual++;

            // Desaciona o relé após o teste
            if (strcmp(config.tipoAcionamento, "TIPO_DC") == 0) {
                digitalWrite(RELAY_DC, 0);
            } else {
                digitalWrite(RELAY_AC, 0);
            }
            reset_output();
            delay(500);  // Tempo para estabilização
        }
    }

    // --- FINALIZAÇÃO ---
    // Garante que o relé está desacionado
    if (strcmp(config.tipoAcionamento, "TIPO_DC") == 0) {
        digitalWrite(RELAY_DC, 0);
    } else {
        digitalWrite(RELAY_AC, 0);
    }
    reset_output();

    // Aguarda um pouco antes de enviar o status final
    delay(500);  // Aumentado para dar tempo para a conexão se estabilizar

    StaticJsonDocument<200> completeDoc;
    completeDoc["status"] = "test_complete";
    completeDoc["message"] = "Teste finalizado com sucesso";
    sendJsonResponse(completeDoc);

    // Retorna ao estado idle
    currentDeviceState = DEVICE_IDLE;
    currentTestStep = -1;
    memset(currentModule, 0, sizeof(currentModule));
}

// =================================================================
// PROCESSAMENTO DE COMANDOS
// =================================================================

void handleCommand(const JsonDocument& doc) {
    // Verifica se é um ACK
    if (doc.containsKey("type") && doc["type"] == "ack") {
        String messageId = doc["messageId"];
        // Processa ACK
        if (awaitingAck && strcmp(currentMessageId, messageId.c_str()) == 0) {
            awaitingAck = false;
            commState = COMM_IDLE;
            updateAdaptiveInterval(true);
            resumeHeartbeat();
        } else {
            DEBUG_PRINT("ACK inválido ou não esperado: ");
            DEBUG_PRINTLN(messageId);
        }
        return;
    }

    // Verifica se a mensagem requer ACK
    bool requiresAck = doc.containsKey("requiresAck") && doc["requiresAck"];
    String messageId = doc["messageId"];

    if (requiresAck && !messageId.isEmpty()) {
        // Envia ACK imediatamente
        sendAck(messageId.c_str());
    }

    const char* comando = doc["comando"];
    if (strcmp(comando, "calibrar") == 0) {
        pauseHeartbeat(30000);  // Pausa por 30 segundos calibração
        calibrate();

    } else if (strcmp(comando, "iniciar_teste") == 0) {
        // Envia ACK antes de iniciar o processo longo
        if (requiresAck && !messageId.isEmpty()) {
            sendAck(messageId.c_str());
        }

        // Atualiza estado do dispositivo
        currentDeviceState = DEVICE_TESTING;
        currentTestStep = 0;

        pauseHeartbeat(30000);  // Pausa por 30 segundos durante teste

        TestConfig config;
        // Copia string com segurança
        strncpy(config.tipoAcionamento, doc["tipoAcionamento"],
                sizeof(config.tipoAcionamento) - 1);
        config.tipoAcionamento[sizeof(config.tipoAcionamento) - 1] =
            '\0';  // Garante terminação nula

        config.quantidadeContatos = doc["quantidadeContatos"];
        config.calibracao = doc["calibracao"].as<JsonArrayConst>();

        if (config.calibracao.size() > 0) {
            res_cal = config.calibracao[0].as<float>();
            char res_cal_str[32];
            snprintf(res_cal_str, sizeof(res_cal_str), "%.6f", res_cal);
        } else {
            sendError("Erro: Dados de calibração não encontrados");
            return;
        }

        executarTesteConfiguravel(config);

    } else if (strcmp(comando, "confirmar_etapa") == 0) {
        g_aguardandoConfirmacao = false;

    } else if (strcmp(comando, "test_complete_ack") == 0) {
        // Confirmação de que o WebApp recebeu o test_complete
        DEBUG_PRINTLN("Confirmação de test_complete recebida do WebApp");
        // Pode ser usado para lógica adicional no futuro

    } else if (strcmp(comando, "heartbeat_pause") == 0) {
        int duration = doc["duration"] | 10000;  // Default 10 segundos
        pauseHeartbeat(duration);

    } else if (strcmp(comando, "heartbeat_resume") == 0) {
        DEBUG_PRINTLN("Resumindo heartbeat...");
        resumeHeartbeat();

    } else if (strcmp(comando, "ping") == 0) {
        DEBUG_PRINTLN("Ping recebido");
        lastClientPing = millis();  // Registra timestamp do último ping
        StaticJsonDocument<200> response;
        response["status"] = "pong";
        response["timestamp"] = millis();
        sendJsonResponse(response);

    } else if (strcmp(comando, "get_status") == 0) {
        DEBUG_PRINTLN("Solicitação de status recebida");
        sendDeviceStatus();

    } else {
        // Usa buffer temporário para evitar overflow
        char error_msg[64];
        snprintf(error_msg, sizeof(error_msg), "Comando não reconhecido: %.20s",
                 comando);
        sendError(error_msg);
    }
}

// =================================================================
// CLASSES DE CALLBACKS BLE
// =================================================================

class MyCharacteristicCallbacks : public BLECharacteristicCallbacks {
    void onWrite(BLECharacteristic* pCharacteristic) {
        String value = pCharacteristic->getValue().c_str();
        if (value.length() > 0 && value.length() < BUFFER_SIZE_COMANDO) {
            // Copia para char array com segurança
            strncpy(g_comandoJson, value.c_str(), BUFFER_SIZE_COMANDO - 1);
            g_comandoJson[BUFFER_SIZE_COMANDO - 1] =
                '\0';  // Garante terminação nula

            g_comandoRecebidoFlag = true;
            // Atualiza timestamp da última comunicação
            lastDataSent = millis();
        }
    }
};

class MyServerCallbacks : public BLEServerCallbacks {
    void onConnect(BLEServer* pServer) {
        deviceConnected = true;
        DEBUG_PRINTLN("Cliente conectado via BLE");

        // Configurações otimizadas para conexão estabelecida
        unsigned long currentTime = millis();
        lastHeartbeat = currentTime;
        lastConnectionCheck = currentTime;
        lastDataSent = currentTime;
        lastSuccessfulOperation = currentTime;
        connectionStartTime = currentTime;
        retryCount = 0;
        totalReconnections++;

        // Reset flags de controle
        g_aguardandoConfirmacao = false;
        g_comandoRecebidoFlag = false;
    }

    void onDisconnect(BLEServer* pServer) {
        deviceConnected = false;
        DEBUG_PRINTLN("Cliente desconectado");
        reset_output();

        // Resetar estado de aguardo se necessário
        g_aguardandoConfirmacao = false;
        g_comandoRecebidoFlag = false;

        // Pausa otimizada antes de reiniciar advertising
        delay(200);  // Reduzido de 500ms para 200ms

        // Reinicia o advertising automaticamente com configurações otimizadas
        BLEAdvertising* pAdvertising = BLEDevice::getAdvertising();
        pAdvertising->stop();
        delay(50);  // Reduzido de 100ms para 50ms
        pAdvertising->start();
        DEBUG_PRINTLN(
            "Advertising reiniciado - Dispositivo disponível novamente");
    }
};

// =================================================================
// SETUP E LOOP PRINCIPAL
// =================================================================

void setup() {
#if DEBUG_ENABLED
    Serial.begin(9600);
#endif

    // Inicializa I2C e ADS1115
    Wire.begin();
    ADS.begin();
    ADS.setGain(1);

    // Configuração dos pinos
    pinMode(LED_CONT, OUTPUT);
    pinMode(RGB_RED, OUTPUT);
    pinMode(RGB_GREEN, OUTPUT);
    pinMode(RGB_BLUE, OUTPUT);
    pinMode(RELAY_AC, OUTPUT);
    pinMode(RELAY_DC, OUTPUT);
    pinMode(BUTTON, INPUT);

    // Estado inicial
    reset_output();

    // Inicializa BLE com configurações otimizadas
    BLEDevice::init("Jiga-Teste-Reles");

    // Configurações avançadas para estabilidade e visibilidade
    BLEDevice::setMTU(256);  // Reduzido para melhor compatibilidade
    BLEDevice::setPower(ESP_PWR_LVL_P6);

    pServer = BLEDevice::createServer();
    pServer->setCallbacks(new MyServerCallbacks());

    BLEService* pService = pServer->createService(BLE_SERVICE_UUID);

    // Característica para receber comandos (WebApp -> ESP32)
    BLECharacteristic* pReceiveCharacteristic = pService->createCharacteristic(
        BLE_RECEIVE_CHARACTERISTIC_UUID,
        BLECharacteristic::PROPERTY_WRITE |
            BLECharacteristic::PROPERTY_WRITE_NR);
    pReceiveCharacteristic->setCallbacks(new MyCharacteristicCallbacks());

    // Característica para enviar respostas (ESP32 -> WebApp)
    pSendCharacteristic = pService->createCharacteristic(
        BLE_SEND_CHARACTERISTIC_UUID,
        BLECharacteristic::PROPERTY_NOTIFY | BLECharacteristic::PROPERTY_READ);
    pSendCharacteristic->addDescriptor(new BLE2902());

    // Configurações otimizadas para as características
    pSendCharacteristic->setNotifyProperty(true);
    pReceiveCharacteristic->setWriteProperty(true);

    pService->start();

    // Inicia advertising com configurações otimizadas para descoberta
    BLEAdvertising* pAdvertising = BLEDevice::getAdvertising();
    pAdvertising->addServiceUUID(BLE_SERVICE_UUID);
    pAdvertising->setScanResponse(true);

    // Define os intervalos de CONEXÃO preferenciais (para estabilidade
    // pós-conexão) O dispositivo irá solicitar à interface para se comunicarem
    // a cada 30-90ms.
    pAdvertising->setMinPreferred(0x18);  // 30ms
    pAdvertising->setMaxPreferred(0x48);  // 90ms

    pAdvertising->setAdvertisementType(ADV_TYPE_IND);

    // Define os intervalos de ADVERTISING (para descoberta antes da conexão)
    // O dispositivo irá se anunciar a cada 50-100ms.
    pAdvertising->setMinInterval(0x50);  // 50ms
    pAdvertising->setMaxInterval(0xA0);  // 100ms

    BLEDevice::startAdvertising();

    if (ADS.isConnected()) {
        state_RGB('O');  // Azul - pronto para conectar
    } else {
        state_RGB('R');  // Vermelho - erro
    }
}

void loop() {
    // Verificação de conexão adaptativa baseada no estado
    static unsigned long lastConnectionCheck = 0;
    unsigned long checkInterval =
        deviceConnected ? 3000 : 1000;  // 3s conectado, 1s desconectado

    if (millis() - lastConnectionCheck > checkInterval) {
        checkConnection();
        lastConnectionCheck = millis();
    }

    // Gerencia timeout de ACK
    if (awaitingAck && millis() > ackTimeout) {
        DEBUG_PRINTLN("Timeout de ACK - mensagem pode ter sido perdida");
        awaitingAck = false;
        commState = COMM_IDLE;
        updateAdaptiveInterval(false);  // Falha na comunicação
        resumeHeartbeat();
    }

    // Monitora timeout de ping do cliente
    if (deviceConnected && lastClientPing > 0 &&
        millis() - lastClientPing > CLIENT_PING_TIMEOUT) {
        DEBUG_PRINTLN("Timeout de ping do cliente - cliente pode ter travado");

        // Se estava em teste, para o teste e volta ao idle
        if (currentDeviceState == DEVICE_TESTING ||
            currentDeviceState == DEVICE_WAITING_BUTTON) {
            DEBUG_PRINTLN("Parando teste devido ao timeout de ping");
            currentDeviceState = DEVICE_IDLE;
            currentTestStep = -1;
            memset(currentModule, 0, sizeof(currentModule));
            reset_output();
            resumeHeartbeat();
        }

        // Reset do timestamp para evitar spam de logs
        lastClientPing = 0;
    }

    // Gerencia pausa do heartbeat
    if (heartbeatPaused && millis() > heartbeatResumeTime) {
        DEBUG_PRINTLN("Tempo de pausa do heartbeat expirado - resumindo");
        resumeHeartbeat();
    }

    // Processa comandos recebidos via BLE
    if (g_comandoRecebidoFlag) {
        g_comandoRecebidoFlag = false;

        StaticJsonDocument<512> doc;
        DeserializationError error = deserializeJson(doc, g_comandoJson);

        if (error) {
            sendError("JSON inválido");
        } else {
            // Verifica se ainda está conectado antes de processar
            if (deviceConnected) {
                handleCommand(doc);
            }
        }
    }

    // Envia heartbeat se não estiver pausado
    static unsigned long lastHeartbeat = 0;
    if (!heartbeatPaused && deviceConnected &&
        millis() - lastHeartbeat > currentHeartbeatInterval) {
        StaticJsonDocument<150> heartbeat;
        heartbeat["status"] = "heartbeat";
        heartbeat["timestamp"] = millis();
        heartbeat["state"] = commState;

        if (sendJsonResponse(heartbeat)) {
            lastHeartbeat = millis();
        }
    }

    // Delay adaptativo baseado no estado da conexão
    if (deviceConnected) {
        delay(10);  // Mais responsivo quando conectado
    } else {
        delay(100);  // Menos recursos quando desconectado
    }
}
