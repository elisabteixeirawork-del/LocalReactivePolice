/*
 * LocalReactivePolice.cpp
 * Plugin para GTA San Andreas - Sistema de Polícia Reativa Local
 *
 * Compilar com: Visual Studio 2019/2022 + plugin-sdk (GTASA)
 * Output: LocalReactivePolice.asi (colocar em /cleo/ ou raiz do GTA SA)
 *
 * Dependências:
 *   - plugin-sdk (https://github.com/DK22Pac/plugin-sdk)
 *   - GTA SA (versão 1.0 US / downgraded)
 *
 * Configuração do projeto VS:
 *   - Character Set: Multi-Byte
 *   - Output Extension: .asi
 *   - Include dirs: plugin-sdk/plugin_sa, plugin-sdk/shared, plugin-sdk/shared/game
 *   - Additional deps: plugin-sdk static libs (conforme README do plugin-sdk)
 */

#include "plugin.h"
#include "CPed.h"
#include "CPlayer.h"
#include "CWorld.h"
#include "CPools.h"
#include "CTaskManager.h"
#include "tasks/TaskSimpleAttack.h"
#include "tasks/TaskComplexKillPedOnFoot.h"
#include "tasks/TaskComplexEnterCarAsDriver.h"

// Necessário para logging
#include <fstream>
#include <ctime>
#include <string>

using namespace plugin;

// ─────────────────────────────────────────────
//  CONFIGURAÇÕES
// ─────────────────────────────────────────────

static constexpr float DETECTION_RADIUS      = 65.0f;  // raio de deteção (metros)
static constexpr float POLICE_ENGAGE_RADIUS  = 80.0f;  // raio em que polícia reage
static constexpr int   CHECK_INTERVAL_FRAMES = 30;     // verificar a cada N frames (~0.5s a 60fps)

// Ativar/desativar logging para ficheiro (debug)
static constexpr bool  ENABLE_LOG = true;
static const char*     LOG_FILE   = "LocalReactivePolice.log";

// ─────────────────────────────────────────────
//  LOGGING
// ─────────────────────────────────────────────

static void Log(const std::string& msg)
{
    if (!ENABLE_LOG) return;

    std::ofstream file(LOG_FILE, std::ios::app);
    if (!file.is_open()) return;

    // Timestamp simples
    std::time_t t = std::time(nullptr);
    char buf[20];
    std::strftime(buf, sizeof(buf), "%H:%M:%S", std::localtime(&t));

    file << "[" << buf << "] " << msg << "\n";
}

// ─────────────────────────────────────────────
//  UTILITÁRIOS
// ─────────────────────────────────────────────

/*
 * Calcula distância 2D entre dois peds (ignora diferença de altura).
 * Mais leve que distância 3D para verificações em loop.
 */
static float GetDistance2D(CPed* a, CPed* b)
{
    if (!a || !b) return 9999.0f;

    float dx = a->GetPosition().x - b->GetPosition().x;
    float dy = a->GetPosition().y - b->GetPosition().y;
    return std::sqrt(dx * dx + dy * dy);
}

/*
 * Calcula distância 2D de um ped a uma posição CVector.
 */
static float GetDistanceToPoint2D(CPed* ped, const CVector& pos)
{
    if (!ped) return 9999.0f;

    float dx = ped->GetPosition().x - pos.x;
    float dy = ped->GetPosition().y - pos.y;
    return std::sqrt(dx * dx + dy * dy);
}

/*
 * Verifica se um ped está atualmente em combate (a atacar outro ped).
 * Usa a task primária da IA; "attack" tasks têm IDs específicos no SA.
 */
static bool IsPedFighting(CPed* ped)
{
    if (!ped) return false;

    // Verifica flag de combate nativa do SA
    // m_nPedFlags.bInVehicle, etc.; usamos GetTaskManager para tasks ativas
    CTaskManager& tm = ped->m_pIntelligence->m_TaskMgr;

    // Task slot PRIMARY (0) é a task de nível mais alto
    CTask* primaryTask = tm.GetTaskPrimary(TASK_PRIMARY_PRIMARY);
    if (!primaryTask) return false;

    int taskType = primaryTask->GetTaskType();

    // IDs de tasks relevantes no GTA SA (plugin-sdk constants):
    //   TASK_COMPLEX_KILL_PED_ON_FOOT  = 167
    //   TASK_COMPLEX_FIGHT             = 134
    //   TASK_SIMPLE_FIGHT              = 140
    //   TASK_COMPLEX_KILL_PED_ON_FOOT_STEALTH = 168
    return (taskType == TASK_COMPLEX_KILL_PED_ON_FOOT         ||
            taskType == TASK_COMPLEX_FIGHT                     ||
            taskType == TASK_SIMPLE_FIGHT                      ||
            taskType == TASK_COMPLEX_KILL_PED_ON_FOOT_STEALTH ||
            taskType == TASK_SIMPLE_GUN_CTRL);
}

/*
 * Verifica se um ped é do tipo polícia (cop).
 * Usa ePedType do enum do plugin-sdk.
 */
static bool IsCopPed(CPed* ped)
{
    if (!ped) return false;

    // ePedType::PED_TYPE_COP = 6 no SA
    return (ped->m_nPedType == PED_TYPE_COP);
}

/*
 * Verifica se o ped está vivo e válido para processar.
 */
static bool IsPedAliveAndValid(CPed* ped)
{
    if (!ped) return false;
    if (ped->m_fHealth <= 0.0f) return false;
    if (ped->bInVehicle) return false;          // ignorar peds em carros
    if (ped->bIsDead) return false;

    return true;
}

/*
 * Força um ped polícia a atacar um alvo específico.
 * Usa CTaskComplexKillPedOnFoot — a task nativa de "ir matar um ped".
 */
static void ForceCopAttackTarget(CPed* cop, CPed* target)
{
    if (!cop || !target) return;
    if (!IsPedAliveAndValid(cop)) return;
    if (!IsPedAliveAndValid(target)) return;

    CTaskManager& tm = cop->m_pIntelligence->m_TaskMgr;

    // Não interromper se já estiver a atacar o mesmo alvo
    CTask* current = tm.GetTaskPrimary(TASK_PRIMARY_PRIMARY);
    if (current && current->GetTaskType() == TASK_COMPLEX_KILL_PED_ON_FOOT)
    {
        // Já tem uma kill task ativa — não substituir para evitar spam
        return;
    }

    // Criar task de combate: KillPedOnFoot(target, -1, 0, true, true, 100)
    // Parâmetros: alvo, arma (-1 = atual), flags, correr, afastar, range
    CTaskComplexKillPedOnFoot* killTask =
        new CTaskComplexKillPedOnFoot(target, -1, 0, true, true, 100);

    // Definir como task primária
    tm.SetTask(killTask, TASK_PRIMARY_PRIMARY);

    Log("Policia [" + std::to_string((int)cop) + "] engajou alvo [" +
        std::to_string((int)target) + "]");
}

// ─────────────────────────────────────────────
//  CLASSE PRINCIPAL DO PLUGIN
// ─────────────────────────────────────────────

class LocalReactivePolice
{
public:
    LocalReactivePolice()
    {
        Log("=== LocalReactivePolice iniciado ===");

        // Hookar o evento de loop principal do jogo
        Events::gameProcessEvent.Add([this]() {
            this->OnGameProcess();
        });
    }

private:
    int m_frameCounter = 0;

    void OnGameProcess()
    {
        // Só processar a cada CHECK_INTERVAL_FRAMES frames
        // para não sobrecarregar a performance
        m_frameCounter++;
        if (m_frameCounter < CHECK_INTERVAL_FRAMES) return;
        m_frameCounter = 0;

        // Obter o jogador (CJ)
        CPlayerPed* player = FindPlayerPed();
        if (!player) return;

        // Verificar se o jogo está em estado jogável
        if (CGame::currArea != 0 && CGame::currArea != 13) return; // só exterior/interior normal

        ProcessLocalViolence(player);
    }

    /*
     * Lógica principal:
     * 1. Iterar todos os peds no mundo
     * 2. Encontrar pares em combate perto do jogador
     * 3. Para cada agressor encontrado, forçar polícia próxima a reagir
     */
    void ProcessLocalViolence(CPlayerPed* player)
    {
        const CVector& playerPos = player->GetPosition();

        // Listas temporárias para este frame
        std::vector<CPed*> aggressorsNearby;  // peds agressores perto do jogador
        std::vector<CPed*> copsNearby;        // polícias perto do jogador

        // ── Iterar todos os peds via CPools ──
        // CPools::ms_pPedPool contém todos os peds alocados no jogo
        for (int i = 0; i < CPools::ms_pPedPool->m_nSize; i++)
        {
            // Verificar se o slot está ocupado
            if (!CPools::ms_pPedPool->IsSlotUsed(i)) continue;

            CPed* ped = CPools::ms_pPedPool->GetAt(i);
            if (!ped) continue;

            // Ignorar o próprio jogador
            if (ped == player) continue;

            // Só processar peds vivos, a pé
            if (!IsPedAliveAndValid(ped)) continue;

            // Calcular distância ao jogador
            float dist = GetDistanceToPoint2D(ped, playerPos);

            // ── Classificar como polícia ──
            if (IsCopPed(ped) && dist <= POLICE_ENGAGE_RADIUS)
            {
                copsNearby.push_back(ped);
                continue; // polícia não é "agressor" para este sistema
            }

            // ── Verificar se é agressor NPC (não polícia) ──
            if (dist <= DETECTION_RADIUS && IsPedFighting(ped))
            {
                // Confirmar que está a atacar outro NPC (não o jogador)
                CPed* target = GetPedAttackTarget(ped);
                if (target && target != player && !IsCopPed(target))
                {
                    aggressorsNearby.push_back(ped);
                }
            }
        }

        // ── Se não há violência local, nada a fazer ──
        if (aggressorsNearby.empty()) return;

        Log("Violencia local detetada: " + std::to_string(aggressorsNearby.size()) +
            " agressor(es), " + std::to_string(copsNearby.size()) + " policia(s) nearby");

        // ── Para cada polícia perto, forçar reagir ao agressor mais próximo ──
        for (CPed* cop : copsNearby)
        {
            // Encontrar o agressor mais próximo desta polícia
            CPed* closestAggressor = FindClosestPed(cop, aggressorsNearby);
            if (!closestAggressor) continue;

            // Forçar o cop a atacar o agressor
            ForceCopAttackTarget(cop, closestAggressor);
        }
    }

    /*
     * Obtém o alvo atual de um ped em combate.
     * Tenta extrair da task primária de kill.
     */
    CPed* GetPedAttackTarget(CPed* ped)
    {
        if (!ped) return nullptr;

        // O alvo está em m_pTargetedObject ou no task
        // Método mais seguro: usar o campo nativo de targeting
        CPed* target = static_cast<CPed*>(ped->m_pTargetedObject);

        // Verificar se o target é um ped válido (não veículo, não objeto)
        if (target && target->m_nType == ENTITY_TYPE_PED)
            return target;

        return nullptr;
    }

    /*
     * Encontra o ped mais próximo de 'from' dentro de uma lista.
     */
    CPed* FindClosestPed(CPed* from, const std::vector<CPed*>& peds)
    {
        if (!from || peds.empty()) return nullptr;

        CPed* closest  = nullptr;
        float minDist  = 9999.0f;

        for (CPed* candidate : peds)
        {
            if (!candidate) continue;
            float d = GetDistance2D(from, candidate);
            if (d < minDist)
            {
                minDist = d;
                closest = candidate;
            }
        }

        return closest;
    }
};

// ─────────────────────────────────────────────
//  PONTO DE ENTRADA DO PLUGIN
// ─────────────────────────────────────────────

// O plugin-sdk instancia automaticamente os objetos estáticos
// antes do WinMain do jogo correr — basta declarar a instância global.
LocalReactivePolice g_LocalReactivePolice;
