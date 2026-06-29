/*
 * LocalReactivePolice.cpp
 * Plugin para GTA San Andreas - Sistema de Polícia Reativa Local
 * Versão compatível com MSVC moderno (sem dependência de injector.hpp)
 */

// Desativar o injector do plugin-sdk para evitar erros com MSVC 14.29+
#define INJECTOR_GTA_SA_SUPPORT
#define SKIP_INJECTOR

#include "plugin.h"
#include "CPed.h"
#include "CPlayerPed.h"
#include "CPools.h"
#include "CGame.h"
#include "CVector.h"
#include "tasks/TaskComplexKillPedOnFoot.h"
#include "CTaskManager.h"

#include <fstream>
#include <ctime>
#include <string>
#include <vector>
#include <cmath>

using namespace plugin;

// ── Configurações ──
static constexpr float DETECTION_RADIUS      = 65.0f;
static constexpr float POLICE_ENGAGE_RADIUS  = 80.0f;
static constexpr int   CHECK_INTERVAL_FRAMES = 30;
static constexpr bool  ENABLE_LOG            = true;
static const char*     LOG_FILE              = "LocalReactivePolice.log";

// ── Logging ──
static void Log(const std::string& msg)
{
    if (!ENABLE_LOG) return;
    std::ofstream file(LOG_FILE, std::ios::app);
    if (!file.is_open()) return;
    std::time_t t = std::time(nullptr);
    char buf[20];
    std::strftime(buf, sizeof(buf), "%H:%M:%S", std::localtime(&t));
    file << "[" << buf << "] " << msg << "\n";
}

// ── Distância 2D entre dois peds ──
static float GetDistance2D(CPed* a, CPed* b)
{
    if (!a || !b) return 9999.0f;
    float dx = a->GetPosition().x - b->GetPosition().x;
    float dy = a->GetPosition().y - b->GetPosition().y;
    return std::sqrt(dx * dx + dy * dy);
}

static float GetDistanceToPoint2D(CPed* ped, const CVector& pos)
{
    if (!ped) return 9999.0f;
    float dx = ped->GetPosition().x - pos.x;
    float dy = ped->GetPosition().y - pos.y;
    return std::sqrt(dx * dx + dy * dy);
}

// ── Verificar se ped está em combate ──
static bool IsPedFighting(CPed* ped)
{
    if (!ped) return false;
    CTask* task = ped->m_pIntelligence->m_TaskMgr.GetTaskPrimary(TASK_PRIMARY_PRIMARY);
    if (!task) return false;
    int type = task->GetTaskType();
    return (type == TASK_COMPLEX_KILL_PED_ON_FOOT         ||
            type == TASK_COMPLEX_FIGHT                     ||
            type == TASK_SIMPLE_FIGHT                      ||
            type == TASK_COMPLEX_KILL_PED_ON_FOOT_STEALTH ||
            type == TASK_SIMPLE_GUN_CTRL);
}

// ── Verificar se é polícia ──
static bool IsCopPed(CPed* ped)
{
    if (!ped) return false;
    return (ped->m_nPedType == PED_TYPE_COP);
}

// ── Verificar se ped está vivo e a pé ──
static bool IsPedValid(CPed* ped)
{
    if (!ped) return false;
    if (ped->m_fHealth <= 0.0f) return false;
    if (ped->bInVehicle) return false;
    if (ped->bIsDead) return false;
    return true;
}

// ── Obter alvo do ped ──
static CPed* GetAttackTarget(CPed* ped)
{
    if (!ped) return nullptr;
    CEntity* target = ped->m_pTargetedObject;
    if (target && target->m_nType == ENTITY_TYPE_PED)
        return reinterpret_cast<CPed*>(target);
    return nullptr;
}

// ── Forçar cop a atacar alvo ──
static void ForceCopAttackTarget(CPed* cop, CPed* target)
{
    if (!cop || !target) return;
    if (!IsPedValid(cop) || !IsPedValid(target)) return;

    CTaskManager& tm = cop->m_pIntelligence->m_TaskMgr;

    CTask* current = tm.GetTaskPrimary(TASK_PRIMARY_PRIMARY);
    if (current && current->GetTaskType() == TASK_COMPLEX_KILL_PED_ON_FOOT)
        return;

    CTaskComplexKillPedOnFoot* killTask =
        new CTaskComplexKillPedOnFoot(target, -1, 0, true, true, 100);

    tm.SetTask(killTask, TASK_PRIMARY_PRIMARY);
    Log("Policia engajou alvo");
}

// ── Encontrar ped mais próximo numa lista ──
static CPed* FindClosestPed(CPed* from, const std::vector<CPed*>& peds)
{
    CPed* closest = nullptr;
    float minDist = 9999.0f;
    for (CPed* p : peds)
    {
        if (!p) continue;
        float d = GetDistance2D(from, p);
        if (d < minDist) { minDist = d; closest = p; }
    }
    return closest;
}

// ── Classe principal ──
class LocalReactivePolice
{
    int m_frameCounter = 0;

public:
    LocalReactivePolice()
    {
        Log("=== LocalReactivePolice iniciado ===");
        Events::gameProcessEvent.Add([this]() { OnGameProcess(); });
    }

private:
    void OnGameProcess()
    {
        if (++m_frameCounter < CHECK_INTERVAL_FRAMES) return;
        m_frameCounter = 0;

        CPlayerPed* player = FindPlayerPed();
        if (!player) return;

        const CVector& playerPos = player->GetPosition();

        std::vector<CPed*> aggressors;
        std::vector<CPed*> cops;

        for (int i = 0; i < CPools::ms_pPedPool->m_nSize; i++)
        {
            if (!CPools::ms_pPedPool->IsSlotUsed(i)) continue;
            CPed* ped = CPools::ms_pPedPool->GetAt(i);
            if (!ped || ped == player) continue;
            if (!IsPedValid(ped)) continue;

            float dist = GetDistanceToPoint2D(ped, playerPos);

            if (IsCopPed(ped))
            {
                if (dist <= POLICE_ENGAGE_RADIUS)
                    cops.push_back(ped);
                continue;
            }

            if (dist <= DETECTION_RADIUS && IsPedFighting(ped))
            {
                CPed* target = GetAttackTarget(ped);
                if (target && target != player && !IsCopPed(target))
                    aggressors.push_back(ped);
            }
        }

        if (aggressors.empty() || cops.empty()) return;

        Log("Violencia local: " + std::to_string(aggressors.size()) +
            " agressor(es), " + std::to_string(cops.size()) + " policia(s)");

        for (CPed* cop : cops)
        {
            CPed* closest = FindClosestPed(cop, aggressors);
            if (closest)
                ForceCopAttackTarget(cop, closest);
        }
    }
};

LocalReactivePolice g_LocalReactivePolice;
