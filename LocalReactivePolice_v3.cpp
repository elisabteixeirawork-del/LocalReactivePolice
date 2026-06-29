/*
 * LocalReactivePolice.cpp
 * Plugin GTA San Andreas - Policia Reativa Local
 * Versao sem plugin-sdk - apenas Windows API + enderecos de memoria GTA SA 1.0 US
 *
 * Compilar: Visual Studio / MSVC qualquer versao
 * Output: LocalReactivePolice.asi
 * Requer: Ultimate ASI Loader ou Silent's ASI Loader
 */

#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <cmath>
#include <vector>
#include <fstream>
#include <ctime>
#include <string>

// ─────────────────────────────────────────────
//  ENDERECOS DE MEMORIA DO GTA SA 1.0 US
// ─────────────────────────────────────────────

// Pool de peds
#define PED_POOL_PTR        0xB74490  // CPools::ms_pPedPool
#define PLAYER_PED_PTR      0xB6F5F0  // FindPlayerPed() result cache

// Offsets dentro de CPed
#define PED_HEALTH_OFFSET       0x540  // float m_fHealth
#define PED_TYPE_OFFSET         0x528  // byte m_nPedType
#define PED_FLAGS_OFFSET        0x46C  // DWORD flags
#define PED_TASK_MGR_OFFSET     0x4A8  // CTaskManager (inline)
#define PED_TARGET_OFFSET       0x564  // CEntity* m_pTargetedObject
#define PED_IN_VEHICLE_FLAG     (1 << 8) // bInVehicle no flags

// Offsets CTaskManager
#define TASK_PRIMARY_OFFSET     0x00   // tasks[0..4]
#define TASK_PRIMARY_PRIMARY    2      // slot 2 = task principal

// Task types relevantes
#define TASK_COMPLEX_KILL_PED_ON_FOOT       167
#define TASK_COMPLEX_FIGHT                  134
#define TASK_SIMPLE_FIGHT                   140
#define TASK_COMPLEX_KILL_PED_ON_FOOT_STEALTH 168
#define TASK_SIMPLE_GUN_CTRL                160

// PedType
#define PED_TYPE_COP    6

// CEntity type
#define ENTITY_TYPE_PED 4

// Pool struct offsets
#define POOL_OBJECTS_OFFSET     0x00
#define POOL_BYTEARRAY_OFFSET   0x04
#define POOL_SIZE_OFFSET        0x08

// ─────────────────────────────────────────────
//  CONFIGURACOES
// ─────────────────────────────────────────────

static constexpr float DETECTION_RADIUS      = 65.0f;
static constexpr float POLICE_ENGAGE_RADIUS  = 80.0f;
static constexpr int   CHECK_INTERVAL_MS     = 500;  // verificar a cada 500ms
static constexpr bool  ENABLE_LOG            = true;
static const char*     LOG_FILE              = "LocalReactivePolice.log";

// ─────────────────────────────────────────────
//  LOGGING
// ─────────────────────────────────────────────

static void Log(const std::string& msg)
{
    if (!ENABLE_LOG) return;
    std::ofstream f(LOG_FILE, std::ios::app);
    if (!f.is_open()) return;
    std::time_t t = std::time(nullptr);
    char buf[20];
    std::strftime(buf, sizeof(buf), "%H:%M:%S", std::localtime(&t));
    f << "[" << buf << "] " << msg << "\n";
}

// ─────────────────────────────────────────────
//  LEITURA DE MEMORIA
// ─────────────────────────────────────────────

template<typename T>
static T ReadMem(DWORD addr)
{
    return *reinterpret_cast<T*>(addr);
}

template<typename T>
static void WriteMem(DWORD addr, T val)
{
    *reinterpret_cast<T*>(addr) = val;
}

// ─────────────────────────────────────────────
//  ESTRUTURAS SIMPLIFICADAS
// ─────────────────────────────────────────────

struct CVector
{
    float x, y, z;
};

// ─────────────────────────────────────────────
//  POOL DE PEDS
// ─────────────────────────────────────────────

static int GetPedPoolSize()
{
    DWORD pool = ReadMem<DWORD>(PED_POOL_PTR);
    if (!pool) return 0;
    return ReadMem<int>(pool + POOL_SIZE_OFFSET);
}

static DWORD GetPedAt(int index)
{
    DWORD pool = ReadMem<DWORD>(PED_POOL_PTR);
    if (!pool) return 0;

    // Verificar se slot esta usado (byte array: bit 7 = livre)
    DWORD byteArray = ReadMem<DWORD>(pool + POOL_BYTEARRAY_OFFSET);
    if (!byteArray) return 0;

    BYTE flags = ReadMem<BYTE>(byteArray + index);
    if (flags & 0x80) return 0; // slot livre

    DWORD objects = ReadMem<DWORD>(pool + POOL_OBJECTS_OFFSET);
    if (!objects) return 0;

    // Cada ped tem tamanho fixo no pool
    // Tamanho de CPed no SA = 0x7C4
    return objects + (DWORD)(index * 0x7C4);
}

static DWORD GetPlayerPed()
{
    // FindPlayerPed(0) - ped do jogador
    // Endereco direto da variavel PlayerPed
    DWORD ptr = ReadMem<DWORD>(0xB6F5F0);
    return ptr;
}

// ─────────────────────────────────────────────
//  UTILIDADES DE PEDS
// ─────────────────────────────────────────────

static CVector GetPedPosition(DWORD ped)
{
    // CPlaceable::m_matrix esta em offset 0x14, pos em +0x30
    CVector pos = { 0, 0, 0 };
    if (!ped) return pos;
    // matrix no ped: offset 0x44 (CPlaceable offset 0x0, matrix offset 0x44)
    pos.x = ReadMem<float>(ped + 0x30 + 0x14);
    pos.y = ReadMem<float>(ped + 0x34 + 0x14);
    pos.z = ReadMem<float>(ped + 0x38 + 0x14);
    return pos;
}

static float GetDist2D(DWORD pedA, DWORD pedB)
{
    if (!pedA || !pedB) return 9999.0f;
    CVector a = GetPedPosition(pedA);
    CVector b = GetPedPosition(pedB);
    float dx = a.x - b.x;
    float dy = a.y - b.y;
    return std::sqrt(dx * dx + dy * dy);
}

static float GetDist2DToPos(DWORD ped, float px, float py)
{
    if (!ped) return 9999.0f;
    CVector p = GetPedPosition(ped);
    float dx = p.x - px;
    float dy = p.y - py;
    return std::sqrt(dx * dx + dy * dy);
}

static bool IsPedValid(DWORD ped)
{
    if (!ped) return false;
    __try {
        float health = ReadMem<float>(ped + PED_HEALTH_OFFSET);
        if (health <= 0.0f) return false;

        DWORD flags = ReadMem<DWORD>(ped + PED_FLAGS_OFFSET);
        if (flags & PED_IN_VEHICLE_FLAG) return false;

        return true;
    }
    __except (EXCEPTION_EXECUTE_HANDLER) {
        return false;
    }
}

static bool IsCopPed(DWORD ped)
{
    if (!ped) return false;
    __try {
        BYTE pedType = ReadMem<BYTE>(ped + PED_TYPE_OFFSET);
        return (pedType == PED_TYPE_COP);
    }
    __except (EXCEPTION_EXECUTE_HANDLER) {
        return false;
    }
}

static bool IsPedFighting(DWORD ped)
{
    if (!ped) return false;
    __try {
        // CTaskManager esta em ped + PED_TASK_MGR_OFFSET
        // tasks[] sao ponteiros, task primaria esta no slot TASK_PRIMARY_PRIMARY
        DWORD taskMgr = ped + PED_TASK_MGR_OFFSET;
        DWORD task = ReadMem<DWORD>(taskMgr + TASK_PRIMARY_PRIMARY * 4);
        if (!task) return false;

        // Primeiro campo de CTask e vtable, segundo e task type (offset 0x4)
        // Na verdade GetTaskType() e virtual, mas o tipo esta armazenado em 0x4 ou via vtable
        // Usar vtable: taskType = *(*(task) + 0x8) chamado como funcao
        // Forma segura: ler m_nTaskType offset 0x4
        int taskType = ReadMem<int>(task + 0x4);

        return (taskType == TASK_COMPLEX_KILL_PED_ON_FOOT         ||
                taskType == TASK_COMPLEX_FIGHT                     ||
                taskType == TASK_SIMPLE_FIGHT                      ||
                taskType == TASK_COMPLEX_KILL_PED_ON_FOOT_STEALTH ||
                taskType == TASK_SIMPLE_GUN_CTRL);
    }
    __except (EXCEPTION_EXECUTE_HANDLER) {
        return false;
    }
}

static DWORD GetPedTarget(DWORD ped)
{
    if (!ped) return 0;
    __try {
        DWORD target = ReadMem<DWORD>(ped + PED_TARGET_OFFSET);
        if (!target) return 0;

        // Verificar se e um ped (nType == 4)
        BYTE nType = ReadMem<BYTE>(target + 0x36); // CEntity::m_nType offset
        if (nType != ENTITY_TYPE_PED) return 0;

        return target;
    }
    __except (EXCEPTION_EXECUTE_HANDLER) {
        return 0;
    }
}

// ─────────────────────────────────────────────
//  FORCIAR COP A ATACAR - via funcao nativa SA
// ─────────────────────────────────────────────

// CTaskComplexKillPedOnFoot::CTaskComplexKillPedOnFoot
// Endereco SA 1.0 US: 0x624670
typedef void* (__thiscall* tKillPedTaskCtor)(void* task, DWORD* target, int weapon,
                                              int flags, bool run, bool flee, float range);
static tKillPedTaskCtor KillPedTaskCtor = (tKillPedTaskCtor)0x624670;

// CTaskManager::SetTask
// Endereco SA 1.0 US: 0x681AD0
typedef void (__thiscall* tTaskMgrSetTask)(void* taskMgr, void* task, int slot);
static tTaskMgrSetTask TaskMgrSetTask = (tTaskMgrSetTask)0x681AD0;

// operator new para alocar task (tamanho de CTaskComplexKillPedOnFoot = 0x28)
static void* AllocTask(size_t size)
{
    return HeapAlloc(GetProcessHeap(), 0, size);
}

static void ForceCopAttack(DWORD cop, DWORD target)
{
    if (!cop || !target) return;
    if (!IsPedValid(cop) || !IsPedValid(target)) return;

    __try {
        DWORD taskMgr = cop + PED_TASK_MGR_OFFSET;

        // Verificar se ja tem kill task ativa
        DWORD currentTask = ReadMem<DWORD>(taskMgr + TASK_PRIMARY_PRIMARY * 4);
        if (currentTask)
        {
            int currentType = ReadMem<int>(currentTask + 0x4);
            if (currentType == TASK_COMPLEX_KILL_PED_ON_FOOT) return;
        }

        // Alocar e construir nova task
        void* task = AllocTask(0x28);
        if (!task) return;

        KillPedTaskCtor(task, (DWORD*)target, -1, 0, true, true, 100.0f);
        TaskMgrSetTask((void*)taskMgr, task, TASK_PRIMARY_PRIMARY);

        Log("Policia [" + std::to_string(cop) + "] engajou [" + std::to_string(target) + "]");
    }
    __except (EXCEPTION_EXECUTE_HANDLER) {
        Log("Erro em ForceCopAttack");
    }
}

// ─────────────────────────────────────────────
//  LOGICA PRINCIPAL
// ─────────────────────────────────────────────

static void ProcessLocalViolence()
{
    DWORD player = GetPlayerPed();
    if (!player) return;

    CVector playerPos = GetPedPosition(player);
    int poolSize = GetPedPoolSize();
    if (poolSize <= 0) return;

    std::vector<DWORD> aggressors;
    std::vector<DWORD> cops;

    for (int i = 0; i < poolSize; i++)
    {
        DWORD ped = GetPedAt(i);
        if (!ped || ped == player) continue;
        if (!IsPedValid(ped)) continue;

        float dist = GetDist2DToPos(ped, playerPos.x, playerPos.y);

        if (IsCopPed(ped))
        {
            if (dist <= POLICE_ENGAGE_RADIUS)
                cops.push_back(ped);
            continue;
        }

        if (dist <= DETECTION_RADIUS && IsPedFighting(ped))
        {
            DWORD target = GetPedTarget(ped);
            if (target && target != player && !IsCopPed(target))
                aggressors.push_back(ped);
        }
    }

    if (aggressors.empty() || cops.empty()) return;

    Log("Violencia local: " + std::to_string(aggressors.size()) +
        " agressor(es), " + std::to_string(cops.size()) + " policia(s)");

    for (DWORD cop : cops)
    {
        // Encontrar agressor mais proximo deste cop
        DWORD closest = 0;
        float minDist  = 9999.0f;
        for (DWORD agg : aggressors)
        {
            float d = GetDist2D(cop, agg);
            if (d < minDist) { minDist = d; closest = agg; }
        }
        if (closest)
            ForceCopAttack(cop, closest);
    }
}

// ─────────────────────────────────────────────
//  THREAD PRINCIPAL DO PLUGIN
// ─────────────────────────────────────────────

static HANDLE g_hThread = nullptr;
static bool   g_bRunning = false;

static DWORD WINAPI PluginThread(LPVOID)
{
    // Aguardar o jogo carregar completamente
    Sleep(5000);

    Log("=== LocalReactivePolice iniciado ===");

    while (g_bRunning)
    {
        __try {
            ProcessLocalViolence();
        }
        __except (EXCEPTION_EXECUTE_HANDLER) {
            Log("Excecao no loop principal");
        }

        Sleep(CHECK_INTERVAL_MS);
    }

    return 0;
}

// ─────────────────────────────────────────────
//  ENTRY POINT DO ASI
// ─────────────────────────────────────────────

BOOL WINAPI DllMain(HINSTANCE hInstance, DWORD reason, LPVOID)
{
    if (reason == DLL_PROCESS_ATTACH)
    {
        DisableThreadLibraryCalls(hInstance);
        g_bRunning = true;
        g_hThread = CreateThread(nullptr, 0, PluginThread, nullptr, 0, nullptr);
    }
    else if (reason == DLL_PROCESS_DETACH)
    {
        g_bRunning = false;
        if (g_hThread)
        {
            WaitForSingleObject(g_hThread, 1000);
            CloseHandle(g_hThread);
        }
    }
    return TRUE;
}
