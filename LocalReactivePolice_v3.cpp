/*
 * LocalReactivePolice.cpp
 * Plugin GTA San Andreas - Policia Reativa Local
 * Versao sem plugin-sdk - apenas Windows API + enderecos de memoria GTA SA 1.0 US
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

#define PED_POOL_PTR                        0xB74490
#define PLAYER_PED_PTR                      0xB6F5F0
#define PED_HEALTH_OFFSET                   0x540
#define PED_TYPE_OFFSET                     0x528
#define PED_FLAGS_OFFSET                    0x46C
#define PED_TASK_MGR_OFFSET                 0x4A8
#define PED_TARGET_OFFSET                   0x564
#define PED_IN_VEHICLE_FLAG                 (1 << 8)
#define TASK_PRIMARY_PRIMARY                2
#define TASK_COMPLEX_KILL_PED_ON_FOOT       167
#define TASK_COMPLEX_FIGHT                  134
#define TASK_SIMPLE_FIGHT                   140
#define TASK_COMPLEX_KILL_PED_ON_FOOT_STEALTH 168
#define TASK_SIMPLE_GUN_CTRL                160
#define PED_TYPE_COP                        6
#define ENTITY_TYPE_PED                     4

// ─────────────────────────────────────────────
//  CONFIGURACOES
// ─────────────────────────────────────────────

static constexpr float DETECTION_RADIUS     = 65.0f;
static constexpr float POLICE_ENGAGE_RADIUS = 80.0f;
static constexpr int   CHECK_INTERVAL_MS    = 500;
static constexpr bool  ENABLE_LOG           = true;
static const char*     LOG_FILE             = "LocalReactivePolice.log";

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
static inline T ReadMem(DWORD addr)
{
    return *reinterpret_cast<T*>(addr);
}

// ─────────────────────────────────────────────
//  ESTRUTURA SIMPLES DE VECTOR
// ─────────────────────────────────────────────

struct Vec3 { float x, y, z; };

// ─────────────────────────────────────────────
//  POOL DE PEDS
// ─────────────────────────────────────────────

static int GetPedPoolSize()
{
    DWORD pool = ReadMem<DWORD>(PED_POOL_PTR);
    if (!pool) return 0;
    return ReadMem<int>(pool + 0x08);
}

static DWORD GetPedAt(int index)
{
    DWORD pool = ReadMem<DWORD>(PED_POOL_PTR);
    if (!pool) return 0;
    DWORD byteArray = ReadMem<DWORD>(pool + 0x04);
    if (!byteArray) return 0;
    BYTE flags = ReadMem<BYTE>(byteArray + index);
    if (flags & 0x80) return 0;
    DWORD objects = ReadMem<DWORD>(pool + 0x00);
    if (!objects) return 0;
    return objects + (DWORD)(index * 0x7C4);
}

static DWORD GetPlayerPed()
{
    return ReadMem<DWORD>(PLAYER_PED_PTR);
}

// ─────────────────────────────────────────────
//  UTILIDADES DE PEDS - sem __try para evitar C2712
// ─────────────────────────────────────────────

static Vec3 GetPedPos(DWORD ped)
{
    Vec3 v = {0,0,0};
    if (!ped) return v;
    v.x = ReadMem<float>(ped + 0x44);
    v.y = ReadMem<float>(ped + 0x48);
    v.z = ReadMem<float>(ped + 0x4C);
    return v;
}

static float Dist2D(DWORD a, DWORD b)
{
    if (!a || !b) return 9999.f;
    Vec3 pa = GetPedPos(a), pb = GetPedPos(b);
    float dx = pa.x - pb.x, dy = pa.y - pb.y;
    return std::sqrt(dx*dx + dy*dy);
}

static float Dist2DToXY(DWORD ped, float px, float py)
{
    if (!ped) return 9999.f;
    Vec3 p = GetPedPos(ped);
    float dx = p.x - px, dy = p.y - py;
    return std::sqrt(dx*dx + dy*dy);
}

static bool IsPedValid(DWORD ped)
{
    if (!ped) return false;
    if (IsBadReadPtr((void*)ped, 0x600)) return false;
    float hp = ReadMem<float>(ped + PED_HEALTH_OFFSET);
    if (hp <= 0.f) return false;
    DWORD fl = ReadMem<DWORD>(ped + PED_FLAGS_OFFSET);
    if (fl & PED_IN_VEHICLE_FLAG) return false;
    return true;
}

static bool IsCopPed(DWORD ped)
{
    if (!ped) return false;
    if (IsBadReadPtr((void*)ped, PED_TYPE_OFFSET + 1)) return false;
    return ReadMem<BYTE>(ped + PED_TYPE_OFFSET) == PED_TYPE_COP;
}

static bool IsPedFighting(DWORD ped)
{
    if (!ped) return false;
    DWORD taskMgr = ped + PED_TASK_MGR_OFFSET;
    if (IsBadReadPtr((void*)taskMgr, 20)) return false;
    DWORD task = ReadMem<DWORD>(taskMgr + TASK_PRIMARY_PRIMARY * 4);
    if (!task) return false;
    if (IsBadReadPtr((void*)task, 8)) return false;
    int type = ReadMem<int>(task + 0x4);
    return (type == TASK_COMPLEX_KILL_PED_ON_FOOT          ||
            type == TASK_COMPLEX_FIGHT                      ||
            type == TASK_SIMPLE_FIGHT                       ||
            type == TASK_COMPLEX_KILL_PED_ON_FOOT_STEALTH  ||
            type == TASK_SIMPLE_GUN_CTRL);
}

static DWORD GetPedTarget(DWORD ped)
{
    if (!ped) return 0;
    if (IsBadReadPtr((void*)(ped + PED_TARGET_OFFSET), 4)) return 0;
    DWORD target = ReadMem<DWORD>(ped + PED_TARGET_OFFSET);
    if (!target) return 0;
    if (IsBadReadPtr((void*)(target + 0x36), 1)) return 0;
    BYTE nType = ReadMem<BYTE>(target + 0x36);
    return (nType == ENTITY_TYPE_PED) ? target : 0;
}

// ─────────────────────────────────────────────
//  FORCIAR COP A ATACAR
// ─────────────────────────────────────────────

typedef void* (__thiscall* tKillTaskCtor)(void*, DWORD*, int, int, bool, bool, float);
typedef void  (__thiscall* tSetTask)(void*, void*, int);

static tKillTaskCtor KillTaskCtor = (tKillTaskCtor)0x624670;
static tSetTask      SetTask      = (tSetTask)0x681AD0;

static void ForceCopAttack(DWORD cop, DWORD target)
{
    if (!IsPedValid(cop) || !IsPedValid(target)) return;

    DWORD taskMgr = cop + PED_TASK_MGR_OFFSET;
    if (IsBadReadPtr((void*)taskMgr, 20)) return;

    DWORD cur = ReadMem<DWORD>(taskMgr + TASK_PRIMARY_PRIMARY * 4);
    if (cur && !IsBadReadPtr((void*)cur, 8))
    {
        if (ReadMem<int>(cur + 0x4) == TASK_COMPLEX_KILL_PED_ON_FOOT)
            return;
    }

    void* task = HeapAlloc(GetProcessHeap(), 0, 0x28);
    if (!task) return;

    KillTaskCtor(task, (DWORD*)target, -1, 0, true, true, 100.f);
    SetTask((void*)taskMgr, task, TASK_PRIMARY_PRIMARY);
    Log("Policia engajou alvo");
}

// ─────────────────────────────────────────────
//  LOGICA PRINCIPAL - sem __try (usa IsBadReadPtr)
// ─────────────────────────────────────────────

static void ProcessLocalViolence()
{
    DWORD player = GetPlayerPed();
    if (!player || IsBadReadPtr((void*)player, 0x600)) return;

    Vec3 pp = GetPedPos(player);
    int poolSize = GetPedPoolSize();
    if (poolSize <= 0 || poolSize > 140) return;

    // Arrays estaticos para evitar std::vector com __try
    static DWORD aggressors[64];
    static DWORD cops[32];
    int aggCount = 0, copCount = 0;

    for (int i = 0; i < poolSize && aggCount < 64 && copCount < 32; i++)
    {
        DWORD ped = GetPedAt(i);
        if (!ped || ped == player) continue;
        if (!IsPedValid(ped)) continue;

        float dist = Dist2DToXY(ped, pp.x, pp.y);

        if (IsCopPed(ped))
        {
            if (dist <= POLICE_ENGAGE_RADIUS)
                cops[copCount++] = ped;
            continue;
        }

        if (dist <= DETECTION_RADIUS && IsPedFighting(ped))
        {
            DWORD target = GetPedTarget(ped);
            if (target && target != player && !IsCopPed(target))
                aggressors[aggCount++] = ped;
        }
    }

    if (aggCount == 0 || copCount == 0) return;

    Log("Violencia local: " + std::to_string(aggCount) +
        " agressor(es), " + std::to_string(copCount) + " policia(s)");

    for (int c = 0; c < copCount; c++)
    {
        DWORD closest = 0;
        float minDist = 9999.f;
        for (int a = 0; a < aggCount; a++)
        {
            float d = Dist2D(cops[c], aggressors[a]);
            if (d < minDist) { minDist = d; closest = aggressors[a]; }
        }
        if (closest) ForceCopAttack(cops[c], closest);
    }
}

// ─────────────────────────────────────────────
//  THREAD E ENTRY POINT
// ─────────────────────────────────────────────

static HANDLE g_hThread = nullptr;
static bool   g_bRunning = false;

static DWORD WINAPI PluginThread(LPVOID)
{
    Sleep(5000);
    Log("=== LocalReactivePolice iniciado ===");
    while (g_bRunning)
    {
        ProcessLocalViolence();
        Sleep(CHECK_INTERVAL_MS);
    }
    return 0;
}

BOOL WINAPI DllMain(HINSTANCE hInst, DWORD reason, LPVOID)
{
    if (reason == DLL_PROCESS_ATTACH)
    {
        DisableThreadLibraryCalls(hInst);
        g_bRunning = true;
        g_hThread = CreateThread(nullptr, 0, PluginThread, nullptr, 0, nullptr);
    }
    else if (reason == DLL_PROCESS_DETACH)
    {
        g_bRunning = false;
        if (g_hThread) { WaitForSingleObject(g_hThread, 1000); CloseHandle(g_hThread); }
    }
    return TRUE;
}
