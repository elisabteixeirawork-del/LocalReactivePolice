/*
 * LocalReactivePolice.cpp - v5
 * Plugin GTA San Andreas - Policia Reativa Local
 * Modificacoes v5: detecao de combate mais robusta
 */

#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <cmath>
#include <fstream>
#include <ctime>
#include <string>

// ─────────────────────────────────────────────
//  ENDERECOS DE MEMORIA DO GTA SA 1.0 US
// ─────────────────────────────────────────────

#define PED_POOL_PTR                            0xB74490
#define PLAYER_PED_PTR                          0xB6F5F0
#define PED_HEALTH_OFFSET                       0x540
#define PED_TYPE_OFFSET                         0x528
#define PED_FLAGS_OFFSET                        0x46C
#define PED_TASK_MGR_OFFSET                     0x4A8
#define PED_TARGET_OFFSET                       0x564  // m_pTargetedObject
#define PED_EVENT_HANDLER_OFFSET                0x578  // CEventHandler
#define PED_WEAPON_SLOT_OFFSET                  0x5A0  // weapon slot actual
#define PED_WEAPON_TYPE_OFFSET                  0x5A4  // tipo da arma actual
#define PED_INAIR_FLAG                          (1 << 8)
#define PED_INWATER_FLAG                        (1 << 9)
#define PED_TYPE_COP                            6
#define ENTITY_TYPE_PED                         4

// Task types - principal slot
#define TASK_PRIMARY_PRIMARY                    2
#define TASK_PRIMARY_PHYSICAL_RESPONSE          3

// Tasks de combate conhecidas no GTA SA
#define TASK_COMPLEX_KILL_PED_ON_FOOT           167
#define TASK_COMPLEX_KILL_PED_ON_FOOT_STEALTH   168
#define TASK_COMPLEX_FIGHT                      134
#define TASK_SIMPLE_FIGHT                       140
#define TASK_SIMPLE_GUN_CTRL                    160
#define TASK_COMPLEX_GUN_FIGHT                  162  // combate com arma de fogo
#define TASK_COMPLEX_FLEE_PED                   147  // fuga (indica que esta a ser atacado)
#define TASK_SIMPLE_SHOOT_AT_PED                159  // disparar directamente
#define TASK_COMPLEX_ATTACK_PED                 130  // atacar ped
#define TASK_SIMPLE_PUNCH                       138  // soco
#define TASK_SIMPLE_BE_HIT                      136  // a ser atingido (indica combate activo)

// ─────────────────────────────────────────────
//  CONFIGURACOES
// ─────────────────────────────────────────────

static constexpr float DETECTION_RADIUS     = 70.0f;
static constexpr float POLICE_ENGAGE_RADIUS = 85.0f;
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
    if (ReadMem<BYTE>(byteArray + index) & 0x80) return 0;
    DWORD objects = ReadMem<DWORD>(pool + 0x00);
    if (!objects) return 0;
    return objects + (DWORD)(index * 0x7C4);
}

static DWORD GetPlayerPed()
{
    return ReadMem<DWORD>(PLAYER_PED_PTR);
}

// ─────────────────────────────────────────────
//  UTILIDADES DE PEDS
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
    return true;
}

static bool IsCopPed(DWORD ped)
{
    if (!ped) return false;
    if (IsBadReadPtr((void*)ped, PED_TYPE_OFFSET + 1)) return false;
    return ReadMem<BYTE>(ped + PED_TYPE_OFFSET) == PED_TYPE_COP;
}

// ─────────────────────────────────────────────
//  DETECAO DE COMBATE - VERSAO ROBUSTA v5
// ─────────────────────────────────────────────

/*
 * Obtem o tipo de task num slot especifico do CTaskManager.
 * CTaskManager tem 5 slots de tasks primarias (indices 0-4).
 * Cada slot e um ponteiro para CTask.
 * O tipo da task esta em offset 0x4 dentro de CTask.
 */
static int GetTaskType(DWORD ped, int slot)
{
    if (!ped) return -1;
    DWORD taskMgr = ped + PED_TASK_MGR_OFFSET;
    if (IsBadReadPtr((void*)taskMgr, (slot + 1) * 4)) return -1;
    DWORD task = ReadMem<DWORD>(taskMgr + slot * 4);
    if (!task) return -1;
    if (IsBadReadPtr((void*)task, 8)) return -1;
    return ReadMem<int>(task + 0x4);
}

/*
 * IsPedFighting v5 - detecao muito mais abrangente:
 * 1. Verifica multiplos slots de task (PRIMARY e PHYSICAL_RESPONSE)
 * 2. Inclui tasks de fuga (indica que esta a ser atacado)
 * 3. Verifica se o ped tem arma equipada E tem um alvo
 * 4. Verifica flag de "em combate" no CEventHandler
 */
static bool IsPedFighting(DWORD ped)
{
    if (!ped) return false;
    if (IsBadReadPtr((void*)ped, 0x600)) return false;

    // Lista alargada de tasks de combate
    static const int combatTasks[] = {
        TASK_COMPLEX_KILL_PED_ON_FOOT,
        TASK_COMPLEX_KILL_PED_ON_FOOT_STEALTH,
        TASK_COMPLEX_FIGHT,
        TASK_SIMPLE_FIGHT,
        TASK_SIMPLE_GUN_CTRL,
        TASK_COMPLEX_GUN_FIGHT,
        TASK_SIMPLE_SHOOT_AT_PED,
        TASK_COMPLEX_ATTACK_PED,
        TASK_SIMPLE_PUNCH,
        TASK_SIMPLE_BE_HIT,
        -1
    };

    // Verificar slots 0, 1, 2, 3 do task manager
    for (int slot = 0; slot <= 3; slot++)
    {
        int type = GetTaskType(ped, slot);
        if (type < 0) continue;

        for (int i = 0; combatTasks[i] != -1; i++)
        {
            if (type == combatTasks[i])
            {
                Log("Task " + std::to_string(type) + " detectada no slot " + std::to_string(slot));
                return true;
            }
        }
    }

    // Metodo alternativo: verificar se tem alvo e arma equipada
    // weapon slot actual != 0 significa que tem arma na mao
    if (!IsBadReadPtr((void*)(ped + PED_WEAPON_SLOT_OFFSET), 4))
    {
        DWORD weaponSlot = ReadMem<DWORD>(ped + PED_WEAPON_SLOT_OFFSET);
        if (weaponSlot > 0 && weaponSlot <= 12)
        {
            // Tem arma equipada - verificar se tem alvo valido
            if (!IsBadReadPtr((void*)(ped + PED_TARGET_OFFSET), 4))
            {
                DWORD target = ReadMem<DWORD>(ped + PED_TARGET_OFFSET);
                if (target && !IsBadReadPtr((void*)target, 4))
                {
                    Log("Arma equipada com alvo detectado (slot " + std::to_string(weaponSlot) + ")");
                    return true;
                }
            }
        }
    }

    return false;
}

/*
 * GetPedTarget v5 - mais robusta:
 * 1. Tenta offset primario (0x564)
 * 2. Tenta offset alternativo (0x55C) usado nalgumas versoes
 * 3. Verifica se o entity e realmente um ped
 */
static DWORD GetPedTarget(DWORD ped)
{
    if (!ped) return 0;

    // Tentar offsets conhecidos para m_pTargetedObject
    static const DWORD targetOffsets[] = { 0x564, 0x55C, 0x568, 0 };

    for (int i = 0; targetOffsets[i] != 0; i++)
    {
        DWORD offset = targetOffsets[i];
        if (IsBadReadPtr((void*)(ped + offset), 4)) continue;

        DWORD target = ReadMem<DWORD>(ped + offset);
        if (!target) continue;
        if (IsBadReadPtr((void*)target, 0x40)) continue;

        // Verificar entity type: offset 0x36 = m_nType
        BYTE nType = ReadMem<BYTE>(target + 0x36);
        if (nType == ENTITY_TYPE_PED)
        {
            Log("Alvo encontrado via offset 0x" + std::to_string(offset));
            return target;
        }
    }

    return 0;
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
//  LOGICA PRINCIPAL
// ─────────────────────────────────────────────

static void ProcessLocalViolence()
{
    DWORD player = GetPlayerPed();
    if (!player || IsBadReadPtr((void*)player, 0x600)) return;

    Vec3 pp = GetPedPos(player);
    int poolSize = GetPedPoolSize();
    if (poolSize <= 0 || poolSize > 140) return;

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
            {
                Log("Agressor registado (dist: " + std::to_string((int)dist) + "m)");
                aggressors[aggCount++] = ped;
            }
            else if (!target)
            {
                // Sem alvo confirmado mas esta em combate - registar mesmo assim
                Log("Agressor sem alvo confirmado registado");
                aggressors[aggCount++] = ped;
            }
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
    Log("=== LocalReactivePolice v5 iniciado ===");
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
