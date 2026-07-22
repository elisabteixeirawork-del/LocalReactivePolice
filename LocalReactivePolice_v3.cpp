/*
 * LocalReactivePolice.cpp - v8
 * Plugin GTA San Andreas - Policia Reativa Local
 *
 * Correcoes v8 (baseadas em GTAMods Wiki documentado):
 *   1. GetPedPos(): corrigido para double dereference
 *      *(ped + 0x14) + 0x30 em vez de ped + 0x44 directo
 *   2. ENTITY_TYPE_PED: corrigido de 4 para 3
 *   3. GetPedTarget(): usa 0x79C (Targetted CPed, documentado)
 *      em vez dos offsets incertos anteriores
 *
 * Arquitectura: baseada no Police Assistance (CLEO)
 *   - offset 0x764 = ultimo ped que causou dano (documentado, valido para qualquer CPed)
 *   - generalizado para qualquer ped, nao apenas CJ
 */

#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <cmath>
#include <fstream>
#include <ctime>
#include <string>

// ─────────────────────────────────────────────
//  ENDERECOS DE MEMORIA DO GTA SA 1.0 US
//  Fonte: GTAMods Wiki - Memory Addresses (SA)
//  https://gtamods.com/wiki/Memory_Addresses_(SA)
// ─────────────────────────────────────────────

#define PED_POOL_PTR            0xB74490   // Pointer to ped pool usage information
#define PLAYER_PED_PTR          0xB6F5F0   // Player pointer (CPed)

// CPed offsets (documentados GTAMods Wiki)
#define PED_MATRIX_PTR          0x14       // Pointer to XYZ position structure
#define PED_MATRIX_POS          0x30       // [CVector] Position dentro da matrix
// GetPedPos(): pos = *(ped + 0x14) + 0x30  (double dereference)

#define PED_HEALTH_OFFSET       0x540      // [float] Health
#define PED_TYPE_OFFSET         0x528      // [byte] PedType
#define PED_FLAGS_OFFSET        0x46C      // [byte] flags (0=air/water, 1=car, 3=foot)
#define PED_IN_VEHICLE_VAL      1          // valor para "in car" em 0x46C

#define PED_DAMAGER_OFFSET      0x764      // [dword] Pointer to the ped that damaged you
#define PED_TARGET_OFFSET       0x79C      // [dword] Targetted CPed
#define PED_WEAPON_DMG          0x760      // [dword] Weapon you were damaged with

// eEntityType (documentado GTAMods Wiki)
#define ENTITY_TYPE_PED         3          // ENTITY_TYPE_PED = 3 (nao 4!)
#define ENTITY_TYPE_OFFSET      0x36       // [byte] dentro de CEntity

// ePedType
#define PED_TYPE_COP            6

// Task slots e tipos
#define TASK_MGR_OFFSET         0x4A8      // CTaskManager inline
#define TASK_SLOT_PRIMARY       2          // slot principal
#define TASK_COMPLEX_KILL_PED   167        // CTaskComplexKillPedOnFoot

// ─────────────────────────────────────────────
//  CONFIGURACOES
// ─────────────────────────────────────────────

static constexpr float DETECTION_RADIUS     = 70.0f;
static constexpr float POLICE_ENGAGE_RADIUS = 85.0f;
static constexpr int   CHECK_INTERVAL_MS    = 500;
static constexpr int   COP_COOLDOWN_MS      = 12000;
static constexpr float HP_LOSS_THRESHOLD    = 1.0f;
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
//  HISTORICO DE SAUDE
// ─────────────────────────────────────────────

static float g_prevHealth[140] = {};
static bool  g_healthInit      = false;

// ─────────────────────────────────────────────
//  COOLDOWN POR COP
// ─────────────────────────────────────────────

#define MAX_COPS_TRACKED 16
static DWORD g_copAddr[MAX_COPS_TRACKED]     = {};
static DWORD g_copLastTask[MAX_COPS_TRACKED] = {};

static bool CopIsOnCooldown(DWORD cop)
{
    DWORD now = GetTickCount();
    for (int i = 0; i < MAX_COPS_TRACKED; i++)
        if (g_copAddr[i] == cop)
            return (now - g_copLastTask[i]) < (DWORD)COP_COOLDOWN_MS;
    return false;
}

static void SetCopCooldown(DWORD cop)
{
    DWORD now = GetTickCount();
    for (int i = 0; i < MAX_COPS_TRACKED; i++)
    {
        if (g_copAddr[i] == cop) { g_copLastTask[i] = now; return; }
    }
    int slot = 0;
    DWORD oldest = g_copLastTask[0];
    for (int i = 1; i < MAX_COPS_TRACKED; i++)
    {
        if (g_copAddr[i] == 0) { slot = i; break; }
        if (g_copLastTask[i] < oldest) { oldest = g_copLastTask[i]; slot = i; }
    }
    g_copAddr[slot]     = cop;
    g_copLastTask[slot] = now;
}

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
//  POSICAO DO PED - CORRIGIDA v8
//
//  GTAMods Wiki: CPed +0x14 = Pointer to XYZ position structure
//                (CPed+0x14) +0x30 = [CVector] Position
//
//  E um double dereference:
//    1. Ler o ponteiro em (ped + 0x14)
//    2. Ler a posicao em (ponteiro + 0x30)
// ─────────────────────────────────────────────

static Vec3 GetPedPos(DWORD ped)
{
    Vec3 v = {0,0,0};
    if (!ped) return v;
    if (IsBadReadPtr((void*)(ped + PED_MATRIX_PTR), 4)) return v;

    // Passo 1: ler o ponteiro para a estrutura de posicao
    DWORD matrixPtr = ReadMem<DWORD>(ped + PED_MATRIX_PTR);
    if (!matrixPtr) return v;
    if (IsBadReadPtr((void*)(matrixPtr + PED_MATRIX_POS), 12)) return v;

    // Passo 2: ler a posicao dentro da estrutura
    v.x = ReadMem<float>(matrixPtr + PED_MATRIX_POS + 0);
    v.y = ReadMem<float>(matrixPtr + PED_MATRIX_POS + 4);
    v.z = ReadMem<float>(matrixPtr + PED_MATRIX_POS + 8);
    return v;
}

static float Dist2D(DWORD a, DWORD b)
{
    Vec3 pa = GetPedPos(a), pb = GetPedPos(b);
    float dx = pa.x - pb.x, dy = pa.y - pb.y;
    return std::sqrt(dx*dx + dy*dy);
}

static float Dist2DToXY(DWORD ped, float px, float py)
{
    Vec3 p = GetPedPos(ped);
    float dx = p.x - px, dy = p.y - py;
    return std::sqrt(dx*dx + dy*dy);
}

// ─────────────────────────────────────────────
//  VALIDACOES DE PED
// ─────────────────────────────────────────────

static bool IsPedValid(DWORD ped)
{
    if (!ped) return false;
    if (IsBadReadPtr((void*)ped, 0x600)) return false;
    return ReadMem<float>(ped + PED_HEALTH_OFFSET) > 0.f;
}

static bool IsCopPed(DWORD ped)
{
    if (!ped) return false;
    if (IsBadReadPtr((void*)(ped + PED_TYPE_OFFSET), 1)) return false;
    return ReadMem<BYTE>(ped + PED_TYPE_OFFSET) == PED_TYPE_COP;
}

static bool IsInVehicle(DWORD ped)
{
    if (!ped) return true;
    if (IsBadReadPtr((void*)(ped + PED_FLAGS_OFFSET), 1)) return true;
    // GTAMods: 0x46C: 1 = in car, 3 = on foot
    return ReadMem<BYTE>(ped + PED_FLAGS_OFFSET) == PED_IN_VEHICLE_VAL;
}

// ─────────────────────────────────────────────
//  VERIFICAR SE ENTITY E PED - CORRIGIDA v8
//  ENTITY_TYPE_PED = 3 (nao 4)
// ─────────────────────────────────────────────

static bool IsEntityAPed(DWORD entity)
{
    if (!entity) return false;
    if (IsBadReadPtr((void*)(entity + ENTITY_TYPE_OFFSET), 1)) return false;
    return ReadMem<BYTE>(entity + ENTITY_TYPE_OFFSET) == ENTITY_TYPE_PED;
}

// ─────────────────────────────────────────────
//  SAUDE A DIMINUIR (backup)
// ─────────────────────────────────────────────

static bool IsPedLosingHealth(DWORD ped, int index)
{
    if (!ped || index < 0 || index >= 140) return false;
    if (IsBadReadPtr((void*)(ped + PED_HEALTH_OFFSET), 4)) return false;

    float cur = ReadMem<float>(ped + PED_HEALTH_OFFSET);
    if (!g_healthInit) { g_prevHealth[index] = cur; return false; }

    float prev = g_prevHealth[index];
    g_prevHealth[index] = cur;
    return (prev > 0.f && cur > 0.f && (prev - cur) > HP_LOSS_THRESHOLD);
}

// ─────────────────────────────────────────────
//  OBTER DAMAGER - METODO PRINCIPAL (Police Assistance)
//  CPed +0x764 = Pointer to the ped that damaged you
//  Documentado GTAMods Wiki, valido para qualquer CPed
// ─────────────────────────────────────────────

static DWORD GetPedDamager(DWORD ped)
{
    if (!ped) return 0;
    if (IsBadReadPtr((void*)(ped + PED_DAMAGER_OFFSET), 4)) return 0;

    DWORD damager = ReadMem<DWORD>(ped + PED_DAMAGER_OFFSET);
    if (!damager) return 0;
    if (!IsPedValid(damager)) return 0;
    if (!IsEntityAPed(damager)) return 0;

    return damager;
}

// ─────────────────────────────────────────────
//  OBTER ALVO ACTIVO - CORRIGIDO v8
//  CPed +0x79C = Targetted CPed (documentado GTAMods Wiki)
// ─────────────────────────────────────────────

static DWORD GetPedTarget(DWORD ped)
{
    if (!ped) return 0;
    if (IsBadReadPtr((void*)(ped + PED_TARGET_OFFSET), 4)) return 0;

    DWORD target = ReadMem<DWORD>(ped + PED_TARGET_OFFSET);
    if (!target) return 0;
    if (!IsPedValid(target)) return 0;
    if (!IsEntityAPed(target)) return 0;

    return target;
}

// ─────────────────────────────────────────────
//  ORDENAR COP A ATACAR
// ─────────────────────────────────────────────

typedef void* (__thiscall* tKillTaskCtor)(void*, DWORD*, int, int, bool, bool, float);
typedef void  (__thiscall* tSetTask)(void*, void*, int);

static tKillTaskCtor KillTaskCtor = (tKillTaskCtor)0x624670;
static tSetTask      SetTask      = (tSetTask)0x681AD0;

static bool OrderCopAttack(DWORD cop, DWORD target)
{
    if (!IsPedValid(cop) || !IsPedValid(target)) return false;
    if (cop == target) return false;
    if (IsInVehicle(cop)) return false;
    if (CopIsOnCooldown(cop)) return false;

    DWORD taskMgr = cop + TASK_MGR_OFFSET;
    if (IsBadReadPtr((void*)taskMgr, 20)) return false;

    // Nao interromper se ja esta a atacar
    DWORD curTask = ReadMem<DWORD>(taskMgr + TASK_SLOT_PRIMARY * 4);
    if (curTask && !IsBadReadPtr((void*)curTask, 8))
        if (ReadMem<int>(curTask + 0x4) == TASK_COMPLEX_KILL_PED) return false;

    void* task = HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, 0x28);
    if (!task) return false;

    KillTaskCtor(task, (DWORD*)target, -1, 0, true, true, 100.f);
    SetTask((void*)taskMgr, task, TASK_SLOT_PRIMARY);
    SetCopCooldown(cop);

    Vec3 cp = GetPedPos(cop);
    Vec3 tp = GetPedPos(target);
    Log("Cop [" + std::to_string((int)cp.x) + "," + std::to_string((int)cp.y) +
        "] -> alvo [" + std::to_string((int)tp.x) + "," + std::to_string((int)tp.y) + "]");
    Log("OrderCopAttack: OK");
    return true;
}

// ─────────────────────────────────────────────
//  LOGICA PRINCIPAL
// ─────────────────────────────────────────────

static void ProcessLocalViolence()
{
    DWORD player = GetPlayerPed();
    if (!player || IsBadReadPtr((void*)player, 0x600)) return;

    Vec3 pp = GetPedPos(player);

    // Verificar que a posicao do jogador e valida
    if (pp.x == 0.f && pp.y == 0.f) return;

    int poolSize = GetPedPoolSize();
    if (poolSize <= 0 || poolSize > 140) return;

    static DWORD aggressors[32];
    static DWORD cops[16];
    int aggCount = 0, copCount = 0;

    for (int i = 0; i < poolSize && aggCount < 32 && copCount < 16; i++)
    {
        DWORD ped = GetPedAt(i);
        if (!ped || ped == player) continue;
        if (!IsPedValid(ped)) continue;
        if (IsInVehicle(ped)) continue;

        float dist = Dist2DToXY(ped, pp.x, pp.y);

        // Recolher policias
        if (IsCopPed(ped))
        {
            if (dist <= POLICE_ENGAGE_RADIUS)
                cops[copCount++] = ped;
            continue;
        }

        if (dist > DETECTION_RADIUS) continue;

        // ─────────────────────────────────────────────
        // METODO A: damager de outro ped
        // Este ped foi atacado recentemente?
        // Se sim, quem o atacou e o agressor confirmado.
        // ─────────────────────────────────────────────
        DWORD damager = GetPedDamager(ped);
        if (damager && damager != player && !IsCopPed(damager))
        {
            float dmgDist = Dist2DToXY(damager, pp.x, pp.y);
            if (dmgDist <= DETECTION_RADIUS)
            {
                bool found = false;
                for (int k = 0; k < aggCount; k++)
                    if (aggressors[k] == damager) { found = true; break; }
                if (!found)
                {
                    aggressors[aggCount++] = damager;
                    Vec3 dp = GetPedPos(damager);
                    Log("Agressor via damager: [" +
                        std::to_string((int)dp.x) + "," +
                        std::to_string((int)dp.y) + "] dist=" +
                        std::to_string((int)dmgDist) + "m");
                }
            }
        }

        // ─────────────────────────────────────────────
        // METODO B: alvo activo (0x79C)
        // Este ped esta a visar activamente outro ped nao-policia?
        // ─────────────────────────────────────────────
        DWORD target = GetPedTarget(ped);
        if (target && target != player && !IsCopPed(target))
        {
            bool found = false;
            for (int k = 0; k < aggCount; k++)
                if (aggressors[k] == ped) { found = true; break; }
            if (!found)
            {
                aggressors[aggCount++] = ped;
                Vec3 ap = GetPedPos(ped);
                Log("Agressor via target activo: [" +
                    std::to_string((int)ap.x) + "," +
                    std::to_string((int)ap.y) + "] dist=" +
                    std::to_string((int)dist) + "m");
            }
        }

        // ─────────────────────────────────────────────
        // METODO C: saude a diminuir (backup)
        // ─────────────────────────────────────────────
        bool losingHP = IsPedLosingHealth(ped, i);
        if (losingHP)
        {
            // Tentar obter o damager primeiro
            DWORD dmg2 = GetPedDamager(ped);
            DWORD toAdd = (dmg2 && dmg2 != player && !IsCopPed(dmg2)) ? dmg2 : ped;

            bool found = false;
            for (int k = 0; k < aggCount; k++)
                if (aggressors[k] == toAdd) { found = true; break; }
            if (!found && aggCount < 32)
            {
                aggressors[aggCount++] = toAdd;
                Log("Participante via perda de saude");
            }
        }
    }

    g_healthInit = true;

    if (aggCount == 0 || copCount == 0) return;

    Log("Violencia detectada: " + std::to_string(aggCount) +
        " agressor(es), " + std::to_string(copCount) + " policia(s)");

    int tasked = 0;
    for (int c = 0; c < copCount; c++)
    {
        DWORD cop = cops[c];
        DWORD closest = 0;
        float minDist = 9999.f;
        for (int a = 0; a < aggCount; a++)
        {
            float d = Dist2D(cop, aggressors[a]);
            if (d < minDist) { minDist = d; closest = aggressors[a]; }
        }
        if (closest)
        {
            Log("Destacar cop (dist: " + std::to_string((int)minDist) + "m)");
            if (OrderCopAttack(cop, closest))
                tasked++;
        }
    }

    if (tasked > 0)
        Log("Cops destacados: " + std::to_string(tasked));
}

// ─────────────────────────────────────────────
//  THREAD E ENTRY POINT
// ─────────────────────────────────────────────

static HANDLE g_hThread = nullptr;
static bool   g_bRunning = false;

static DWORD WINAPI PluginThread(LPVOID)
{
    Sleep(5000);
    Log("=== LocalReactivePolice v8 iniciado ===");
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
        if (g_hThread)
        {
            WaitForSingleObject(g_hThread, 1000);
            CloseHandle(g_hThread);
        }
    }
    return TRUE;
}
