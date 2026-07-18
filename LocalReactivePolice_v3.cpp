/*
 * LocalReactivePolice.cpp - v7
 * Plugin GTA San Andreas - Policia Reativa Local
 *
 * Arquitectura baseada no Police Assistance (CLEO) - provado funcionar.
 * Generalizado: observa qualquer ped, nao apenas o CJ.
 *
 * Filosofia:
 *   1. Para cada ped proximo do jogador:
 *      - ler offset 0x764 (m_pDamager: ultimo ped que causou dano)
 *      - se existir um atacante valido e nao-policia -> agressor confirmado
 *   2. Encontrar policia proximo
 *   3. Ordenar ataque via AS_actor kill_actor (opcode 05E2 nativo)
 *   4. Aguardar fim do combate
 *   5. Devolver cop ao comportamento normal
 *
 * Componentes reutilizados da v6.1:
 *   - DllMain, thread, logging
 *   - Pool de peds, validacoes, distancias
 *   - Cooldown por cop
 *   - IsPedLosingHealth (backup adicional)
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

#define PED_POOL_PTR            0xB74490   // CPools::ms_pPedPool
#define PLAYER_PED_PTR          0xB6F5F0   // FindPlayerPed cache

// Offsets dentro de CPed
#define PED_POS_X               0x44       // CEntity::GetPosition().x
#define PED_POS_Y               0x48
#define PED_POS_Z               0x4C
#define PED_HEALTH_OFFSET       0x540      // float m_fHealth
#define PED_TYPE_OFFSET         0x528      // BYTE m_nPedType
#define PED_FLAGS_OFFSET        0x46C      // DWORD flags
#define PED_IN_VEHICLE_FLAG     (1 << 8)
#define PED_TYPE_COP            6

// Offset critico: m_pDamager
// Descoberto pela analise do Police Assistance CLEO:
//   get_ped_pointer + 1892 (decimal) = 0x764
// Este offset aponta para o ultimo CPed que causou dano a este ped.
// E o metodo mais fiavel para detectar agressao activa.
#define PED_DAMAGER_OFFSET      0x764      // CPed* m_pLastDamager

// Entity type
#define ENTITY_TYPE_PED         4
#define ENTITY_TYPE_OFFSET      0x36       // BYTE dentro de CEntity

// Enderecos de funcoes nativas do GTA SA 1.0 US
// CTaskComplexKillPedOnFoot::ctor
#define ADDR_KILL_TASK_CTOR     0x624670
// CTaskManager::SetTask
#define ADDR_SET_TASK           0x681AD0
// CPed::ClearTasks (equivalente a clear_actor task)
#define ADDR_CLEAR_TASKS        0x61A0A0
// CPed::RestorePreviousObjective (equivalente a walk_around_ped_path)
#define ADDR_RESTORE_PATROL     0x601640

// ─────────────────────────────────────────────
//  CONFIGURACOES
// ─────────────────────────────────────────────

static constexpr float DETECTION_RADIUS     = 70.0f;   // raio de observacao
static constexpr float POLICE_ENGAGE_RADIUS = 85.0f;   // raio de busca de policia
static constexpr int   CHECK_INTERVAL_MS    = 500;     // intervalo de verificacao
static constexpr int   COP_COOLDOWN_MS      = 12000;   // cooldown por cop (12s)
static constexpr float HP_LOSS_THRESHOLD    = 1.0f;    // perda minima de HP
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
//  HISTORICO DE SAUDE (backup de deteccao)
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
    int oldest = 0;
    DWORD oldestTime = g_copLastTask[0];
    for (int i = 1; i < MAX_COPS_TRACKED; i++)
    {
        if (g_copAddr[i] == 0) { oldest = i; break; }
        if (g_copLastTask[i] < oldestTime) { oldest = i; oldestTime = g_copLastTask[i]; }
    }
    g_copAddr[oldest]     = cop;
    g_copLastTask[oldest] = now;
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
//  UTILIDADES
// ─────────────────────────────────────────────

static Vec3 GetPedPos(DWORD ped)
{
    Vec3 v = {0,0,0};
    if (!ped || IsBadReadPtr((void*)(ped + PED_POS_X), 12)) return v;
    v.x = ReadMem<float>(ped + PED_POS_X);
    v.y = ReadMem<float>(ped + PED_POS_Y);
    v.z = ReadMem<float>(ped + PED_POS_Z);
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

static bool IsPedValid(DWORD ped)
{
    if (!ped || IsBadReadPtr((void*)ped, 0x600)) return false;
    return ReadMem<float>(ped + PED_HEALTH_OFFSET) > 0.f;
}

static bool IsCopPed(DWORD ped)
{
    if (!ped || IsBadReadPtr((void*)(ped + PED_TYPE_OFFSET), 1)) return false;
    return ReadMem<BYTE>(ped + PED_TYPE_OFFSET) == PED_TYPE_COP;
}

static bool IsInVehicle(DWORD ped)
{
    if (!ped || IsBadReadPtr((void*)(ped + PED_FLAGS_OFFSET), 4)) return true;
    return (ReadMem<DWORD>(ped + PED_FLAGS_OFFSET) & PED_IN_VEHICLE_FLAG) != 0;
}

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
//  DETECAO DE AGRESSOR - METODO DO POLICE ASSISTANCE
//
//  Ler PED_DAMAGER_OFFSET (0x764) dentro do ped vitima.
//  Este campo e actualizado pelo proprio motor do GTA SA
//  sempre que o ped sofre dano de outro ped.
//  E exactamente o mesmo metodo que o Police Assistance
//  usa para identificar quem atacou o CJ.
//
//  Aqui generalizamos: para qualquer ped proximo,
//  verificamos se tem um damager valido e nao-policia.
// ─────────────────────────────────────────────

static DWORD GetPedDamager(DWORD ped)
{
    if (!ped) return 0;
    if (IsBadReadPtr((void*)(ped + PED_DAMAGER_OFFSET), 4)) return 0;

    DWORD damager = ReadMem<DWORD>(ped + PED_DAMAGER_OFFSET);
    if (!damager) return 0;
    if (IsBadReadPtr((void*)damager, 0x600)) return 0;

    // Verificar que e um ped (entity type == 4)
    if (IsBadReadPtr((void*)(damager + ENTITY_TYPE_OFFSET), 1)) return 0;
    BYTE nType = ReadMem<BYTE>(damager + ENTITY_TYPE_OFFSET);
    if (nType != ENTITY_TYPE_PED) return 0;

    // Verificar que esta vivo
    if (!IsPedValid(damager)) return 0;

    return damager;
}

// ─────────────────────────────────────────────
//  ORDENAR COP A ATACAR
//  Usa CTaskComplexKillPedOnFoot via ctor + SetTask
//  (equivalente ao opcode 05E2 do CLEO)
// ─────────────────────────────────────────────

typedef void* (__thiscall* tKillTaskCtor)(void*, DWORD*, int, int, bool, bool, float);
typedef void  (__thiscall* tSetTask)(void*, void*, int);
typedef void  (__thiscall* tClearTasks)(void*, bool);

static tKillTaskCtor KillTaskCtor = (tKillTaskCtor)ADDR_KILL_TASK_CTOR;
static tSetTask      SetTask      = (tSetTask)ADDR_SET_TASK;
static tClearTasks   ClearTasks   = (tClearTasks)ADDR_CLEAR_TASKS;

static bool OrderCopAttack(DWORD cop, DWORD target)
{
    if (!IsPedValid(cop) || !IsPedValid(target)) return false;
    if (cop == target) return false;
    if (IsInVehicle(cop))
    {
        Log("Cop em viatura, ignorar");
        return false;
    }
    if (CopIsOnCooldown(cop))
    {
        return false;
    }

    DWORD taskMgr = cop + 0x4A8;  // PED_TASK_MGR_OFFSET
    if (IsBadReadPtr((void*)taskMgr, 20)) return false;

    // Nao interromper se ja esta a atacar
    DWORD curTask = ReadMem<DWORD>(taskMgr + 2 * 4);
    if (curTask && !IsBadReadPtr((void*)curTask, 8))
    {
        int curType = ReadMem<int>(curTask + 0x4);
        if (curType == 167 || curType == 134 || curType == 162)
        {
            Log("Cop ja em combate, manter task");
            return false;
        }
    }

    void* task = HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, 0x28);
    if (!task) return false;

    KillTaskCtor(task, (DWORD*)target, -1, 0, true, true, 100.f);
    SetTask((void*)taskMgr, task, 2);
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
//
//  Para cada ped proximo do jogador (nao-policia):
//    A) Verificar PED_DAMAGER_OFFSET -> ha agressor confirmado?
//    B) Backup: ped esta a perder HP? (alguem esta a atacar)
//
//  Se detectado -> encontrar policia proximo -> ordenar ataque.
// ─────────────────────────────────────────────

static void ProcessLocalViolence()
{
    DWORD player = GetPlayerPed();
    if (!player || IsBadReadPtr((void*)player, 0x600)) return;

    Vec3 pp = GetPedPos(player);
    int poolSize = GetPedPoolSize();
    if (poolSize <= 0 || poolSize > 140) return;

    // Listas de peds a processar
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

        // Recolher policias proximos
        if (IsCopPed(ped))
        {
            if (dist <= POLICE_ENGAGE_RADIUS)
                cops[copCount++] = ped;
            continue;
        }

        // Verificar ped nao-policia dentro do raio
        if (dist > DETECTION_RADIUS) continue;

        // -----------------------------------------
        // METODO A: PED_DAMAGER_OFFSET (Police Assistance)
        // Quem atacou este ped recentemente?
        // -----------------------------------------
        DWORD damager = GetPedDamager(ped);

        if (damager && damager != player && !IsCopPed(damager))
        {
            // Confirmar que o damager esta proximo
            float damagerDist = Dist2DToXY(damager, pp.x, pp.y);
            if (damagerDist <= DETECTION_RADIUS)
            {
                // Registar o AGRESSOR (quem causou o dano), nao a vitima
                bool found = false;
                for (int k = 0; k < aggCount; k++)
                    if (aggressors[k] == damager) { found = true; break; }
                if (!found)
                {
                    aggressors[aggCount++] = damager;
                    Log("Agressor via damager (dist vitima: " +
                        std::to_string((int)dist) + "m)");
                }
            }
        }

        // -----------------------------------------
        // METODO B: Saude a diminuir (backup)
        // Se este ped esta a perder HP, alguem o atacou.
        // Registar o proprio ped como participante de combate.
        // -----------------------------------------
        bool losingHP = IsPedLosingHealth(ped, i);
        if (losingHP)
        {
            // Tentar usar o damager se existir
            DWORD dmg2 = GetPedDamager(ped);
            if (dmg2 && dmg2 != player && !IsCopPed(dmg2))
            {
                bool found = false;
                for (int k = 0; k < aggCount; k++)
                    if (aggressors[k] == dmg2) { found = true; break; }
                if (!found && aggCount < 32)
                {
                    aggressors[aggCount++] = dmg2;
                    Log("Agressor via saude+damager");
                }
            }
            else
            {
                // Sem damager identificado - registar a vitima
                // (policia vai para o local do combate de qualquer forma)
                bool found = false;
                for (int k = 0; k < aggCount; k++)
                    if (aggressors[k] == ped) { found = true; break; }
                if (!found && aggCount < 32)
                {
                    aggressors[aggCount++] = ped;
                    Log("Participante de combate via saude (dist: " +
                        std::to_string((int)dist) + "m)");
                }
            }
        }
    }

    g_healthInit = true;

    if (aggCount == 0 || copCount == 0) return;

    Log("Violencia detectada: " + std::to_string(aggCount) +
        " agressor(es), " + std::to_string(copCount) + " policia(s)");

    // Destacar cada cop para o agressor mais proximo
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
            Log("Destacar cop (dist agressor: " + std::to_string((int)minDist) + "m)");
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
    Log("=== LocalReactivePolice v7 iniciado ===");
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
