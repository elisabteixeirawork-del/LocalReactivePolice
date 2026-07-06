/*
 * LocalReactivePolice.cpp - v6
 * Plugin GTA San Andreas - Policia Reativa Local
 *
 * v6: Sistema de detecao baseado em eventos reais do GTA SA
 * em vez de TASK IDs incertas.
 *
 * Abordagem:
 *   1. Saude a diminuir entre frames (ped a sofrer dano activo)
 *   2. Arma equipada + flag de disparo activo
 *   3. CEventHandler com eventos hostis activos
 *   4. TASK IDs como ultimo recurso (lista alargada)
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

#define PED_POOL_PTR                0xB74490
#define PLAYER_PED_PTR              0xB6F5F0

// Offsets dentro de CPed
#define PED_HEALTH_OFFSET           0x540   // float
#define PED_TYPE_OFFSET             0x528   // BYTE
#define PED_FLAGS_OFFSET            0x46C   // DWORD
#define PED_TASK_MGR_OFFSET         0x4A8   // CTaskManager (inline, 5 slots * 4 bytes)
#define PED_TARGET_OFFSET           0x564   // CEntity* m_pTargetedObject
#define PED_IN_VEHICLE_FLAG         (1 << 8)
#define ENTITY_TYPE_PED             4
#define PED_TYPE_COP                6

// Offsets de arma (dentro de CPed)
// CWeaponSlot array começa em 0x5A0, cada slot tem 0x1C bytes
// slot actual em 0x718 (m_nActiveWeaponSlot = BYTE)
#define PED_ACTIVE_WEAPON_SLOT      0x718   // BYTE: indice do slot activo (0=fists)
#define PED_WEAPON_ARRAY_OFFSET     0x5A0   // array de CWeapon (cada um tem 0x1C bytes)
#define WEAPON_TYPE_OFFSET          0x00    // DWORD dentro de CWeapon: eWeaponType

// Offsets de animacao / estado
// RpAnimBlend em CPed: offset 0x4C8 - nao usar, demasiado fragil
// Usar flags de estado do ped
#define PED_FIGHTFLAGS_OFFSET       0x46C   // flags gerais (bit 16 = bInFight?)

// CEventHandler: lista de eventos activos do ped
// CPed::m_pEventHandler = offset 0x578 (ponteiro para CEventHandler)
#define PED_EVENT_HANDLER_OFFSET    0x578   // CEventHandler*

// Dentro de CEventHandler:
// offset 0x04 = array de CEvent* (lista de eventos activos)
// offset 0x08 = numero de eventos activos
#define EVENTHANDLER_EVENTS_OFFSET  0x04
#define EVENTHANDLER_COUNT_OFFSET   0x08

// Tipos de eventos relevantes (eEventType no GTA SA)
// Estes valores sao da analise da comunidade SA-MP/modding
#define EVENT_GUN_SHOT              8    // alguem disparou perto
#define EVENT_PED_DEAD              53   // ped morreu perto
#define EVENT_POTENTIAL_GET_RUN_OVER 13  // atropelamento
#define EVENT_SEEN_PANICPED         46   // ped em panico visto
#define EVENT_DAMAGE               16   // dano sofrido
#define EVENT_INJURED              17   // ferido
#define EVENT_KNOCKED_OFF_BIKE     36   // derrubado de mota
#define EVENT_FIRE                 10   // incendio

// Tasks (ultimo recurso)
#define TASK_COMPLEX_KILL_PED_ON_FOOT           167
#define TASK_COMPLEX_KILL_PED_ON_FOOT_STEALTH   168
#define TASK_COMPLEX_FIGHT                      134
#define TASK_SIMPLE_FIGHT                       140
#define TASK_SIMPLE_GUN_CTRL                    160
#define TASK_COMPLEX_GUN_FIGHT                  162
#define TASK_SIMPLE_SHOOT_AT_PED                159
#define TASK_COMPLEX_ATTACK_PED                 130
#define TASK_SIMPLE_PUNCH                       138
#define TASK_SIMPLE_BE_HIT                      136
#define TASK_COMPLEX_FLEE_PED_ON_FOOT           147
#define TASK_SIMPLE_FIRE_GUN                    155  // disparar com arma

// ─────────────────────────────────────────────
//  CONFIGURACOES
// ─────────────────────────────────────────────

static constexpr float DETECTION_RADIUS     = 70.0f;
static constexpr float POLICE_ENGAGE_RADIUS = 85.0f;
static constexpr int   CHECK_INTERVAL_MS    = 400;  // ligeiramente mais rapido
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
//  HISTORICO DE SAUDE (para detectar dano activo)
// ─────────────────────────────────────────────

// Guarda a saude anterior de cada ped no pool (max 140 peds)
static float g_prevHealth[140] = {};
static bool  g_healthInitialized = false;

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
    if (IsBadReadPtr((void*)ped, 0x750)) return false;
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
//  METODO 1: SAUDE A DIMINUIR ENTRE FRAMES
//  O ped perdeu HP desde a ultima verificacao?
//  Isso indica que esta a ser atacado activamente.
// ─────────────────────────────────────────────

static bool IsPedLosingHealth(DWORD ped, int index)
{
    if (!ped || index < 0 || index >= 140) return false;
    if (IsBadReadPtr((void*)(ped + PED_HEALTH_OFFSET), 4)) return false;

    float currentHP = ReadMem<float>(ped + PED_HEALTH_OFFSET);

    if (!g_healthInitialized)
    {
        g_prevHealth[index] = currentHP;
        return false;
    }

    float prevHP = g_prevHealth[index];
    g_prevHealth[index] = currentHP;

    // Perdeu mais de 1 ponto de HP desde a ultima frame de verificacao
    if (prevHP > 0.f && currentHP > 0.f && (prevHP - currentHP) > 1.0f)
    {
        Log("Ped a perder saude: " + std::to_string((int)prevHP) +
            " -> " + std::to_string((int)currentHP));
        return true;
    }
    return false;
}

// ─────────────────────────────────────────────
//  METODO 2: ARMA EQUIPADA
//  Ped tem arma na mao que nao seja os punhos?
//  Tipo de arma > 0 e slot activo > 0.
// ─────────────────────────────────────────────

static bool IsPedArmed(DWORD ped)
{
    if (!ped) return false;
    if (IsBadReadPtr((void*)(ped + PED_ACTIVE_WEAPON_SLOT), 1)) return false;

    BYTE activeSlot = ReadMem<BYTE>(ped + PED_ACTIVE_WEAPON_SLOT);

    // Slot 0 = punhos, ignorar
    if (activeSlot == 0) return false;
    if (activeSlot > 12) return false;

    // Ler tipo da arma no slot activo
    DWORD weaponAddr = ped + PED_WEAPON_ARRAY_OFFSET + (activeSlot * 0x1C);
    if (IsBadReadPtr((void*)weaponAddr, 4)) return false;

    DWORD weaponType = ReadMem<DWORD>(weaponAddr + WEAPON_TYPE_OFFSET);

    // Tipos de arma > 1 sao armas reais (facas, pistolas, etc.)
    if (weaponType > 1)
    {
        Log("Ped armado: arma tipo " + std::to_string(weaponType) +
            " no slot " + std::to_string(activeSlot));
        return true;
    }
    return false;
}

// ─────────────────────────────────────────────
//  METODO 3: EVENTOS ACTIVOS NO CEventHandler
//  Verificar se o ped tem eventos hostis activos
//  (disparos, dano, panico, etc.)
// ─────────────────────────────────────────────

static bool IsPedHavingCombatEvent(DWORD ped)
{
    if (!ped) return false;
    if (IsBadReadPtr((void*)(ped + PED_EVENT_HANDLER_OFFSET), 4)) return false;

    DWORD eventHandler = ReadMem<DWORD>(ped + PED_EVENT_HANDLER_OFFSET);
    if (!eventHandler) return false;
    if (IsBadReadPtr((void*)eventHandler, 16)) return false;

    int eventCount = ReadMem<int>(eventHandler + EVENTHANDLER_COUNT_OFFSET);
    if (eventCount <= 0 || eventCount > 32) return false;

    DWORD eventsArray = ReadMem<DWORD>(eventHandler + EVENTHANDLER_EVENTS_OFFSET);
    if (!eventsArray) return false;
    if (IsBadReadPtr((void*)eventsArray, eventCount * 4)) return false;

    for (int i = 0; i < eventCount; i++)
    {
        DWORD eventPtr = ReadMem<DWORD>(eventsArray + i * 4);
        if (!eventPtr) continue;
        if (IsBadReadPtr((void*)eventPtr, 8)) continue;

        // Tipo do evento: offset 0x04 dentro de CEvent
        int eventType = ReadMem<int>(eventPtr + 0x04);

        if (eventType == EVENT_GUN_SHOT    ||
            eventType == EVENT_DAMAGE      ||
            eventType == EVENT_INJURED     ||
            eventType == EVENT_PED_DEAD    ||
            eventType == EVENT_FIRE)
        {
            Log("Evento hostil encontrado: tipo " + std::to_string(eventType));
            return true;
        }
    }
    return false;
}

// ─────────────────────────────────────────────
//  METODO 4: TASK IDs (lista completa, backup)
// ─────────────────────────────────────────────

static int GetTaskTypeAtSlot(DWORD ped, int slot)
{
    if (!ped) return -1;
    DWORD taskMgr = ped + PED_TASK_MGR_OFFSET;
    if (IsBadReadPtr((void*)taskMgr, (slot + 1) * 4)) return -1;
    DWORD task = ReadMem<DWORD>(taskMgr + slot * 4);
    if (!task) return -1;
    if (IsBadReadPtr((void*)task, 8)) return -1;
    return ReadMem<int>(task + 0x4);
}

static bool IsPedFightingByTask(DWORD ped)
{
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
        TASK_COMPLEX_FLEE_PED_ON_FOOT,
        TASK_SIMPLE_FIRE_GUN,
        -1
    };

    for (int slot = 0; slot <= 4; slot++)
    {
        int type = GetTaskTypeAtSlot(ped, slot);
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
    return false;
}

// ─────────────────────────────────────────────
//  DETECAO COMBINADA - usa todos os metodos
// ─────────────────────────────────────────────

static bool IsPedAggressor(DWORD ped, int poolIndex)
{
    // Metodo 1: perdeu saude recentemente (mais fiavel)
    if (IsPedLosingHealth(ped, poolIndex))
    {
        Log("Agressor por perda de saude");
        return true;
    }

    // Metodo 2: tem arma na mao
    if (IsPedArmed(ped))
    {
        Log("Ped armado detectado");
        return true;
    }

    // Metodo 3: tem eventos de combate activos
    if (IsPedHavingCombatEvent(ped))
    {
        Log("Evento de combate activo");
        return true;
    }

    // Metodo 4: task de combate (backup)
    if (IsPedFightingByTask(ped))
    {
        Log("Task de combate detectada");
        return true;
    }

    return false;
}

// ─────────────────────────────────────────────
//  OBTENCAO DO ALVO
// ─────────────────────────────────────────────

static DWORD GetPedTarget(DWORD ped)
{
    if (!ped) return 0;

    static const DWORD offsets[] = { 0x564, 0x55C, 0x568, 0 };

    for (int i = 0; offsets[i] != 0; i++)
    {
        if (IsBadReadPtr((void*)(ped + offsets[i]), 4)) continue;
        DWORD target = ReadMem<DWORD>(ped + offsets[i]);
        if (!target) continue;
        if (IsBadReadPtr((void*)target, 0x40)) continue;
        BYTE nType = ReadMem<BYTE>(target + 0x36);
        if (nType == ENTITY_TYPE_PED)
        {
            Log("Alvo encontrado via offset 0x" +
                std::to_string(offsets[i]));
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

    DWORD cur = ReadMem<DWORD>(taskMgr + 2 * 4);
    if (cur && !IsBadReadPtr((void*)cur, 8))
        if (ReadMem<int>(cur + 0x4) == TASK_COMPLEX_KILL_PED_ON_FOOT)
            return;

    void* task = HeapAlloc(GetProcessHeap(), 0, 0x28);
    if (!task) return;

    KillTaskCtor(task, (DWORD*)target, -1, 0, true, true, 100.f);
    SetTask((void*)taskMgr, task, 2);
    Log("Policia engajou alvo");
}

// ─────────────────────────────────────────────
//  LOGICA PRINCIPAL
// ─────────────────────────────────────────────

static void ProcessLocalViolence()
{
    DWORD player = GetPlayerPed();
    if (!player || IsBadReadPtr((void*)player, 0x750)) return;

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

        if (dist <= DETECTION_RADIUS)
        {
            if (IsPedAggressor(ped, i))
            {
                // Verificar se nao e o CJ a ser o "agressor" detectado
                DWORD target = GetPedTarget(ped);
                bool targetIsPlayer = (target == player);

                if (!targetIsPlayer)
                {
                    Log("Agressor registado (dist: " +
                        std::to_string((int)dist) + "m)");
                    aggressors[aggCount++] = ped;
                }
            }
        }
    }

    // Actualizar flag de inicializacao do historico de saude
    g_healthInitialized = true;

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
    Log("=== LocalReactivePolice v6 iniciado ===");
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
