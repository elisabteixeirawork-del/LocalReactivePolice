/*
 * LocalReactivePolice.cpp - v6.1
 * Plugin GTA San Andreas - Policia Reativa Local
 *
 * Mudancas v6.1:
 *   - Nova filosofia: detectar PARES em conflito (nao agressores isolados)
 *   - Remocao de IsPedArmed() como criterio isolado
 *   - Cooldown por cop (10s entre tasks)
 *   - Correcao do offset de posicao
 *   - Validacao extra em ForceCopAttack
 *   - Log mais limpo e informativo
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

// Offsets dentro de CPed / CEntity / CPlaceable
// CPlaceable::m_matrix esta em offset 0x14 dentro de CEntity
// CMatrix::pos (translation) esta em offset 0x30 dentro de CMatrix
// Logo posicao = ped + 0x14 + 0x30 = ped + 0x44
// MAS: no GTA SA o CPed herda CPhysical herda CEntity herda CPlaceable
// e o compilador pode inserir padding. O offset correcto confirmado
// pela comunidade para CEntity::GetPosition() e ped+0x44 (x), +0x48 (y), +0x4C (z)
// Se der 0,0,0 e porque o pool offset (0x7C4) esta errado.
// Tamanho real de CPed no SA = 0x7C4 bytes (confirmado pela comunidade).
#define PED_POS_X                   0x44
#define PED_POS_Y                   0x48
#define PED_POS_Z                   0x4C

#define PED_HEALTH_OFFSET           0x540
#define PED_TYPE_OFFSET             0x528
#define PED_FLAGS_OFFSET            0x46C
#define PED_TASK_MGR_OFFSET         0x4A8
#define PED_IN_VEHICLE_FLAG         (1 << 8)
#define PED_TYPE_COP                6

// Arma activa: slot em 0x718, array de armas em 0x5A0 (cada CWeapon = 0x1C bytes)
#define PED_ACTIVE_WEAPON_SLOT      0x718
#define PED_WEAPON_ARRAY_OFFSET     0x5A0
#define WEAPON_TYPE_IN_SLOT         0x00   // offset do tipo dentro de CWeapon

// Tasks
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
#define TASK_SIMPLE_FIRE_GUN                    155

// ─────────────────────────────────────────────
//  CONFIGURACOES
// ─────────────────────────────────────────────

static constexpr float DETECTION_RADIUS     = 70.0f;   // raio de detecao de combate
static constexpr float POLICE_ENGAGE_RADIUS = 85.0f;   // raio de reacao policial
static constexpr float COMBAT_PAIR_DIST     = 20.0f;   // distancia maxima entre par em conflito
static constexpr float HP_LOSS_THRESHOLD    = 1.0f;    // perda minima de HP para considerar dano
static constexpr int   CHECK_INTERVAL_MS    = 500;     // intervalo de verificacao
static constexpr int   COP_COOLDOWN_MS      = 10000;   // cooldown por cop (10s)
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

// Cooldown por cop: guarda DWORD de endereco do cop -> timestamp
#define MAX_COPS_TRACKED 16
static DWORD g_copAddr[MAX_COPS_TRACKED]      = {};
static DWORD g_copLastTask[MAX_COPS_TRACKED]  = {};  // GetTickCount() de quando foi dado task

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
    if (IsBadReadPtr((void*)(ped + PED_POS_X), 12)) return v;
    v.x = ReadMem<float>(ped + PED_POS_X);
    v.y = ReadMem<float>(ped + PED_POS_Y);
    v.z = ReadMem<float>(ped + PED_POS_Z);
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
    // Se posicao for (0,0,0) exactamente, offset pode estar errado
    // Nao filtrar por isso - deixar passar e calcular dist normal
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
    if (IsBadReadPtr((void*)(ped + PED_TYPE_OFFSET), 1)) return false;
    return ReadMem<BYTE>(ped + PED_TYPE_OFFSET) == PED_TYPE_COP;
}

static bool IsInVehicle(DWORD ped)
{
    if (!ped) return true;
    if (IsBadReadPtr((void*)(ped + PED_FLAGS_OFFSET), 4)) return true;
    return (ReadMem<DWORD>(ped + PED_FLAGS_OFFSET) & PED_IN_VEHICLE_FLAG) != 0;
}

// ─────────────────────────────────────────────
//  SAUDE A DIMINUIR
// ─────────────────────────────────────────────

static bool IsPedLosingHealth(DWORD ped, int index)
{
    if (!ped || index < 0 || index >= 140) return false;
    if (IsBadReadPtr((void*)(ped + PED_HEALTH_OFFSET), 4)) return false;

    float curHP = ReadMem<float>(ped + PED_HEALTH_OFFSET);

    if (!g_healthInit)
    {
        g_prevHealth[index] = curHP;
        return false;
    }

    float prevHP = g_prevHealth[index];
    g_prevHealth[index] = curHP;

    return (prevHP > 0.f && curHP > 0.f && (prevHP - curHP) > HP_LOSS_THRESHOLD);
}

// ─────────────────────────────────────────────
//  TASK DE COMBATE (backup)
// ─────────────────────────────────────────────

static bool HasCombatTask(DWORD ped)
{
    if (!ped) return false;
    static const int tasks[] = {
        TASK_COMPLEX_KILL_PED_ON_FOOT, TASK_COMPLEX_KILL_PED_ON_FOOT_STEALTH,
        TASK_COMPLEX_FIGHT, TASK_SIMPLE_FIGHT, TASK_SIMPLE_GUN_CTRL,
        TASK_COMPLEX_GUN_FIGHT, TASK_SIMPLE_SHOOT_AT_PED, TASK_COMPLEX_ATTACK_PED,
        TASK_SIMPLE_PUNCH, TASK_SIMPLE_BE_HIT, TASK_SIMPLE_FIRE_GUN, -1
    };

    for (int slot = 0; slot <= 4; slot++)
    {
        DWORD taskMgr = ped + PED_TASK_MGR_OFFSET;
        if (IsBadReadPtr((void*)taskMgr, (slot+1)*4)) continue;
        DWORD task = ReadMem<DWORD>(taskMgr + slot * 4);
        if (!task || IsBadReadPtr((void*)task, 8)) continue;
        int type = ReadMem<int>(task + 0x4);
        for (int i = 0; tasks[i] != -1; i++)
            if (type == tasks[i]) return true;
    }
    return false;
}

// ─────────────────────────────────────────────
//  COOLDOWN POR COP
// ─────────────────────────────────────────────

static bool CopIsOnCooldown(DWORD cop)
{
    DWORD now = GetTickCount();
    for (int i = 0; i < MAX_COPS_TRACKED; i++)
    {
        if (g_copAddr[i] == cop)
            return (now - g_copLastTask[i]) < (DWORD)COP_COOLDOWN_MS;
    }
    return false;
}

static void SetCopCooldown(DWORD cop)
{
    DWORD now = GetTickCount();
    // Verificar se ja existe
    for (int i = 0; i < MAX_COPS_TRACKED; i++)
    {
        if (g_copAddr[i] == cop)
        {
            g_copLastTask[i] = now;
            return;
        }
    }
    // Inserir em slot livre ou substituir o mais antigo
    int oldest = 0;
    DWORD oldestTime = g_copLastTask[0];
    for (int i = 1; i < MAX_COPS_TRACKED; i++)
    {
        if (g_copAddr[i] == 0) { oldest = i; break; }
        if (g_copLastTask[i] < oldestTime) { oldest = i; oldestTime = g_copLastTask[i]; }
    }
    g_copAddr[oldest]    = cop;
    g_copLastTask[oldest] = now;
}

// ─────────────────────────────────────────────
//  FORCIAR COP A ATACAR
// ─────────────────────────────────────────────

typedef void* (__thiscall* tKillTaskCtor)(void*, DWORD*, int, int, bool, bool, float);
typedef void  (__thiscall* tSetTask)(void*, void*, int);

static tKillTaskCtor KillTaskCtor = (tKillTaskCtor)0x624670;
static tSetTask      SetTask      = (tSetTask)0x681AD0;

static bool ForceCopAttack(DWORD cop, DWORD target)
{
    if (!IsPedValid(cop) || !IsPedValid(target)) return false;
    if (cop == target) return false;
    if (CopIsOnCooldown(cop))
    {
        Log("Cop em cooldown, ignorar");
        return false;
    }

    DWORD taskMgr = cop + PED_TASK_MGR_OFFSET;
    if (IsBadReadPtr((void*)taskMgr, 20)) return false;

    // Verificar se ja tem kill task activa
    DWORD cur = ReadMem<DWORD>(taskMgr + 2 * 4);
    if (cur && !IsBadReadPtr((void*)cur, 8))
    {
        if (ReadMem<int>(cur + 0x4) == TASK_COMPLEX_KILL_PED_ON_FOOT)
        {
            Log("Cop ja tem kill task activa");
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
    Log("ForceCopAttack: OK");
    return true;
}

// ─────────────────────────────────────────────
//  DETECAO DE COMBATE - FILOSOFIA V6.1
//
//  Em vez de procurar "agressores", procuramos
//  PARES DE PEDS em conflito activo:
//
//  Um par (A, B) esta em conflito se:
//    - A e B estao proximos (< COMBAT_PAIR_DIST)
//    - Pelo menos um perdeu HP recentemente OU
//      tem task de combate activa
//    - Nenhum dos dois e o jogador
//    - Nenhum dos dois e policia
//
//  Isto e mais robusto que verificar agressores
//  individualmente porque:
//    - Nao depende de offsets de target incertos
//    - Nao confunde "armado" com "em combate"
//    - Funciona para tiroteios, facadas, lutas
// ─────────────────────────────────────────────

struct CombatParticipant
{
    DWORD ped;
    int   poolIndex;
};

static void ProcessLocalViolence()
{
    DWORD player = GetPlayerPed();
    if (!player || IsBadReadPtr((void*)player, 0x600)) return;

    Vec3 pp = GetPedPos(player);
    int poolSize = GetPedPoolSize();
    if (poolSize <= 0 || poolSize > 140) return;

    // Recolher todos os peds validos dentro do raio
    static CombatParticipant nearPeds[64];
    static DWORD cops[32];
    int nearCount = 0, copCount = 0;

    // Array de "perdeu HP" para cada ped no near
    static bool lostHP[64];

    for (int i = 0; i < poolSize && nearCount < 64 && copCount < 32; i++)
    {
        DWORD ped = GetPedAt(i);
        if (!ped || ped == player) continue;
        if (!IsPedValid(ped)) continue;
        if (IsInVehicle(ped)) continue;

        float dist = Dist2DToXY(ped, pp.x, pp.y);

        if (IsCopPed(ped))
        {
            if (dist <= POLICE_ENGAGE_RADIUS)
                cops[copCount++] = ped;
            continue;
        }

        if (dist <= DETECTION_RADIUS)
        {
            bool lost = IsPedLosingHealth(ped, i);
            nearPeds[nearCount]  = { ped, i };
            lostHP[nearCount]    = lost;
            nearCount++;
        }
        else
        {
            // Actualizar historico mesmo fora do raio
            IsPedLosingHealth(ped, i);
        }
    }

    g_healthInit = true;

    if (nearCount < 2 || copCount == 0) return;

    // Procurar pares em conflito activo
    // Um par valido: distancia < COMBAT_PAIR_DIST E
    //   pelo menos um tem task de combate OU pelo menos um perdeu HP
    static DWORD combatPeds[32];
    int combatCount = 0;

    for (int a = 0; a < nearCount && combatCount < 30; a++)
    {
        for (int b = a + 1; b < nearCount && combatCount < 30; b++)
        {
            DWORD pedA = nearPeds[a].ped;
            DWORD pedB = nearPeds[b].ped;

            float pairDist = Dist2D(pedA, pedB);
            if (pairDist > COMBAT_PAIR_DIST) continue;

            bool aFighting = lostHP[a] || HasCombatTask(pedA);
            bool bFighting = lostHP[b] || HasCombatTask(pedB);

            if (!aFighting && !bFighting) continue;

            // Par em conflito encontrado
            Vec3 pa = GetPedPos(pedA);
            Log("Par em conflito: dist=" + std::to_string((int)pairDist) +
                "m pos=[" + std::to_string((int)pa.x) + "," + std::to_string((int)pa.y) + "]" +
                " A_fight=" + (aFighting ? "sim" : "nao") +
                " B_fight=" + (bFighting ? "sim" : "nao"));

            // Adicionar participantes ao combate (sem duplicados)
            bool foundA = false, foundB = false;
            for (int k = 0; k < combatCount; k++)
            {
                if (combatPeds[k] == pedA) foundA = true;
                if (combatPeds[k] == pedB) foundB = true;
            }
            if (!foundA && combatCount < 32) combatPeds[combatCount++] = pedA;
            if (!foundB && combatCount < 32) combatPeds[combatCount++] = pedB;
        }
    }

    if (combatCount == 0) return;

    Log("Combate detectado: " + std::to_string(combatCount) +
        " participante(s), " + std::to_string(copCount) + " policia(s)");

    // Destacar cada cop para o participante mais proximo
    int tasked = 0;
    for (int c = 0; c < copCount; c++)
    {
        DWORD cop = cops[c];

        // Encontrar participante mais proximo deste cop
        DWORD closest = 0;
        float minDist = 9999.f;
        for (int k = 0; k < combatCount; k++)
        {
            float d = Dist2D(cop, combatPeds[k]);
            if (d < minDist) { minDist = d; closest = combatPeds[k]; }
        }

        if (closest)
        {
            Log("Destacar cop para participante a " + std::to_string((int)minDist) + "m");
            if (ForceCopAttack(cop, closest))
                tasked++;
        }
    }

    if (tasked > 0)
        Log("Total cops destacados: " + std::to_string(tasked));
}

// ─────────────────────────────────────────────
//  THREAD E ENTRY POINT
// ─────────────────────────────────────────────

static HANDLE g_hThread = nullptr;
static bool   g_bRunning = false;

static DWORD WINAPI PluginThread(LPVOID)
{
    Sleep(5000);
    Log("=== LocalReactivePolice v6.1 iniciado ===");
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
