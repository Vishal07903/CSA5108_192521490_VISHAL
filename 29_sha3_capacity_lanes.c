/*
 * ============================================================================
 *  EXPERIMENT 29 : SHA-3 - HOW LONG UNTIL THE CAPACITY LANES BECOME NONZERO?
 * ============================================================================
 *  Aim
 *  ---
 *  Consider the SHA-3 option with a block size (rate) of 1024 bits and assume
 *  that each of the lanes in the first message block P0 has at least one
 *  nonzero bit.  To start, all of the lanes of the internal state matrix that
 *  correspond to the CAPACITY portion of the initial state are zero.  Show how
 *  long it will take before all of these lanes have at least one nonzero bit.
 *  (Ignore the permutation: keep track of the original zero lanes even after
 *  they have changed position in the matrix.)
 *
 *  Setting
 *  -------
 *   state = 5 x 5 lanes of 64 bits = 1600 bits;  lane (x,y) is at index x + 5y
 *   rate  r = 1024 bits = 16 lanes  (indices 0..15)  <- XORed with message block P0
 *   cap.  c =  576 bits =  9 lanes  (indices 16..24) <- initially all ZERO
 *   rows:  y=0  R R R R R
 *          y=1  R R R R R
 *          y=2  R R R R R
 *          y=3  R C C C C        (R = rate lane, C = capacity lane)
 *          y=4  C C C C C
 *
 *  Analysis
 *  --------
 *  Each of the 24 rounds of Keccak-f is theta, rho, pi, chi, iota.  Only theta
 *  and chi move information BETWEEN lanes (rho rotates inside a lane, pi just
 *  moves lanes around - hence "ignore the permutation").
 *
 *  THETA:   C[x] = A[x,0] ^ A[x,1] ^ A[x,2] ^ A[x,3] ^ A[x,4]          (column parity)
 *           D[x] = C[x-1] ^ ROTL(C[x+1], 1)
 *           A[x,y] = A[x,y] ^ D[x]                                      (every lane!)
 *  Every column contains at least one RATE lane (row y=0 is all rate lanes), and
 *  every rate lane has a nonzero bit, so (barring an exact cancellation of
 *  equal lanes) every column parity C[x] is nonzero, hence every D[x] is
 *  nonzero.  The capacity lanes are zero, so after "A[x,y] ^= D[x]" each of
 *  them equals the nonzero value D[x].
 *
 *  ==> ALL capacity lanes are nonzero after the theta step of the FIRST ROUND:
 *      the diffusion takes ONE round of the 24 (even one step of it).
 *      From then on every lane of the state stays nonzero.
 *
 *  (The "no exact cancellation" assumption holds for any realistic block: C[x] is
 *  the XOR of 3-4 different 64-bit lanes; it is zero only for a special block.)
 *
 *  The program
 *   1. self-checks the Keccak code against the SHA3-256 test vectors
 *   2. shows the lane map of the 1024-bit-rate state
 *   3. runs an abstract "lane is zero / nonzero" model of theta (the argument above)
 *   4. runs the REAL Keccak-f permutation step by step on a random block with
 *      zero capacity and prints which lanes are nonzero after each step
 *   5. repeats the experiment for many random blocks and reports the result
 *
 *  Compile :  gcc 29_sha3_capacity_lanes.c -o sha3_lanes
 * ============================================================================
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* ======================================================================== */
/*  KECCAK-f[1600] (the SHA-3 permutation), split into its five steps       */
/*  Lane (x,y) is stored at index x + 5*y; each lane is 64 bits.            */
/* ======================================================================== */
typedef unsigned long long u64;
typedef unsigned char u8;

#define ROL64(v, n) (((v) << (n)) | ((v) >> (64 - (n))))

static const u64 KECCAK_RC[24] = {
    0x0000000000000001ULL, 0x0000000000008082ULL, 0x800000000000808aULL, 0x8000000080008000ULL,
    0x000000000000808bULL, 0x0000000080000001ULL, 0x8000000080008081ULL, 0x8000000000008009ULL,
    0x000000000000008aULL, 0x0000000000000088ULL, 0x0000000080008009ULL, 0x000000008000000aULL,
    0x000000008000808bULL, 0x800000000000008bULL, 0x8000000000008089ULL, 0x8000000000008003ULL,
    0x8000000000008002ULL, 0x8000000000000080ULL, 0x000000000000800aULL, 0x800000008000000aULL,
    0x8000000080008081ULL, 0x8000000000008080ULL, 0x0000000080000001ULL, 0x8000000080008008ULL };
static const int KECCAK_ROT[24] = {1,3,6,10,15,21,28,36,45,55,2,14,27,41,56,8,25,43,62,18,39,61,20,44};
static const int KECCAK_PI[24]  = {10,7,11,17,18,3,5,16,8,21,24,4,15,23,19,13,12,2,20,14,22,9,6,1};

static void keccak_theta(u64 st[25])
{
    u64 bc[5], t;
    int i, j;
    for (i = 0; i < 5; i++) bc[i] = st[i] ^ st[i + 5] ^ st[i + 10] ^ st[i + 15] ^ st[i + 20];
    for (i = 0; i < 5; i++) {
        t = bc[(i + 4) % 5] ^ ROL64(bc[(i + 1) % 5], 1);
        for (j = 0; j < 25; j += 5) st[j + i] ^= t;
    }
}

static void keccak_rho_pi(u64 st[25])
{
    u64 t = st[1], bc0;
    int i;
    for (i = 0; i < 24; i++) {
        int j = KECCAK_PI[i];
        bc0 = st[j];
        st[j] = ROL64(t, KECCAK_ROT[i]);
        t = bc0;
    }
}

static void keccak_chi(u64 st[25])
{
    u64 bc[5];
    int i, j;
    for (j = 0; j < 25; j += 5) {
        for (i = 0; i < 5; i++) bc[i] = st[j + i];
        for (i = 0; i < 5; i++) st[j + i] ^= (~bc[(i + 1) % 5]) & bc[(i + 2) % 5];
    }
}

static void keccak_round(u64 st[25], int round)
{
    keccak_theta(st);
    keccak_rho_pi(st);
    keccak_chi(st);
    st[0] ^= KECCAK_RC[round];                          /* iota */
}

static void keccak_f(u64 st[25]) { int r; for (r = 0; r < 24; r++) keccak_round(st, r); }

/* SHA3-256 of a byte string (rate 136 bytes, domain byte 0x06) - used as a self-check */
static void sha3_256(const u8 *msg, size_t len, u8 out[32])
{
    u64 st[25] = {0};
    u8 blk[136];
    size_t off = 0;
    int i, k;
    while (len - off >= 136) {
        for (i = 0; i < 17; i++) { u64 w = 0; for (k = 7; k >= 0; k--) w = (w << 8) | msg[off + 8 * i + k]; st[i] ^= w; }
        keccak_f(st);
        off += 136;
    }
    memset(blk, 0, sizeof blk);
    memcpy(blk, msg + off, len - off);
    blk[len - off] ^= 0x06;
    blk[135] ^= 0x80;
    for (i = 0; i < 17; i++) { u64 w = 0; for (k = 7; k >= 0; k--) w = (w << 8) | blk[8 * i + k]; st[i] ^= w; }
    keccak_f(st);
    for (i = 0; i < 32; i++) out[i] = (u8)(st[i / 8] >> (8 * (i % 8)));
}
/* ========================= end of Keccak core ============================= */


#define RATE_LANES 16          /* 1024 bits */
#define LANES      25

static u64 rng_s = 0x9E3779B97F4A7C15ULL;
static u64 rnd64(void)
{
    rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17;
    return rng_s * 0x2545F4914F6CDD1DULL;
}

static void show_hex(const u8 *d, int n) { int i; for (i = 0; i < n; i++) printf("%02x", d[i]); }

static void self_check(void)
{
    static const char *want0 = "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a";
    static const char *want1 = "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532";
    u8 h[32];
    char got[65];
    int i, ok;
    sha3_256((const u8 *)"", 0, h);
    for (i = 0; i < 32; i++) sprintf(got + 2 * i, "%02x", h[i]);
    ok = !strcmp(got, want0);
    printf("  SHA3-256(\"\")    = "); show_hex(h, 32); printf("  %s\n", ok ? "[PASS]" : "[FAIL]");
    sha3_256((const u8 *)"abc", 3, h);
    for (i = 0; i < 32; i++) sprintf(got + 2 * i, "%02x", h[i]);
    printf("  SHA3-256(\"abc\") = "); show_hex(h, 32); printf("  %s\n", !strcmp(got, want1) ? "[PASS]" : "[FAIL]");
}

/* print the 5x5 lane map: R/C = original role, uppercase = nonzero, '.' = zero */
static void grid(const char *title, const int nz[LANES], int original_roles)
{
    int x, y;
    printf("  %s\n", title);
    for (y = 0; y < 5; y++) {
        printf("      ");
        for (x = 0; x < 5; x++) {
            int idx = x + 5 * y;
            char ch;
            if (!nz[idx]) ch = '.';
            else if (original_roles) ch = (idx < RATE_LANES) ? 'R' : 'C';
            else ch = '#';
            printf("%c ", ch);
        }
        printf("\n");
    }
}

static int count_zero(const int nz[LANES]) { int i, n = 0; for (i = 0; i < LANES; i++) if (!nz[i]) n++; return n; }
static int cap_zero(const int nz[LANES])   { int i, n = 0; for (i = RATE_LANES; i < LANES; i++) if (!nz[i]) n++; return n; }

/* abstract model of theta: lane nonzero  <=>  (itself or D[x]) nonzero, with D[x] nonzero if any column
   parity C[x-1] or C[x+1] is nonzero, and C[x] nonzero if any lane of column x is nonzero  */
static void abstract_theta(int nz[LANES])
{
    int cpar[5], dd[5], x, y;
    for (x = 0; x < 5; x++) { cpar[x] = 0; for (y = 0; y < 5; y++) cpar[x] |= nz[x + 5 * y]; }
    for (x = 0; x < 5; x++) dd[x] = cpar[(x + 4) % 5] | cpar[(x + 1) % 5];
    for (x = 0; x < 5; x++) for (y = 0; y < 5; y++) nz[x + 5 * y] |= dd[x];
}

static void to_flags(const u64 st[LANES], int nz[LANES]) { int i; for (i = 0; i < LANES; i++) nz[i] = st[i] != 0; }

int main(void)
{
    int nz[LANES], i, x, y;
    u64 st[LANES];
    int trials = 20000, ok_theta = 0, ok_round = 0, rounds_needed_max = 0;

    rng_s ^= (u64)time(NULL) * 0x2545F4914F6CDD1DULL;
    printf("=========================================\n");
    printf("   SHA-3 : DIFFUSION INTO THE CAPACITY LANES\n");
    printf("=========================================\n");
    printf("\nSelf-check of the Keccak implementation:\n");
    self_check();

    printf("\nState with rate r = 1024 bits (16 lanes) and capacity c = 576 bits (9 lanes):\n");
    for (i = 0; i < LANES; i++) nz[i] = 1;
    printf("      R = rate lane (nonzero message lane)   C = capacity lane\n");
    for (y = 0; y < 5; y++) {
        printf("      ");
        for (x = 0; x < 5; x++) printf("%c ", (x + 5 * y < RATE_LANES) ? 'R' : 'C');
        printf("\n");
    }
    printf("      Every column contains a rate lane in row y = 0.\n");

    /* ------------------- abstract model --------------------------------- */
    printf("\n--- PART 1: abstract model (lane = zero or nonzero) ---\n");
    for (i = 0; i < LANES; i++) nz[i] = (i < RATE_LANES);
    grid("initial state after XORing P0 (all 16 rate lanes nonzero, 9 capacity lanes zero):", nz, 1);
    printf("      capacity lanes still zero: %d of 9\n", cap_zero(nz));
    printf("\n  column parities C[x] (x=0..4) all contain a nonzero rate lane -> nonzero\n");
    printf("  D[x] = C[x-1] ^ ROTL(C[x+1],1) is therefore nonzero for every x\n");
    abstract_theta(nz);
    grid("after the theta step of round 1 (A[x,y] ^= D[x] touches every lane;\n      a letter C now means a capacity lane that has become NONZERO, \'.\' = still zero):", nz, 1);
    printf("      capacity lanes still zero: %d of 9      lanes still zero overall: %d of 25\n", cap_zero(nz), count_zero(nz));

    /* ------------------- real Keccak ------------------------------------ */
    printf("\n--- PART 2: the real Keccak-f[1600], step by step ---\n");
    for (i = 0; i < LANES; i++) st[i] = (i < RATE_LANES) ? (rnd64() | 1ULL) : 0ULL;   /* P0 XOR 0 */
    printf("  Initial state (random 1024-bit block P0 in the rate lanes, zeros in the capacity):\n");
    for (i = 0; i < LANES; i++) { if (i % 5 == 0) printf("      "); printf("%016llx%s", st[i], (i % 5 == 4) ? "\n" : " "); }
    to_flags(st, nz);
    grid("nonzero lanes at the start:", nz, 1);

    printf("\n  ROUND 1\n");
    keccak_theta(st);   to_flags(st, nz); grid("after theta :", nz, 0);
    printf("      zero lanes left: %d   (capacity lanes still zero: %d)\n", count_zero(nz), cap_zero(nz));
    keccak_rho_pi(st);  to_flags(st, nz); printf("  after rho+pi: zero lanes left: %d\n", count_zero(nz));
    keccak_chi(st);     to_flags(st, nz); printf("  after chi   : zero lanes left: %d\n", count_zero(nz));
    st[0] ^= KECCAK_RC[0]; to_flags(st, nz); printf("  after iota  : zero lanes left: %d\n", count_zero(nz));

    printf("\n  rounds 2..4 (just to confirm the state stays fully nonzero):\n");
    for (i = 1; i < 4; i++) { keccak_round(st, i); to_flags(st, nz); printf("   after round %d: zero lanes = %d\n", i + 1, count_zero(nz)); }

    /* ------------------- many trials ------------------------------------ */
    printf("\n--- PART 3: %d random blocks ---\n", trials);
    for (i = 0; i < trials; i++) {
        int k, rounds = 0;
        for (k = 0; k < LANES; k++) st[k] = (k < RATE_LANES) ? (rnd64() | 1ULL) : 0ULL;
        keccak_theta(st); to_flags(st, nz);
        if (cap_zero(nz) == 0) ok_theta++;
        /* count rounds until no capacity lane is zero (rounds measured on a fresh copy) */
        for (k = 0; k < LANES; k++) st[k] = (k < RATE_LANES) ? (rnd64() | 1ULL) : 0ULL;
        for (rounds = 1; rounds <= 24; rounds++) {
            keccak_round(st, rounds - 1); to_flags(st, nz);
            if (count_zero(nz) == 0) break;
        }
        if (rounds == 1) ok_round++;
        if (rounds > rounds_needed_max) rounds_needed_max = rounds;
    }
    printf("  all 9 capacity lanes nonzero right after THETA of round 1 : %d / %d blocks\n", ok_theta, trials);
    printf("  whole state (25 lanes) nonzero after round 1              : %d / %d blocks\n", ok_round, trials);
    printf("  largest number of rounds needed in any trial              : %d\n", rounds_needed_max);

    printf("\nCONCLUSION\n"
           "  It takes only ONE round of the permutation (the theta step of the first round): every\n"
           "  column parity picks up a nonzero rate lane, and theta XORs the resulting D[x] into all\n"
           "  five lanes of its column - including the capacity lanes, which were zero.  After one of\n"
           "  the 24 rounds of the first call to Keccak-f, all 25 lanes (rate and capacity) are nonzero.\n");
    return 0;
}
