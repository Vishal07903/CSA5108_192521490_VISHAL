/*
 * ============================================================================
 *  EXPERIMENT 18 : STRUCTURE OF THE DES SUBKEYS
 * ============================================================================
 *  Aim
 *  ---
 *  Show that in DES the FIRST 24 bits of each subkey come from the same subset
 *  of 28 bits of the initial key, and that the SECOND 24 bits of each subkey
 *  come from a DISJOINT subset of 28 bits of the initial key.
 *
 *  Reasoning
 *  ---------
 *  PC-1 selects 56 of the 64 key bits (dropping the 8 parity bits 8,16,..,64)
 *  and splits them into two halves:
 *       C0 = the first 28 bits of PC-1 output  (taken from key bits  S_C)
 *       D0 = the last  28 bits of PC-1 output  (taken from key bits  S_D)
 *  S_C and S_D are disjoint.  In every round C and D are only ROTATED
 *  (cyclically shifted) within their own 28-bit register - bits never cross
 *  from C to D.  So after any number of rounds C still contains exactly the
 *  bits S_C and D exactly the bits S_D.
 *
 *  PC-2 picks 48 of the 56 bits.  Its first 24 outputs are drawn only from
 *  positions 1..28 (the C register) and its last 24 only from positions
 *  29..56 (the D register).  Hence the first 24 bits of EVERY subkey come
 *  from subset S_C (28 key bits) and the last 24 from the disjoint subset S_D.
 *
 *  What the program does (it proves it by tracking the origin of every bit)
 *   1. loads the key as the symbolic values 1..64 (bit number in the key)
 *   2. runs the real DES key schedule on these symbols
 *   3. for each of the 16 subkeys prints which key-bit numbers appear in the
 *      first 24 and the last 24 positions, and checks the claim
 *   4. lists the 4 + 4 bits of C and D that PC-2 discards in each round
 *      and the 8 parity bits dropped by PC-1
 *   5. empirical check: flipping a key bit from S_C changes only the first
 *      24 bits of subkeys, a bit from S_D only the last 24
 *
 *  Compile :  gcc 18_des_subkey_structure.c -o des_subkeys
 * ============================================================================
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ======================================================================== */
/*  DES CORE  (FIPS 46-3)  - tables, key schedule, block encrypt/decrypt    */
/*  Bit numbering follows the standard: bit 1 is the MOST significant bit.  */
/* ======================================================================== */
typedef unsigned long long u64;
typedef unsigned int       u32;
typedef unsigned char      u8;

static const int IP_T[64] = {
    58,50,42,34,26,18,10, 2, 60,52,44,36,28,20,12, 4,
    62,54,46,38,30,22,14, 6, 64,56,48,40,32,24,16, 8,
    57,49,41,33,25,17, 9, 1, 59,51,43,35,27,19,11, 3,
    61,53,45,37,29,21,13, 5, 63,55,47,39,31,23,15, 7 };

static const int FP_T[64] = {
    40, 8,48,16,56,24,64,32, 39, 7,47,15,55,23,63,31,
    38, 6,46,14,54,22,62,30, 37, 5,45,13,53,21,61,29,
    36, 4,44,12,52,20,60,28, 35, 3,43,11,51,19,59,27,
    34, 2,42,10,50,18,58,26, 33, 1,41, 9,49,17,57,25 };

static const int E_T[48] = {
    32, 1, 2, 3, 4, 5,  4, 5, 6, 7, 8, 9,
     8, 9,10,11,12,13, 12,13,14,15,16,17,
    16,17,18,19,20,21, 20,21,22,23,24,25,
    24,25,26,27,28,29, 28,29,30,31,32, 1 };

static const int P_T[32] = {
    16, 7,20,21,29,12,28,17,  1,15,23,26, 5,18,31,10,
     2, 8,24,14,32,27, 3, 9, 19,13,30, 6,22,11, 4,25 };

static const int PC1_T[56] = {
    57,49,41,33,25,17, 9,  1,58,50,42,34,26,18,
    10, 2,59,51,43,35,27, 19,11, 3,60,52,44,36,
    63,55,47,39,31,23,15,  7,62,54,46,38,30,22,
    14, 6,61,53,45,37,29, 21,13, 5,28,20,12, 4 };

static const int PC2_T[48] = {
    14,17,11,24, 1, 5,  3,28,15, 6,21,10,
    23,19,12, 4,26, 8, 16, 7,27,20,13, 2,
    41,52,31,37,47,55, 30,40,51,45,33,48,
    44,49,39,56,34,53, 46,42,50,36,29,32 };

static const int SHIFT_T[16] = { 1,1,2,2,2,2,2,2,1,2,2,2,2,2,2,1 };

static const u8 SBOX_T[8][64] = {
 { 14, 4,13, 1, 2,15,11, 8, 3,10, 6,12, 5, 9, 0, 7,
    0,15, 7, 4,14, 2,13, 1,10, 6,12,11, 9, 5, 3, 8,
    4, 1,14, 8,13, 6, 2,11,15,12, 9, 7, 3,10, 5, 0,
   15,12, 8, 2, 4, 9, 1, 7, 5,11, 3,14,10, 0, 6,13 },
 { 15, 1, 8,14, 6,11, 3, 4, 9, 7, 2,13,12, 0, 5,10,
    3,13, 4, 7,15, 2, 8,14,12, 0, 1,10, 6, 9,11, 5,
    0,14, 7,11,10, 4,13, 1, 5, 8,12, 6, 9, 3, 2,15,
   13, 8,10, 1, 3,15, 4, 2,11, 6, 7,12, 0, 5,14, 9 },
 { 10, 0, 9,14, 6, 3,15, 5, 1,13,12, 7,11, 4, 2, 8,
   13, 7, 0, 9, 3, 4, 6,10, 2, 8, 5,14,12,11,15, 1,
   13, 6, 4, 9, 8,15, 3, 0,11, 1, 2,12, 5,10,14, 7,
    1,10,13, 0, 6, 9, 8, 7, 4,15,14, 3,11, 5, 2,12 },
 {  7,13,14, 3, 0, 6, 9,10, 1, 2, 8, 5,11,12, 4,15,
   13, 8,11, 5, 6,15, 0, 3, 4, 7, 2,12, 1,10,14, 9,
   10, 6, 9, 0,12,11, 7,13,15, 1, 3,14, 5, 2, 8, 4,
    3,15, 0, 6,10, 1,13, 8, 9, 4, 5,11,12, 7, 2,14 },
 {  2,12, 4, 1, 7,10,11, 6, 8, 5, 3,15,13, 0,14, 9,
   14,11, 2,12, 4, 7,13, 1, 5, 0,15,10, 3, 9, 8, 6,
    4, 2, 1,11,10,13, 7, 8,15, 9,12, 5, 6, 3, 0,14,
   11, 8,12, 7, 1,14, 2,13, 6,15, 0, 9,10, 4, 5, 3 },
 { 12, 1,10,15, 9, 2, 6, 8, 0,13, 3, 4,14, 7, 5,11,
   10,15, 4, 2, 7,12, 9, 5, 6, 1,13,14, 0,11, 3, 8,
    9,14,15, 5, 2, 8,12, 3, 7, 0, 4,10, 1,13,11, 6,
    4, 3, 2,12, 9, 5,15,10,11,14, 1, 7, 6, 0, 8,13 },
 {  4,11, 2,14,15, 0, 8,13, 3,12, 9, 7, 5,10, 6, 1,
   13, 0,11, 7, 4, 9, 1,10,14, 3, 5,12, 2,15, 8, 6,
    1, 4,11,13,12, 3, 7,14,10,15, 6, 8, 0, 5, 9, 2,
    6,11,13, 8, 1, 4,10, 7, 9, 5, 0,15,14, 2, 3,12 },
 { 13, 2, 8, 4, 6,15,11, 1,10, 9, 3,14, 5, 0,12, 7,
    1,15,13, 8,10, 3, 7, 4,12, 5, 6,11, 0,14, 9, 2,
    7,11, 4, 1, 9,12,14, 2, 0, 6,10,13,15, 3, 5, 8,
    2, 1,14, 7, 4,10, 8,13,15,12, 9, 0, 3, 5, 6,11 }
};

/* generic bit permutation: out has n_out bits, in has n_in bits, table is 1-based from MSB */
static u64 permute(u64 in, const int *table, int n_out, int n_in)
{
    u64 out = 0;
    int i;
    for (i = 0; i < n_out; i++)
        out = (out << 1) | ((in >> (n_in - table[i])) & 1ULL);
    return out;
}

static u32 rol28(u32 v, int n) { return ((v << n) | (v >> (28 - n))) & 0x0FFFFFFFu; }
__attribute__((unused)) static u32 ror28(u32 v, int n) { return ((v >> n) | (v << (28 - n))) & 0x0FFFFFFFu; }

/* encryption key schedule: sub[0..15] = K1..K16 (48 bits each) */
static void des_key_schedule(u64 key, u64 sub[16])
{
    u64 cd = permute(key, PC1_T, 56, 64);
    u32 c = (u32)(cd >> 28) & 0x0FFFFFFFu, d = (u32)cd & 0x0FFFFFFFu;
    int i;
    for (i = 0; i < 16; i++) {
        c = rol28(c, SHIFT_T[i]);
        d = rol28(d, SHIFT_T[i]);
        sub[i] = permute(((u64)c << 28) | d, PC2_T, 48, 56);
    }
}

/* the round function f(R, K) */
static u32 des_f(u32 r, u64 k)
{
    u64 x = permute(r, E_T, 48, 32) ^ k;
    u32 out = 0;
    int i;
    for (i = 0; i < 8; i++) {
        int six = (int)((x >> (42 - 6 * i)) & 0x3F);
        int row = ((six & 0x20) >> 4) | (six & 1);
        int col = (six >> 1) & 0xF;
        out = (out << 4) | SBOX_T[i][row * 16 + col];
    }
    return (u32)permute(out, P_T, 32, 32);
}

/* encrypt (or decrypt, using the subkeys in reverse order) one 64-bit block */
static u64 des_block(u64 block, const u64 sub[16], int decrypt)
{
    u64 ip = permute(block, IP_T, 64, 64);
    u32 l = (u32)(ip >> 32), r = (u32)ip;
    int i;
    for (i = 0; i < 16; i++) {
        u64 k = decrypt ? sub[15 - i] : sub[i];
        u32 t = r;
        r = l ^ des_f(r, k);
        l = t;
    }
    return permute(((u64)r << 32) | l, FP_T, 64, 64);      /* pre-output swap R16 L16 */
}

/* convenience: single-key DES */
__attribute__((unused)) static u64 des_encrypt(u64 pt, u64 key)  { u64 s[16]; des_key_schedule(key, s); return des_block(pt, s, 0); }
__attribute__((unused)) static u64 des_decrypt(u64 ct, u64 key)  { u64 s[16]; des_key_schedule(key, s); return des_block(ct, s, 1); }

/* hex helpers */
__attribute__((unused)) static int hex_to_u64(const char *s, u64 *out)
{
    u64 v = 0;
    int n = 0;
    for (; *s; s++) {
        int d;
        if (*s >= '0' && *s <= '9') d = *s - '0';
        else if (*s >= 'a' && *s <= 'f') d = *s - 'a' + 10;
        else if (*s >= 'A' && *s <= 'F') d = *s - 'A' + 10;
        else if (*s == ' ' || *s == '\n' || *s == '\r') continue;
        else return 0;
        v = (v << 4) | (u64)d;
        n++;
    }
    *out = v;
    return n > 0 && n <= 16;
}

__attribute__((unused)) static void print_bits(u64 v, int nbits)
{
    int i;
    for (i = nbits - 1; i >= 0; i--) { putchar('0' + (int)((v >> i) & 1)); if (i % 8 == 0 && i) putchar(' '); }
}
/* ======================== end of DES core ================================ */


static int in_set(const int *set, int n, int v)
{
    int i;
    for (i = 0; i < n; i++) if (set[i] == v) return 1;
    return 0;
}

static void print_set(const char *name, const int *s, int n)
{
    int a[64], i, j;
    memcpy(a, s, sizeof(int) * (size_t)n);
    for (i = 0; i < n; i++)
        for (j = i + 1; j < n; j++) if (a[j] < a[i]) { int t = a[i]; a[i] = a[j]; a[j] = t; }
    printf("  %s (%d bits): ", name, n);
    for (i = 0; i < n; i++) printf("%d ", a[i]);
    printf("\n");
}

int main(void)
{
    int sc[28], sd[28], c[28], d[28], i, j, r, ok = 1;
    int first24[16][24], last24[16][24];

    printf("=========================================\n");
    printf("   STRUCTURE OF THE DES SUBKEYS\n");
    printf("=========================================\n\n");

    /* Step 1-2 : symbolic PC-1; bit k of the key is the symbol k (1..64) */
    for (i = 0; i < 28; i++) { c[i] = sc[i] = PC1_T[i]; d[i] = sd[i] = PC1_T[28 + i]; }

    printf("PC-1 splits the 56 selected key bits into two DISJOINT sets:\n");
    print_set("S_C -> register C", sc, 28);
    print_set("S_D -> register D", sd, 28);
    {
        int overlap = 0, parity[8], np = 0;
        for (i = 0; i < 28; i++) if (in_set(sd, 28, sc[i])) overlap++;
        printf("  Overlap between S_C and S_D : %d bits  %s\n", overlap, overlap == 0 ? "(disjoint)" : "(NOT disjoint!)");
        for (i = 1; i <= 64; i++) if (!in_set(sc, 28, i) && !in_set(sd, 28, i)) parity[np++] = i;
        printf("  Key bits dropped by PC-1    : ");
        for (i = 0; i < np; i++) printf("%d ", parity[i]);
        printf(" (the 8 parity bits)\n");
    }

    /* Step 3 : run the schedule symbolically */
    printf("\nPer-round check (symbols = original key-bit numbers)\n");
    for (r = 0; r < 16; r++) {
        int tmp[28], k;
        for (k = 0; k < SHIFT_T[r]; k++) {         /* rotate C and D left, one bit at a time */
            int t = c[0]; memmove(c, c + 1, 27 * sizeof(int)); c[27] = t;
            t = d[0];     memmove(d, d + 1, 27 * sizeof(int)); d[27] = t;
        }
        (void)tmp;
        for (i = 0; i < 48; i++) {
            int pos = PC2_T[i] - 1;                 /* 0..55 : 0..27 in C, 28..55 in D */
            int origin = pos < 28 ? c[pos] : d[pos - 28];
            if (i < 24) first24[r][i] = origin; else last24[r][i - 24] = origin;
        }
        {
            int fok = 1, lok = 1;
            for (i = 0; i < 24; i++) {
                if (!in_set(sc, 28, first24[r][i])) fok = 0;
                if (!in_set(sd, 28, last24[r][i]))  lok = 0;
            }
            ok &= fok && lok;
            printf("  K%-2d  first 24 bits from S_C: %s   last 24 bits from S_D: %s\n", r + 1,
                   fok ? "YES" : "NO ", lok ? "YES" : "NO ");
        }
    }

    printf("\nKey bits that make up K1 (in output order):\n  first 24: ");
    for (i = 0; i < 24; i++) printf("%d ", first24[0][i]);
    printf("\n  last 24 : ");
    for (i = 0; i < 24; i++) printf("%d ", last24[0][i]);
    printf("\n");

    /* PC-2 discards 4 bits from each register */
    printf("\nBits of each register that PC-2 never uses (positions in the 56-bit CD):\n  C: ");
    for (i = 1; i <= 28; i++) { int used = 0; for (j = 0; j < 48; j++) if (PC2_T[j] == i) used = 1; if (!used) printf("%d ", i); }
    printf("\n  D: ");
    for (i = 29; i <= 56; i++) { int used = 0; for (j = 0; j < 48; j++) if (PC2_T[j] == i) used = 1; if (!used) printf("%d ", i); }
    printf("\n  (24 of the 28 bits of each register reach every subkey; the 4 left out change from round to round after rotation.)\n");

    /* Step 5 : empirical bit-flip test */
    printf("\nEmpirical test: flip one key bit and see which half of the subkeys changes\n");
    {
        u64 key = 0x133457799BBCDFF1ULL, sub0[16], sub1[16];
        int probe[2] = { sc[3], sd[3] }, p;
        des_key_schedule(key, sub0);
        for (p = 0; p < 2; p++) {
            int firstchg = 0, lastchg = 0;
            u64 k2 = key ^ (1ULL << (64 - probe[p]));
            des_key_schedule(k2, sub1);
            for (r = 0; r < 16; r++) {
                u64 diff = sub0[r] ^ sub1[r];
                if (diff >> 24) firstchg++;
                if (diff & 0xFFFFFFULL) lastchg++;
            }
            printf("  flip key bit %2d (in %s): changes first-half of %2d subkeys, last-half of %2d subkeys\n",
                   probe[p], p == 0 ? "S_C" : "S_D", firstchg, lastchg);
        }
    }

    printf("\nCONCLUSION: %s\n", ok ? "Verified - the first 24 bits of every subkey depend only on the 28 key bits in S_C,\n"
                                     "            the last 24 bits only on the 28 disjoint key bits in S_D."
                                   : "claim NOT verified");
    return !ok;
}
