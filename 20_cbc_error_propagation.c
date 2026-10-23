/*
 * ============================================================================
 *  EXPERIMENT 20 : ERROR PROPAGATION IN ECB AND CBC MODES
 * ============================================================================
 *  Aim
 *  ---
 *  In ECB mode, if there is an error in a block of the transmitted ciphertext,
 *  only the corresponding plaintext block is affected.  However, in CBC mode
 *  this error propagates.  For example, an error in the transmitted C1
 *  obviously corrupts P1 and P2.
 *    a. Are any blocks beyond P2 affected?
 *    b. Suppose there is a bit error in the source version of P1.  Through how
 *       many ciphertext blocks is this error propagated?  What is the effect
 *       at the receiver?
 *
 *  Theory
 *  ------
 *  CBC:  C_i = E_K(P_i XOR C_(i-1)),  C_0 = IV        P_i = D_K(C_i) XOR C_(i-1)
 *
 *  a. P3 = D_K(C3) XOR C2 uses only C3 and C2, neither of which contains the
 *     error in C1.  So NO block beyond P2 is affected: the error damages
 *     exactly two plaintext blocks - P1 (completely garbled: D_K of a wrong
 *     block) and P2 (only the SAME bit position as the transmission error is
 *     flipped, because P2 = D_K(C2) XOR C1).  CBC is "self-synchronising".
 *
 *  b. An error in the SOURCE P1 changes C1 = E_K(P1 XOR IV); since C1 is the
 *     chaining value, C2 = E_K(P2 XOR C1) also changes, then C3, ... so the
 *     error propagates through ALL the following ciphertext blocks (the
 *     whole rest of the message is different).  At the receiver, however,
 *     the (valid) ciphertext decrypts correctly: P_i = D_K(C_i) XOR C_(i-1)
 *     reproduces exactly what the sender encrypted, so only P1 contains the
 *     bit error - the receiver gets the source message, error and nothing
 *     else.  The error does not spread at the receiver.
 *
 *  The program uses DES in ECB and CBC mode on an 8-block message, injects
 *  errors and prints which plaintext / ciphertext blocks differ.
 *
 *  Compile :  gcc 20_cbc_error_propagation.c -o error_prop
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


#define NB 8                                          /* number of blocks */

static void ecb_enc(const u64 *p, u64 *c, int n, const u64 *sub)
{ int i; for (i = 0; i < n; i++) c[i] = des_block(p[i], sub, 0); }
static void ecb_dec(const u64 *c, u64 *p, int n, const u64 *sub)
{ int i; for (i = 0; i < n; i++) p[i] = des_block(c[i], sub, 1); }

static void cbc_enc(const u64 *p, u64 *c, int n, const u64 *sub, u64 iv)
{ int i; u64 prev = iv; for (i = 0; i < n; i++) { c[i] = des_block(p[i] ^ prev, sub, 0); prev = c[i]; } }
static void cbc_dec(const u64 *c, u64 *p, int n, const u64 *sub, u64 iv)
{ int i; u64 prev = iv; for (i = 0; i < n; i++) { p[i] = des_block(c[i], sub, 1) ^ prev; prev = c[i]; } }

static int popcount64(u64 v) { int n = 0; while (v) { n += (int)(v & 1); v >>= 1; } return n; }

static void report(const char *title, const u64 *ref, const u64 *got, int n)
{
    int i;
    printf("  %-34s : ", title);
    for (i = 0; i < n; i++) {
        int d = popcount64(ref[i] ^ got[i]);
        if (d == 0) printf("  .  ");
        else        printf("%2db  ", d);
    }
    printf("\n");
}

static void header(const char *what)
{
    int i;
    printf("\n  (%s)  columns = block 1..%d, '.' = identical, 'Nb' = N bits differ\n  %-34s : ", what, NB, "");
    for (i = 0; i < NB; i++) printf("  %d  ", i + 1);
    printf("\n");
}

int main(void)
{
    u64 key = 0x133457799BBCDFF1ULL, iv = 0xA5A5A5A5A5A5A5A5ULL, sub[16];
    u64 P[NB], C[NB], Cerr[NB], Pout[NB], P1err[NB], C1err[NB], Pdec[NB];
    int i;

    des_key_schedule(key, sub);
    for (i = 0; i < NB; i++) P[i] = 0x1111111111111111ULL * (u64)(i + 1) ^ 0x0F0F0F0F0F0F0F0FULL;

    printf("=========================================\n");
    printf("   ERROR PROPAGATION: ECB vs CBC (DES)\n");
    printf("=========================================\n");

    printf("\nPART 0 - one bit error in TRANSMITTED ciphertext block C1\n");
    /* ---- ECB ------------------------------------------------------------ */
    ecb_enc(P, C, NB, sub);
    memcpy(Cerr, C, sizeof C);
    Cerr[0] ^= 1ULL << 20;
    ecb_dec(Cerr, Pout, NB, sub);
    header("ECB");
    report("ECB: plaintext blocks damaged", P, Pout, NB);

    /* ---- CBC ------------------------------------------------------------ */
    cbc_enc(P, C, NB, sub, iv);
    memcpy(Cerr, C, sizeof C);
    Cerr[0] ^= 1ULL << 20;
    cbc_dec(Cerr, Pout, NB, sub, iv);
    header("CBC");
    report("CBC: plaintext blocks damaged", P, Pout, NB);
    printf("\n  P1 is garbled (roughly half of its 64 bits are wrong - DES avalanche effect);\n"
           "  P2 has exactly ONE bit wrong\n"
           "  (the same position as the transmission error, bit 21 from the right);\n"
           "  P3...P%d are correct.\n", NB);
    printf("\n  a. Are any blocks beyond P2 affected?   ANSWER: NO - only P1 and P2.\n");
    printf("     P2 differs from P2' by XOR with the error pattern: %016llX\n", P[1] ^ Pout[1]);

    printf("\n--------------------------------------------------------------------\n");
    printf("PART b - one bit error in the SOURCE plaintext block P1 (before encryption)\n");
    memcpy(P1err, P, sizeof P);
    P1err[0] ^= 1ULL << 40;
    cbc_enc(P, C, NB, sub, iv);
    cbc_enc(P1err, C1err, NB, sub, iv);
    header("CBC ciphertext");
    report("ciphertext blocks that change", C, C1err, NB);
    cbc_dec(C1err, Pdec, NB, sub, iv);
    header("receiver output vs intended message");
    report("receiver plaintext vs original P", P, Pdec, NB);
    printf("\n  b. The source error propagates through ALL %d ciphertext blocks (C1...C%d).\n", NB, NB);
    printf("     At the receiver every block decrypts correctly to what was ENCRYPTED, so the\n"
           "     only visible effect is the single original bit error in P1 (%016llX vs %016llX);\n"
           "     P2...P%d are recovered exactly.\n", P[0], Pdec[0], NB);
    {
        int clean = 1;
        for (i = 1; i < NB; i++) if (Pdec[i] != P[i]) clean = 0;
        printf("     Check: P2..P%d identical to the original = %s\n", NB, clean ? "YES" : "NO");
    }
    return 0;
}
