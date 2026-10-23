/*
 * ============================================================================
 *  EXPERIMENT 19 : CBC ENCRYPTION WITH TRIPLE DES  (outer-CBC vs inner-CBC)
 * ============================================================================
 *  Aim
 *  ---
 *  Implement encryption in the cipher block chaining (CBC) mode using an
 *  algorithm stronger than DES - 3DES is a good candidate.  There are two
 *  ways of combining 3DES with CBC, both of which follow from the definition
 *  of CBC (here K1,K2,K3 are the three DES keys, E = encrypt, D = decrypt):
 *
 *   OUTER-CBC  (chain around the whole 3DES box - one IV)
 *        C_i = E_K3( D_K2( E_K1( P_i  XOR  C_(i-1) ) ) )         C_0 = IV
 *
 *   INNER-CBC  (three separate CBC passes over the whole message, 3 IVs)
 *        pass 1 : CBC-encrypt  with K1, IV1   -> X
 *        pass 2 : CBC-decrypt  with K2, IV2   -> Y
 *        pass 3 : CBC-encrypt  with K3, IV3   -> C
 *
 *  Which would you choose
 *   a. FOR SECURITY?   OUTER-CBC.  Inner chaining has three independent
 *      feedback loops, which gives an attacker extra structure to exploit
 *      (Biham's analysis of multiple modes of operation shows inner-chained
 *      modes are weaker than the single outer feedback loop, which keeps the
 *      full 3DES strength).  Outer-CBC is also the standard (SP 800-67,
 *      ANSI X9.52 "3DES-CBC").
 *   b. FOR PERFORMANCE?  INNER-CBC.  In outer-CBC block i cannot start until
 *      block i-1 has finished ALL three DES operations, so the three DES
 *      units cannot overlap.  In inner-CBC the three passes are independent
 *      loops, so in hardware they run as a 3-stage PIPELINE: after the pipe
 *      fills, one block is completed per DES time instead of per 3 DES times
 *      (about 3x throughput).  Outer-CBC cannot be pipelined or parallelised
 *      on a single message.
 *
 *  What the program does
 *   - implements 3DES (EDE, three keys) from the DES core
 *   - encrypts / decrypts a message with BOTH arrangements and checks the
 *     round trip
 *   - counts the DES operations on the critical path for n blocks to show the
 *     pipeline advantage numerically
 *   - shows that the two modes give different ciphertexts for the same keys
 *
 *  Compile :  gcc 19_3des_cbc.c -o tdes_cbc
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


#define MAXBLK 64

typedef struct { u64 k1[16], k2[16], k3[16]; } Tdes;

static void tdes_init(Tdes *t, u64 a, u64 b, u64 c)
{
    des_key_schedule(a, t->k1);
    des_key_schedule(b, t->k2);
    des_key_schedule(c, t->k3);
}

static u64 tdes_enc(const Tdes *t, u64 x) { return des_block(des_block(des_block(x, t->k1, 0), t->k2, 1), t->k3, 0); }
static u64 tdes_dec(const Tdes *t, u64 x) { return des_block(des_block(des_block(x, t->k3, 1), t->k2, 0), t->k1, 1); }

/* ---- OUTER CBC ---- */
static void outer_enc(const Tdes *t, u64 iv, const u64 *p, u64 *c, int n)
{
    u64 prev = iv; int i;
    for (i = 0; i < n; i++) { c[i] = tdes_enc(t, p[i] ^ prev); prev = c[i]; }
}
static void outer_dec(const Tdes *t, u64 iv, const u64 *c, u64 *p, int n)
{
    u64 prev = iv; int i;
    for (i = 0; i < n; i++) { p[i] = tdes_dec(t, c[i]) ^ prev; prev = c[i]; }
}

/* ---- single-DES CBC passes (used by INNER CBC) ---- */
static void cbc_e(const u64 *sub, u64 iv, const u64 *in, u64 *out, int n)
{
    u64 prev = iv; int i;
    for (i = 0; i < n; i++) { out[i] = des_block(in[i] ^ prev, sub, 0); prev = out[i]; }
}
static void cbc_d(const u64 *sub, u64 iv, const u64 *in, u64 *out, int n)
{
    u64 prev = iv; int i;
    for (i = 0; i < n; i++) { out[i] = des_block(in[i], sub, 1) ^ prev; prev = in[i]; }
}

/* ---- INNER CBC ---- */
static void inner_enc(const Tdes *t, const u64 iv[3], const u64 *p, u64 *c, int n)
{
    u64 x[MAXBLK], y[MAXBLK];
    cbc_e(t->k1, iv[0], p, x, n);      /* pass 1: encrypt     */
    cbc_d(t->k2, iv[1], x, y, n);      /* pass 2: decrypt     */
    cbc_e(t->k3, iv[2], y, c, n);      /* pass 3: encrypt     */
}
static void inner_dec(const Tdes *t, const u64 iv[3], const u64 *c, u64 *p, int n)
{
    u64 x[MAXBLK], y[MAXBLK];
    cbc_d(t->k3, iv[2], c, y, n);      /* undo pass 3         */
    cbc_e(t->k2, iv[1], y, x, n);      /* undo pass 2 (CBC-decrypt is undone by CBC-encrypt) */
    cbc_d(t->k1, iv[0], x, p, n);      /* undo pass 1         */
}

static void show_blocks(const char *label, const u64 *v, int n)
{
    int i;
    printf("  %-14s", label);
    for (i = 0; i < n; i++) printf("%016llX ", v[i]);
    printf("\n");
}

int main(void)
{
    const char *msg = "TRIPLE DES in CBC mode: outer chaining versus inner chaining. ";
    u64 p[MAXBLK], c1[MAXBLK], c2[MAXBLK], d1[MAXBLK], d2[MAXBLK];
    u64 K1 = 0x0123456789ABCDEFULL, K2 = 0x23456789ABCDEF01ULL, K3 = 0x456789ABCDEF0123ULL;
    u64 iv = 0x1234567890ABCDEFULL, ivs[3] = { 0x1111111111111111ULL, 0x2222222222222222ULL, 0x3333333333333333ULL };
    int len = (int)strlen(msg), n = (len + 7) / 8, i, j;
    unsigned char buf[MAXBLK * 8];
    Tdes t;

    printf("=========================================\n");
    printf("   3DES IN CBC MODE : OUTER vs INNER\n");
    printf("=========================================\n");

    memset(buf, ' ', sizeof buf);
    memcpy(buf, msg, (size_t)len);
    for (i = 0; i < n; i++) { p[i] = 0; for (j = 0; j < 8; j++) p[i] = (p[i] << 8) | buf[i * 8 + j]; }

    tdes_init(&t, K1, K2, K3);
    printf("\nKeys: K1=%016llX K2=%016llX K3=%016llX\n", K1, K2, K3);
    printf("Message (%d bytes, %d blocks, space padded):\n  \"%s\"\n\n", len, n, msg);

    /* sanity: 3DES with K1=K2=K3 equals single DES */
    {
        Tdes s; u64 x = 0x0123456789ABCDEFULL;
        tdes_init(&s, 0x133457799BBCDFF1ULL, 0x133457799BBCDFF1ULL, 0x133457799BBCDFF1ULL);
        printf("Check: 3DES with K1=K2=K3 reduces to DES: %016llX (expected 85E813540F0AB405)\n\n", tdes_enc(&s, x));
    }

    outer_enc(&t, iv, p, c1, n);
    inner_enc(&t, ivs, p, c2, n);
    show_blocks("plaintext", p, n);
    show_blocks("OUTER-CBC C", c1, n);
    show_blocks("INNER-CBC C", c2, n);

    outer_dec(&t, iv, c1, d1, n);
    inner_dec(&t, ivs, c2, d2, n);
    printf("\n  OUTER-CBC decrypts correctly: %s\n", memcmp(p, d1, (size_t)n * 8) == 0 ? "YES" : "NO");
    printf("  INNER-CBC decrypts correctly: %s\n", memcmp(p, d2, (size_t)n * 8) == 0 ? "YES" : "NO");

    printf("\nPerformance model - DES operations on the critical path for n blocks\n");
    printf("  (3 DES units available in hardware, one DES operation = 1 time unit)\n\n");
    printf("   blocks | OUTER-CBC (3n) | INNER-CBC pipelined (n+2) | speed-up\n");
    printf("   -------+----------------+---------------------------+---------\n");
    {
        int sizes[5] = { 1, 4, 16, 64, 1024 };
        for (i = 0; i < 5; i++)
            printf("   %6d |     %6d     |          %6d           |  %.2fx\n", sizes[i], 3 * sizes[i],
                   sizes[i] + 2, 3.0 * sizes[i] / (sizes[i] + 2));
    }
    printf("\nCHOICE:  a. security -> OUTER-CBC      b. performance -> INNER-CBC\n");
    return 0;
}
