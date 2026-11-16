/*
 * ============================================================================
 *  EXPERIMENT 31 : SUBKEY GENERATION IN CMAC
 * ============================================================================
 *  Aim
 *  ---
 *  In CMAC subkey generation the block cipher is applied to a block consisting
 *  entirely of 0 bits.  The first subkey K1 is derived from the resulting string
 *  by a left shift of one bit and, conditionally, by XORing a constant that
 *  depends on the block size.  The second subkey K2 is derived in the same way
 *  from the first subkey.
 *     a. What constants are needed for block sizes of 64 and 128 bits?
 *     b. How does the left shift and XOR accomplish the desired result?
 *
 *  Algorithm (NIST SP 800-38B)
 *  ---------------------------
 *     L  = E_K( 0^b )
 *     K1 = L << 1                  if MSB(L)  = 0
 *        = (L << 1) XOR Rb         if MSB(L)  = 1
 *     K2 = K1 << 1                 if MSB(K1) = 0
 *        = (K1 << 1) XOR Rb        if MSB(K1) = 1
 *
 *  ANSWER (a) : Rb = 0x1B  (binary 0001 1011) for 64-bit blocks   (b = 64)
 *               Rb = 0x87  (binary 1000 0111) for 128-bit blocks  (b = 128)
 *     They are the lower-order terms of the lexicographically first irreducible
 *     polynomial of degree b with the minimum number of non-zero terms:
 *        b = 64 :  x^64  + x^4 + x^3 + x + 1      -> 0x1B  (bits 4,3,1,0)
 *        b = 128:  x^128 + x^7 + x^2 + x + 1      -> 0x87  (bits 7,2,1,0)
 *
 *  ANSWER (b) : Treat a b-bit string as a polynomial of degree < b over GF(2)
 *     (the leftmost bit is the coefficient of x^(b-1)).  Then
 *       - a one-bit LEFT SHIFT multiplies the polynomial by x
 *       - if the leftmost bit was 1 the product has a term x^b, which is outside
 *         the field GF(2^b).  Because the polynomial p(x) = x^b + r(x) is
 *         irreducible and p(x) = 0 in the field,  x^b = r(x), where r(x) is the
 *         low-order part = the constant Rb.  Replacing x^b by r(x) means
 *         dropping the shifted-out bit and XORing Rb.
 *     So  K1 = L * x   and   K2 = K1 * x = L * x^2   (multiplication in GF(2^b)).
 *     Multiplying by x (and x^2) gives subkeys that are distinct from each other and
 *     from L, yet derived from the secret key by a fast, invertible, linear map -
 *     used to separate "complete last block" (K1) from "padded last block" (K2).
 *
 *  Program
 *   1. derives Rb from the polynomials (a)
 *   2. shows the shift-and-XOR on a worked example and checks it against
 *      explicit polynomial arithmetic modulo p(x) on thousands of random values (b)
 *   3. generates subkeys for AES-128 (b = 128) and DES (b = 64)
 *   4. checks the AES subkeys against RFC 4493 and computes full CMAC tags,
 *      checking the four RFC 4493 test vectors
 *
 *  Compile :  gcc 31_cmac_subkeys.c -o cmac_subkeys
 * ============================================================================
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <time.h>

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

/* ======================================================================== */
/*  AES-128 CORE (FIPS-197) - encryption only, S-box generated at start-up  */
/*  state byte order is the same as the input byte order (column major)     */
/* ======================================================================== */
static u8 AES_SBOX[256];

static u8 aes_rotl8(u8 x, int s) { return (u8)((x << s) | (x >> (8 - s))); }
static u8 aes_xtime(u8 x) { return (u8)((x << 1) ^ ((x & 0x80) ? 0x1B : 0)); }

static void aes_init(void)
{
    u8 p = 1, q = 1;
    do {
        p = (u8)(p ^ (p << 1) ^ ((p & 0x80) ? 0x1B : 0));            /* p *= 3 in GF(2^8) */
        q ^= (u8)(q << 1); q ^= (u8)(q << 2); q ^= (u8)(q << 4);     /* q /= 3 */
        if (q & 0x80) q ^= 0x09;
        AES_SBOX[p] = (u8)(q ^ aes_rotl8(q, 1) ^ aes_rotl8(q, 2) ^ aes_rotl8(q, 3) ^ aes_rotl8(q, 4) ^ 0x63);
    } while (p != 1);
    AES_SBOX[0] = 0x63;
}

static void aes128_expand(const u8 key[16], u8 rk[176])
{
    static const u8 rcon[10] = {0x01,0x02,0x04,0x08,0x10,0x20,0x40,0x80,0x1B,0x36};
    int i;
    memcpy(rk, key, 16);
    for (i = 16; i < 176; i += 4) {
        u8 t[4];
        memcpy(t, rk + i - 4, 4);
        if (i % 16 == 0) {
            u8 tmp = t[0];
            t[0] = (u8)(AES_SBOX[t[1]] ^ rcon[i / 16 - 1]);
            t[1] = AES_SBOX[t[2]]; t[2] = AES_SBOX[t[3]]; t[3] = AES_SBOX[tmp];
        }
        rk[i] = rk[i - 16] ^ t[0]; rk[i + 1] = rk[i - 15] ^ t[1];
        rk[i + 2] = rk[i - 14] ^ t[2]; rk[i + 3] = rk[i - 13] ^ t[3];
    }
}

static void aes128_encrypt(const u8 rk[176], const u8 in[16], u8 out[16])
{
    u8 s[16], t[16];
    int r, i, c;
    for (i = 0; i < 16; i++) s[i] = in[i] ^ rk[i];
    for (r = 1; r <= 10; r++) {
        for (i = 0; i < 16; i++) t[i] = AES_SBOX[s[i]];                 /* SubBytes */
        for (c = 0; c < 4; c++)                                          /* ShiftRows */
            for (i = 0; i < 4; i++) s[4 * c + i] = t[4 * ((c + i) % 4) + i];
        if (r != 10) {
            for (c = 0; c < 4; c++) {                                    /* MixColumns */
                u8 a0 = s[4*c], a1 = s[4*c+1], a2 = s[4*c+2], a3 = s[4*c+3];
                s[4*c]   = (u8)(aes_xtime(a0) ^ (aes_xtime(a1) ^ a1) ^ a2 ^ a3);
                s[4*c+1] = (u8)(a0 ^ aes_xtime(a1) ^ (aes_xtime(a2) ^ a2) ^ a3);
                s[4*c+2] = (u8)(a0 ^ a1 ^ aes_xtime(a2) ^ (aes_xtime(a3) ^ a3));
                s[4*c+3] = (u8)((aes_xtime(a0) ^ a0) ^ a1 ^ a2 ^ aes_xtime(a3));
            }
        }
        for (i = 0; i < 16; i++) s[i] ^= rk[16 * r + i];                 /* AddRoundKey */
    }
    memcpy(out, s, 16);
}
/* ============================ end of AES core ============================= */


static void read_line(const char *prompt, char *buf, size_t n)
{
    printf("%s", prompt);
    fflush(stdout);
    if (!fgets(buf, (int)n, stdin)) { printf("\n"); exit(0); }
    buf[strcspn(buf, "\r\n")] = '\0';
}

static void phex(const char *label, const u8 *d, int n)
{
    int i;
    printf("%s", label);
    for (i = 0; i < n; i++) printf("%02X", d[i]);
    putchar('\n');
}

static void pbin(const u8 *d, int n)
{
    int i, b;
    for (i = 0; i < n; i++) { for (b = 7; b >= 0; b--) putchar('0' + ((d[i] >> b) & 1)); putchar(' '); }
}

static int parse_hex(const char *s, u8 *out, int max)
{
    int n = 0, nib = 0, i;
    u8 cur = 0;
    for (i = 0; s[i]; i++) {
        int d;
        if (s[i] == ' ') continue;
        if (isdigit((unsigned char)s[i])) d = s[i] - '0';
        else if (isxdigit((unsigned char)s[i])) d = tolower((unsigned char)s[i]) - 'a' + 10;
        else return -1;
        cur = (u8)((cur << 4) | d);
        if (++nib % 2 == 0) { if (n >= max) return -1; out[n++] = cur; cur = 0; }
    }
    return nib % 2 ? -1 : n;
}

/* --------------- doubling in GF(2^b) : two independent methods --------------- */

/* Method 1: shift and conditional XOR (what CMAC specifies) */
static void dbl_shift(const u8 *in, u8 *out, int bs, u8 rb)
{
    int i, msb = in[0] >> 7;
    for (i = 0; i < bs; i++) out[i] = (u8)((in[i] << 1) | (i + 1 < bs ? in[i + 1] >> 7 : 0));
    if (msb) out[bs - 1] ^= rb;
}

/* Method 2: explicit polynomial arithmetic.  coefficient c[i] of x^i is bit i (bit b-1 = MSB of byte 0).
   Multiply by x, then replace x^b by the low terms of the irreducible polynomial. */
static void dbl_poly(const u8 *in, u8 *out, int bs, const int *low, int nlow)
{
    int b = bs * 8, i, j, c[129], nc[129], top;
    for (i = 0; i < b; i++) c[i] = (in[bs - 1 - i / 8] >> (i % 8)) & 1;
    for (i = 0; i < b; i++) nc[i] = 0;
    for (i = 0; i + 1 < b; i++) nc[i + 1] = c[i];                 /* multiply by x */
    top = c[b - 1];                                               /* coefficient of x^b */
    if (top) for (j = 0; j < nlow; j++) nc[low[j]] ^= 1;          /* x^b = x^e1 + x^e2 + ... + 1 */
    for (i = 0; i < bs; i++) out[i] = 0;
    for (i = 0; i < b; i++) if (nc[i]) out[bs - 1 - i / 8] |= (u8)(1 << (i % 8));
}

static void subkeys(const u8 *L, int bs, u8 rb, u8 *k1, u8 *k2)
{
    dbl_shift(L, k1, bs, rb);
    dbl_shift(k1, k2, bs, rb);
}

/* -------------------------------- CMAC --------------------------------------- */
typedef void (*enc_fn)(const void *ctx, const u8 *in, u8 *out);

static void aes_enc(const void *ctx, const u8 *in, u8 *out) { aes128_encrypt((const u8 *)ctx, in, out); }
static void des_enc(const void *ctx, const u8 *in, u8 *out)
{
    u64 v = 0; int i;
    for (i = 0; i < 8; i++) v = (v << 8) | in[i];
    v = des_block(v, (const u64 *)ctx, 0);
    for (i = 7; i >= 0; i--) { out[i] = (u8)(v & 255); v >>= 8; }
}

static void cmac(enc_fn E, const void *ctx, int bs, u8 rb, const u8 *m, int len, u8 *tag)
{
    u8 zero[16] = {0}, L[16], k1[16], k2[16], x[16] = {0}, y[16], last[16];
    int n = (len + bs - 1) / bs, i, j, complete;
    E(ctx, zero, L);
    subkeys(L, bs, rb, k1, k2);
    if (n == 0) { n = 1; complete = 0; } else complete = (len % bs == 0);
    for (i = 0; i < n - 1; i++) {
        for (j = 0; j < bs; j++) y[j] = x[j] ^ m[i * bs + j];
        E(ctx, y, x);
    }
    if (complete) { for (j = 0; j < bs; j++) last[j] = m[(n - 1) * bs + j] ^ k1[j]; }
    else {
        int rem = len - (n - 1) * bs;
        for (j = 0; j < bs; j++) last[j] = (j < rem) ? m[(n - 1) * bs + j] : (j == rem ? 0x80 : 0x00);
        for (j = 0; j < bs; j++) last[j] ^= k2[j];
    }
    for (j = 0; j < bs; j++) y[j] = x[j] ^ last[j];
    E(ctx, y, tag);
}

int main(void)
{
    static const int POLY64[]  = {4, 3, 1, 0};
    static const int POLY128[] = {7, 2, 1, 0};
    u8 rk[176], key[16] = {0x2b,0x7e,0x15,0x16,0x28,0xae,0xd2,0xa6,0xab,0xf7,0x15,0x88,0x09,0xcf,0x4f,0x3c};
    u8 zero[16] = {0}, L[16], k1[16], k2[16], p1[16], p2[16], tag[16];
    u8 msg[64] = {0x6b,0xc1,0xbe,0xe2,0x2e,0x40,0x9f,0x96,0xe9,0x3d,0x7e,0x11,0x73,0x93,0x17,0x2a,
                  0xae,0x2d,0x8a,0x57,0x1e,0x03,0xac,0x9c,0x9e,0xb7,0x6f,0xac,0x45,0xaf,0x8e,0x51,
                  0x30,0xc8,0x1c,0x46,0xa3,0x5c,0xe4,0x11,0xe5,0xfb,0xc1,0x19,0x1a,0x0a,0x52,0xef,
                  0xf6,0x9f,0x24,0x45,0xdf,0x4f,0x9b,0x17,0xad,0x2b,0x41,0x7b,0xe6,0x6c,0x37,0x10};
    static const int LENS[4] = {0, 16, 40, 64};
    static const char *WANT[4] = {"BB1D6929E95937287FA37D129B756746", "070A16B46B4D4144F79BDD9DD04A287C",
                                  "DFA66747DE9AE63030CA32611497C827", "51F0BEBF7E3B9D92FC49741779363CFE"};
    int i, t, rb64 = 0, rb128 = 0, all = 1, agree = 0, trials = 5000;

    aes_init();
    srand((unsigned)time(NULL));
    printf("=========================================\n");
    printf("   CMAC SUBKEY GENERATION (K1, K2)\n");
    printf("=========================================\n");

    /* ----------------------------- (a) constants ---------------------------- */
    printf("\n(a) CONSTANTS Rb\n");
    for (i = 0; i < 4; i++) rb64 |= 1 << POLY64[i];
    for (i = 0; i < 4; i++) rb128 |= 1 << POLY128[i];
    printf("   b = 64  : p(x) = x^64  + x^4 + x^3 + x + 1   ->  Rb = ");
    for (i = 7; i >= 0; i--) putchar('0' + ((rb64 >> i) & 1));
    printf(" = 0x%02X\n", rb64);
    printf("   b = 128 : p(x) = x^128 + x^7 + x^2 + x + 1   ->  Rb = ");
    for (i = 7; i >= 0; i--) putchar('0' + ((rb128 >> i) & 1));
    printf(" = 0x%02X\n", rb128);
    printf("   (Rb is the polynomial p(x) with its leading x^b term removed.)\n");

    /* ----------------------------- (b) worked example ---------------------------- */
    aes128_expand(key, rk);
    aes128_encrypt(rk, zero, L);
    printf("\n(b) HOW SHIFT-AND-XOR WORKS  -  worked example, AES-128 key 2B7E1516 28AED2A6 ABF71588 09CF4F3C\n");
    phex("   L  = E_K(0^128)      = ", L, 16);
    printf("   MSB(L) = %d\n", L[0] >> 7);
    dbl_shift(L, k1, 16, 0x00);
    phex("   L << 1               = ", k1, 16);
    subkeys(L, 16, 0x87, k1, k2);
    if (L[0] >> 7) printf("   MSB(L) = 1  -> K1 = (L << 1) XOR 0x87 :\n");
    else           printf("   MSB(L) = 0  -> no XOR is needed, K1 = L << 1 :\n");
    phex("   K1                   = ", k1, 16);
    if (k1[0] >> 7) printf("   MSB(K1) = 1 -> K2 = (K1 << 1) XOR 0x87 :\n");
    else            printf("   MSB(K1) = 0 -> K2 = K1 << 1 :\n");
    phex("   K2                   = ", k2, 16);
    printf("   RFC 4493 expected:  K1 = FBEED618357133667C85E08F7236A8DE   K2 = F7DDAC306AE266CCF90BC11EE46D513B\n");
    printf("   %s\n", (!memcmp(k1, "\xFB\xEE\xD6\x18\x35\x71\x33\x66\x7C\x85\xE0\x8F\x72\x36\xA8\xDE", 16) &&
                       !memcmp(k2, "\xF7\xDD\xAC\x30\x6A\xE2\x66\xCC\xF9\x0B\xC1\x1E\xE4\x6D\x51\x3B", 16)) ? "[PASS] subkeys match RFC 4493" : "[FAIL]");

    printf("\n   Same operation done as explicit polynomial arithmetic in GF(2^128):\n"
           "      L(x) * x  =  x*L(x) with the x^128 term replaced by x^7 + x^2 + x + 1\n");
    dbl_poly(L, p1, 16, POLY128, 4);
    dbl_poly(p1, p2, 16, POLY128, 4);
    phex("   K1 (polynomial method) = ", p1, 16);
    phex("   K2 (polynomial method) = ", p2, 16);
    printf("   identical to the shift/XOR result: %s\n", (!memcmp(p1, k1, 16) && !memcmp(p2, k2, 16)) ? "YES" : "NO");

    printf("\n   Random test: shift/XOR vs polynomial multiplication by x in GF(2^b), %d values each\n", trials);
    for (t = 0, agree = 0; t < trials; t++) {
        u8 a[16], s[16], q[16];
        for (i = 0; i < 16; i++) a[i] = (u8)(rand() & 255);
        dbl_shift(a, s, 16, 0x87); dbl_poly(a, q, 16, POLY128, 4);
        if (!memcmp(s, q, 16)) agree++;
    }
    printf("      b = 128, Rb = 0x87 : agree on %d / %d\n", agree, trials);
    for (t = 0, agree = 0; t < trials; t++) {
        u8 a[8], s[8], q[8];
        for (i = 0; i < 8; i++) a[i] = (u8)(rand() & 255);
        dbl_shift(a, s, 8, 0x1B); dbl_poly(a, q, 8, POLY64, 4);
        if (!memcmp(s, q, 8)) agree++;
    }
    printf("      b =  64, Rb = 0x1B : agree on %d / %d\n", agree, trials);
    printf("   => a left shift multiplies by x; the XOR with Rb folds the overflow bit x^b back into the field.\n");

    /* ----------------------------- DES (64-bit) -------------------------------- */
    {
        u64 dsub[16], dk = 0x133457799BBCDFF1ULL;
        u8 dz[8] = {0}, dL[8], d1[8], d2[8];
        des_key_schedule(dk, dsub);
        des_enc(dsub, dz, dL);
        subkeys(dL, 8, 0x1B, d1, d2);
        printf("\nSubkeys for a 64-bit block cipher (DES, key 133457799BBCDFF1), Rb = 0x1B:\n");
        phex("   L  = E_K(0^64) = ", dL, 8);
        phex("   K1             = ", d1, 8);
        phex("   K2             = ", d2, 8);
        printf("   L  = "); pbin(dL, 8); printf("\n   K1 = "); pbin(d1, 8); printf("\n   K2 = "); pbin(d2, 8); printf("\n");
    }

    /* ----------------------------- RFC 4493 tags -------------------------------- */
    printf("\nFULL CMAC-AES-128 TEST VECTORS (RFC 4493)\n  len | tag                              | expected                         |\n");
    for (i = 0; i < 4; i++) {
        char got[40]; int j;
        cmac(aes_enc, rk, 16, 0x87, msg, LENS[i], tag);
        for (j = 0; j < 16; j++) sprintf(got + 2 * j, "%02X", tag[j]);
        printf("  %3d | %s | %s | %s\n", LENS[i], got, WANT[i], strcmp(got, WANT[i]) == 0 ? "PASS" : "FAIL");
        if (strcmp(got, WANT[i])) all = 0;
    }
    printf("  %s\n", all ? "All four RFC 4493 vectors reproduced." : "MISMATCH");

    /* ----------------------------- user input ----------------------------------- */
    {
        char buf[300];
        u8 k[16], m[128];
        int kn, mn;
        read_line("\nTry your own: AES key (32 hex digits, Enter to skip): ", buf, sizeof buf);
        if (buf[0]) {
            kn = parse_hex(buf, k, 16);
            if (kn != 16) { printf("  need exactly 16 bytes\n"); return 0; }
            read_line("Message in hex (any length up to 128 bytes, may be empty): ", buf, sizeof buf);
            mn = parse_hex(buf, m, 128);
            if (mn < 0) { printf("  bad hex\n"); return 0; }
            aes128_expand(k, rk);
            aes128_encrypt(rk, zero, L);
            subkeys(L, 16, 0x87, k1, k2);
            phex("  L   = ", L, 16); phex("  K1  = ", k1, 16); phex("  K2  = ", k2, 16);
            cmac(aes_enc, rk, 16, 0x87, m, mn, tag);
            phex("  CMAC = ", tag, 16);
        }
    }
    return 0;
}
