/*
 * ============================================================================
 *  EXPERIMENT 22 : CIPHER BLOCK CHAINING (CBC) MODE WITH SEVERAL CIPHERS
 * ============================================================================
 *  Aim
 *  ---
 *  Encrypt and decrypt in cipher block chaining mode using one of:
 *      affine modulo 256, Hill modulo 256, S-DES, DES.
 *  Test data for S-DES: binary IV 1010 1010, binary plaintext
 *      0000 0001 0010 0011, binary key 01111 11101
 *  must give the binary ciphertext 1111 0100 0000 1011.
 *  Decryption must work correspondingly.
 *
 *  CBC mode
 *  --------
 *      C_0 = IV
 *      C_i = E_K( P_i XOR C_(i-1) )              (encryption)
 *      P_i = D_K( C_i ) XOR C_(i-1)              (decryption)
 *
 *  The four block ciphers
 *  ----------------------
 *   S-DES            8-bit block, 10-bit key                       (textbook)
 *   Affine mod 256   8-bit block:  C = (a*P + b) mod 256, a odd (gcd(a,256)=1)
 *                    P = a^-1 (C - b) mod 256
 *   Hill mod 256     16-bit block = 2 bytes (p1,p2); key = 2x2 matrix K with
 *                    det K odd:   (c1,c2)^T = K (p1,p2)^T mod 256;  decryption
 *                    uses K^-1 = det^-1 * adj(K) mod 256
 *   DES              64-bit block, 64-bit key (56 effective bits)
 *
 *  (Affine and Hill mod 256 are NOT secure ciphers - they are linear - but they
 *  illustrate how a mode of operation sits on top of any block cipher.)
 *
 *  Input formats : 1 = binary,  2 = hex,  3 = text (ASCII, padded with 0x80 00..)
 *  For binary/hex input the length must be a whole number of blocks.
 *
 *  Menu option 0 runs the required S-DES test vector automatically.
 *
 *  Compile :  gcc 22_cbc_mode_ciphers.c -o cbc
 * ============================================================================
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

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
/*  S-DES CORE  (Simplified DES, Stallings)                                  */
/*  10-bit key, 8-bit block, two Feistel rounds.  Bits are numbered 1..n     */
/*  from the LEFT (most significant bit), exactly as in the textbook.        */
/* ======================================================================== */
static const int SD_P10[10] = {3,5,2,7,4,10,1,9,8,6};
static const int SD_P8[8]   = {6,3,7,4,8,5,10,9};
static const int SD_IP[8]   = {2,6,3,1,4,8,5,7};
static const int SD_IPI[8]  = {4,1,3,5,7,2,8,6};
static const int SD_EP[8]   = {4,1,2,3,2,3,4,1};
static const int SD_P4[4]   = {2,4,3,1};
static const int SD_S0[4][4] = {{1,0,3,2},{3,2,1,0},{0,2,1,3},{3,1,3,2}};
static const int SD_S1[4][4] = {{0,1,2,3},{2,0,1,3},{3,0,1,0},{2,1,0,3}};

/* permute: in has n_in bits (MSB = position 1) -> out has n_out bits */
static unsigned sd_perm(unsigned in, const int *t, int n_out, int n_in)
{
    unsigned out = 0;
    int i;
    for (i = 0; i < n_out; i++) out = (out << 1) | ((in >> (n_in - t[i])) & 1u);
    return out;
}

static unsigned sd_ls(unsigned v5, int n) { return ((v5 << n) | (v5 >> (5 - n))) & 0x1Fu; }

/* generate K1, K2 (8 bits each) from a 10-bit key */
static void sdes_keys(unsigned key10, unsigned *k1, unsigned *k2)
{
    unsigned p = sd_perm(key10, SD_P10, 10, 10);
    unsigned l = (p >> 5) & 0x1F, r = p & 0x1F;
    l = sd_ls(l, 1); r = sd_ls(r, 1);
    *k1 = sd_perm((l << 5) | r, SD_P8, 8, 10);
    l = sd_ls(l, 2); r = sd_ls(r, 2);
    *k2 = sd_perm((l << 5) | r, SD_P8, 8, 10);
}

static unsigned sd_sbox(unsigned in4, const int s[4][4])
{
    int row = (int)(((in4 >> 3) & 1) << 1 | (in4 & 1));
    int col = (int)((in4 >> 1) & 3);
    return (unsigned)s[row][col];
}

/* f_K : (L, R) -> (L xor F(R,K), R) */
static unsigned sd_fk(unsigned in8, unsigned k)
{
    unsigned l = (in8 >> 4) & 0xF, r = in8 & 0xF;
    unsigned x = sd_perm(r, SD_EP, 8, 4) ^ k;
    unsigned s = (sd_sbox((x >> 4) & 0xF, SD_S0) << 2) | sd_sbox(x & 0xF, SD_S1);
    unsigned f = sd_perm(s, SD_P4, 4, 4);
    return ((l ^ f) << 4) | r;
}

static unsigned sd_sw(unsigned v) { return ((v & 0xF) << 4) | ((v >> 4) & 0xF); }

/* encrypt / decrypt a single 8-bit block */
static unsigned sdes_encrypt(unsigned pt, unsigned key10)
{
    unsigned k1, k2, x;
    sdes_keys(key10, &k1, &k2);
    x = sd_perm(pt, SD_IP, 8, 8);
    x = sd_fk(x, k1);
    x = sd_sw(x);
    x = sd_fk(x, k2);
    return sd_perm(x, SD_IPI, 8, 8);
}

__attribute__((unused)) static unsigned sdes_decrypt(unsigned ct, unsigned key10)
{
    unsigned k1, k2, x;
    sdes_keys(key10, &k1, &k2);
    x = sd_perm(ct, SD_IP, 8, 8);
    x = sd_fk(x, k2);
    x = sd_sw(x);
    x = sd_fk(x, k1);
    return sd_perm(x, SD_IPI, 8, 8);
}

/* print the low n bits of v as binary, grouped in nibbles */
__attribute__((unused)) static void sd_bits(unsigned v, int n)
{
    int i;
    for (i = n - 1; i >= 0; i--) { putchar('0' + (int)((v >> i) & 1u)); if (i % 4 == 0 && i) putchar(' '); }
}

/* parse a binary string (spaces ignored); returns number of bits read, value in *out */
__attribute__((unused)) static int sd_parse(const char *s, unsigned *out)
{
    unsigned v = 0;
    int n = 0;
    for (; *s; s++) {
        if (*s == '0' || *s == '1') { v = (v << 1) | (unsigned)(*s - '0'); n++; }
        else if (*s == ' ' || *s == '\t' || *s == '\r' || *s == '\n') continue;
        else return -1;
    }
    *out = v;
    return n;
}
/* ====================== end of S-DES core ================================ */


#define MAXB 512

/* ------------------------- selected cipher state -------------------------- */
enum { C_SDES = 1, C_AFFINE, C_HILL, C_DES };
static int  cipher = C_SDES, BS = 1;                  /* block size in bytes */
static unsigned sd_key = 0x1FD;                        /* 01111 11101 */
static int  aff_a = 5, aff_b = 17;
static int  hk[4] = {3, 5, 2, 7}, hki[4];              /* Hill key and inverse */
static u64  des_sub[16];

static void read_line(const char *prompt, char *buf, size_t n)
{
    printf("%s", prompt);
    fflush(stdout);
    if (!fgets(buf, (int)n, stdin)) { printf("\n"); exit(0); }
    buf[strcspn(buf, "\r\n")] = '\0';
}

static int inv256(int a)
{
    int x;
    a &= 255;
    for (x = 1; x < 256; x += 2) if (((a * x) & 255) == 1) return x;
    return -1;
}

static int setup_hill(void)
{
    int det = ((hk[0] * hk[3] - hk[1] * hk[2]) % 256 + 256) % 256, di;
    if (det % 2 == 0) return 0;
    di = inv256(det);
    hki[0] = (di * hk[3]) & 255;
    hki[1] = (((-di * hk[1]) % 256) + 256) & 255;
    hki[2] = (((-di * hk[2]) % 256) + 256) & 255;
    hki[3] = (di * hk[0]) & 255;
    return 1;
}

/* encrypt / decrypt ONE block held in bytes b[0..BS-1], in place */
static void block_crypt(u8 *b, int dec)
{
    switch (cipher) {
    case C_SDES:   b[0] = (u8)(dec ? sdes_decrypt(b[0], sd_key) : sdes_encrypt(b[0], sd_key)); break;
    case C_AFFINE:
        if (!dec) b[0] = (u8)((aff_a * b[0] + aff_b) & 255);
        else      b[0] = (u8)((inv256(aff_a) * (b[0] - aff_b)) & 255);
        break;
    case C_HILL: {
        const int *k = dec ? hki : hk;
        int x = b[0], y = b[1];
        b[0] = (u8)((k[0] * x + k[1] * y) & 255);
        b[1] = (u8)((k[2] * x + k[3] * y) & 255);
        break; }
    default: {
        u64 v = 0; int i;
        for (i = 0; i < 8; i++) v = (v << 8) | b[i];
        v = des_block(v, des_sub, dec);
        for (i = 7; i >= 0; i--) { b[i] = (u8)(v & 255); v >>= 8; }
    }
    }
}

/* CBC over n bytes (n multiple of BS) */
static void cbc(const u8 *in, u8 *out, int n, const u8 *iv, int dec, int verbose)
{
    u8 prev[8], blk[8], tmp[8];
    int i, j;
    const int bs = BS;                                 /* local copy: block size is always 1, 2 or 8 bytes */
    if (bs < 1 || bs > 8) return;
    memcpy(prev, iv, (size_t)bs);
    for (i = 0; i < n; i += bs) {
        if (!dec) {
            for (j = 0; j < bs; j++) blk[j] = in[i + j] ^ prev[j];
            if (verbose) { printf("   block %d: P xor prev = ", i / bs + 1); for (j = 0; j < bs; j++) printf("%02X", blk[j]); }
            block_crypt(blk, 0);
            memcpy(out + i, blk, (size_t)bs);
            memcpy(prev, blk, (size_t)bs);
            if (verbose) { printf("  ->  C = "); for (j = 0; j < bs; j++) printf("%02X", blk[j]); printf("\n"); }
        } else {
            memcpy(tmp, in + i, (size_t)bs);
            memcpy(blk, tmp, (size_t)bs);
            block_crypt(blk, 1);
            for (j = 0; j < bs; j++) out[i + j] = blk[j] ^ prev[j];
            if (verbose) { printf("   block %d: C = ", i / bs + 1); for (j = 0; j < bs; j++) printf("%02X", tmp[j]);
                           printf("  D(C) xor prev -> P = "); for (j = 0; j < bs; j++) printf("%02X", out[i + j]); printf("\n"); }
            memcpy(prev, tmp, (size_t)bs);
        }
    }
}

/* ------------------------------ I/O helpers ------------------------------- */
static int parse_bin(const char *s, u8 *out)       /* returns bytes, -1 on error */
{
    int bits = 0, i, n = 0;
    u8 cur = 0;
    for (i = 0; s[i]; i++) {
        if (s[i] == ' ') continue;
        if (s[i] != '0' && s[i] != '1') return -1;
        cur = (u8)((cur << 1) | (s[i] - '0'));
        if (++bits % 8 == 0) { out[n++] = cur; cur = 0; }
    }
    return bits % 8 ? -1 : n;
}

static int parse_hex(const char *s, u8 *out)
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
        if (++nib % 2 == 0) { out[n++] = cur; cur = 0; }
    }
    return nib % 2 ? -1 : n;
}

static void show(const char *label, const u8 *d, int n)
{
    int i, b;
    printf("%s", label);
    if (cipher == C_SDES || cipher == C_AFFINE) {                 /* binary, nibbles */
        for (i = 0; i < n; i++) { for (b = 7; b >= 0; b--) { putchar('0' + ((d[i] >> b) & 1)); if (b == 4) putchar(' '); } putchar(' '); }
        printf("  (hex ");
    } else printf("hex ");
    for (i = 0; i < n; i++) printf("%02X", d[i]);
    if (cipher == C_SDES || cipher == C_AFFINE) putchar(')');
    putchar('\n');
}

static int pad(const u8 *in, int n, u8 *out)
{
    int total = (n / BS + 1) * BS, i;
    memcpy(out, in, (size_t)n);
    out[n] = 0x80;
    for (i = n + 1; i < total; i++) out[i] = 0;
    return total;
}
static int unpad(const u8 *in, int n)
{
    int i = n - 1;
    while (i >= 0 && in[i] == 0) i--;
    return (i >= 0 && in[i] == 0x80) ? i : -1;
}

/* ------------------------------ test vector -------------------------------- */
static void test_vector(void)
{
    u8 pt[2] = {0x01, 0x23}, iv[1] = {0xAA}, ct[2], back[2];
    int saved = cipher, sbs = BS, ok;
    unsigned skey = sd_key;
    cipher = C_SDES; BS = 1; sd_key = 0x1FD;

    printf("\nS-DES CBC TEST VECTOR\n  key (10 bits)   : 01111 11101\n  IV              : 1010 1010\n"
           "  plaintext       : 0000 0001 0010 0011\n  expected cipher : 1111 0100 0000 1011\n\n");
    cbc(pt, ct, 2, iv, 0, 1);
    show("  ciphertext      : ", ct, 2);
    ok = (ct[0] == 0xF4 && ct[1] == 0x0B);
    printf("  encryption %s\n\n", ok ? "[PASS]" : "[FAIL]");
    cbc(ct, back, 2, iv, 1, 1);
    show("  decrypted       : ", back, 2);
    printf("  decryption %s\n", (back[0] == 0x01 && back[1] == 0x23) ? "[PASS]" : "[FAIL]");

    cipher = saved; BS = sbs; sd_key = skey;
}

static void choose_cipher(void)
{
    char buf[128];
    unsigned v;
    read_line("Cipher: 1 = S-DES, 2 = affine mod 256, 3 = Hill mod 256, 4 = DES : ", buf, sizeof buf);
    switch (atoi(buf)) {
    case 1:
        cipher = C_SDES; BS = 1;
        read_line("10-bit key in binary (Enter = 01111 11101): ", buf, sizeof buf);
        if (buf[0]) { if (sd_parse(buf, &v) == 10) sd_key = v; else printf("  need exactly 10 bits - keeping old key\n"); }
        break;
    case 2:
        cipher = C_AFFINE; BS = 1;
        read_line("a (odd) and b, e.g. \"5 17\" (Enter = keep): ", buf, sizeof buf);
        if (buf[0]) {
            int a, b;
            if (sscanf(buf, "%d %d", &a, &b) == 2 && (a & 1)) { aff_a = a & 255; aff_b = b & 255; }
            else printf("  a must be odd (gcd(a,256)=1) - keeping old key\n");
        }
        printf("  using E(p) = (%d p + %d) mod 256, a^-1 = %d\n", aff_a, aff_b, inv256(aff_a));
        break;
    case 3:
        cipher = C_HILL; BS = 2;
        read_line("2x2 key k11 k12 k21 k22 (Enter = keep): ", buf, sizeof buf);
        if (buf[0]) {
            int t[4], save[4], i;
            if (sscanf(buf, "%d %d %d %d", &t[0], &t[1], &t[2], &t[3]) == 4) {
                memcpy(save, hk, sizeof save);
                for (i = 0; i < 4; i++) hk[i] = t[i] & 255;
                if (!setup_hill()) { printf("  det must be odd - keeping old key\n"); memcpy(hk, save, sizeof save); }
            }
        }
        setup_hill();
        printf("  K = [%d %d; %d %d]   K^-1 mod 256 = [%d %d; %d %d]\n", hk[0], hk[1], hk[2], hk[3], hki[0], hki[1], hki[2], hki[3]);
        break;
    case 4: {
        u64 k;
        cipher = C_DES; BS = 8;
        read_line("64-bit key in hex (Enter = 133457799BBCDFF1): ", buf, sizeof buf);
        k = 0x133457799BBCDFF1ULL;
        if (buf[0] && !hex_to_u64(buf, &k)) printf("  bad hex, using default\n");
        des_key_schedule(k, des_sub);
        break; }
    default: printf("Invalid.\n");
    }
}

static void run(int dec)
{
    char buf[1024];
    u8 in[MAXB], iv[8], out[MAXB], padded[MAXB + 8];
    int fmt, n, i, ivn, textmode;

    read_line("Input format: 1 = binary, 2 = hex, 3 = text : ", buf, sizeof buf);
    fmt = atoi(buf);
    textmode = (fmt == 3);

    read_line("IV (same format; for text mode give hex, Enter = all zero): ", buf, sizeof buf);
    memset(iv, 0, sizeof iv);
    if (buf[0]) {
        ivn = (fmt == 1) ? parse_bin(buf, iv) : parse_hex(buf, iv);
        if (ivn != BS) { printf("  IV must be exactly %d byte(s)\n", BS); return; }
    }

    read_line(dec ? "Ciphertext: " : "Plaintext: ", buf, sizeof buf);
    if (fmt == 1) n = parse_bin(buf, in);
    else if (fmt == 2) n = parse_hex(buf, in);
    else if (!dec) { n = (int)strlen(buf); memcpy(in, buf, (size_t)n); }
    else n = parse_hex(buf, in);
    if (n < 0) { printf("  bad input\n"); return; }

    if (!dec && textmode) { n = pad(in, n, padded); memcpy(in, padded, (size_t)n); }
    if (n == 0 || n % BS) { printf("  length must be a positive multiple of %d byte(s)\n", BS); return; }

    printf("\n");
    cbc(in, out, n, iv, dec, 1);
    printf("\n");
    show(dec ? "  plaintext : " : "  ciphertext: ", out, n);
    if (dec && textmode) {
        int len = unpad(out, n);
        printf("  text      : ");
        for (i = 0; i < (len < 0 ? n : len); i++) putchar(isprint(out[i]) ? out[i] : '.');
        putchar('\n');
    }
}

int main(void)
{
    char buf[16];
    int choice;

    des_key_schedule(0x133457799BBCDFF1ULL, des_sub);
    setup_hill();
    printf("=========================================\n");
    printf("   CBC MODE: affine / Hill / S-DES / DES\n");
    printf("=========================================\n");
    test_vector();

    for (;;) {
        printf("\nCurrent cipher: %s\n", cipher == C_SDES ? "S-DES" : cipher == C_AFFINE ? "affine mod 256"
               : cipher == C_HILL ? "Hill mod 256" : "DES");
        printf("0. Run S-DES test vector   1. Choose cipher / key   2. Encrypt (CBC)   3. Decrypt (CBC)   4. Exit\n");
        read_line("Choice: ", buf, sizeof buf);
        choice = atoi(buf);
        if (choice == 4) return 0;
        if (choice == 0 && buf[0] == '0') test_vector();
        else if (choice == 1) choose_cipher();
        else if (choice == 2) run(0);
        else if (choice == 3) run(1);
        else printf("Invalid choice.\n");
    }
}
