/*
 * ============================================================================
 *  EXPERIMENT 33 : DATA ENCRYPTION STANDARD (DES)
 * ============================================================================
 *  Aim
 *  ---
 *  DES has been found vulnerable to very powerful attacks and its popularity
 *  has declined, but it is still a classic.  DES is a BLOCK cipher: 64 bits of
 *  plaintext go in, 64 bits of ciphertext come out.  The same algorithm and
 *  key are used for encryption and decryption (with the subkeys applied in
 *  reverse order).  The key is 56 bits (supplied as 64 bits, every 8th bit
 *  being a parity bit).  Implement DES in C.
 *
 *  Algorithm
 *  ---------
 *      plaintext (64) -> IP -> 16 Feistel rounds -> swap -> IP^-1 -> ciphertext
 *
 *   Round i :   L_i = R_(i-1)
 *               R_i = L_(i-1)  XOR  f(R_(i-1), K_i)
 *   f(R,K)  :   expand R from 32 to 48 bits (E)  -> XOR K_i
 *               -> eight 6-to-4-bit S-boxes -> permutation P
 *   Key schedule: PC-1 (64 -> 56 bits) -> split C0, D0 (28 bits each)
 *               -> for each round rotate both halves left by 1 or 2 bits
 *               -> PC-2 (56 -> 48 bits) = subkey K_i
 *
 *  Program features
 *   1. Self-test with the standard test vector
 *        key 133457799BBCDFF1, plaintext 0123456789ABCDEF -> 85E813540F0AB405
 *   2. Encrypt / decrypt one 64-bit block given in hex, showing every round
 *      (L, R and the 48-bit subkey)
 *   3. Encrypt / decrypt a text message (ECB mode, zero padding), output in hex
 *
 *  Compile :  gcc 33_des_algorithm.c -o des
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


static void read_line(const char *prompt, char *buf, size_t n)
{
    printf("%s", prompt);
    fflush(stdout);
    if (!fgets(buf, (int)n, stdin)) { printf("\n"); exit(0); }
    buf[strcspn(buf, "\r\n")] = '\0';
}

/* DES with a full trace of every round */
static u64 des_trace(u64 block, u64 key, int decrypt)
{
    u64 sub[16], ip;
    u32 l, r;
    int i;

    des_key_schedule(key, sub);
    printf("\n  Subkeys (48 bits, hex):\n");
    for (i = 0; i < 16; i++) printf("    K%-2d = %012llX\n", i + 1, sub[i]);

    ip = permute(block, IP_T, 64, 64);
    l = (u32)(ip >> 32); r = (u32)ip;
    printf("\n  After initial permutation IP : %016llX\n", ip);
    printf("  L0 = %08X   R0 = %08X\n\n", l, r);
    printf("  round | subkey used     |   L          R\n");
    printf("  ------+-----------------+------------------\n");
    for (i = 0; i < 16; i++) {
        u64 k = decrypt ? sub[15 - i] : sub[i];
        u32 t = r;
        r = l ^ des_f(r, k);
        l = t;
        printf("   %2d   | K%-2d = %012llX | %08X  %08X\n", i + 1, decrypt ? 16 - i : i + 1, k, l, r);
    }
    {
        u64 pre = ((u64)r << 32) | l;
        printf("\n  After 32-bit swap (R16 L16)  : %016llX\n", pre);
        return permute(pre, FP_T, 64, 64);
    }
}

static void self_test(void)
{
    u64 key = 0x133457799BBCDFF1ULL, pt = 0x0123456789ABCDEFULL, ct, back;
    ct = des_encrypt(pt, key);
    back = des_decrypt(ct, key);
    printf("\nSTANDARD TEST VECTOR\n");
    printf("  key        = %016llX\n  plaintext  = %016llX\n", key, pt);
    printf("  ciphertext = %016llX   (expected 85E813540F0AB405) %s\n", ct,
           ct == 0x85E813540F0AB405ULL ? "[PASS]" : "[FAIL]");
    printf("  decrypted  = %016llX   %s\n", back, back == pt ? "[PASS]" : "[FAIL]");
}

static void text_mode(u64 key)
{
    char text[512], hex[1100];
    u8 buf[520];
    int len, nblk, i, j;
    u64 sub[16];

    des_key_schedule(key, sub);
    read_line("Enter text to encrypt (ECB, zero padded): ", text, sizeof text);
    len = (int)strlen(text);
    nblk = (len + 7) / 8;
    if (nblk == 0) nblk = 1;
    memset(buf, 0, sizeof buf);
    memcpy(buf, text, (size_t)len);

    printf("\n  block | plaintext (hex)  | ciphertext (hex)\n  ------+------------------+------------------\n");
    hex[0] = '\0';
    for (i = 0; i < nblk; i++) {
        u64 b = 0, c;
        for (j = 0; j < 8; j++) b = (b << 8) | buf[i * 8 + j];
        c = des_block(b, sub, 0);
        printf("   %3d  | %016llX | %016llX\n", i + 1, b, c);
        sprintf(hex + strlen(hex), "%016llX", c);
    }
    printf("\n  Ciphertext (hex): %s\n", hex);

    /* decrypt it back */
    printf("  Decrypted text  : ");
    for (i = 0; i < nblk; i++) {
        u64 c = 0, p;
        for (j = 0; j < 16; j++) {
            char ch = hex[i * 16 + j];
            c = (c << 4) | (u64)(ch <= '9' ? ch - '0' : ch - 'A' + 10);
        }
        p = des_block(c, sub, 1);
        for (j = 7; j >= 0; j--) { int ch = (int)((p >> (8 * j)) & 0xFF); if (ch) putchar(ch); }
    }
    printf("\n");
}

int main(void)
{
    char buf[128];
    u64 key = 0x133457799BBCDFF1ULL, block;
    int choice;

    printf("=========================================\n");
    printf("      DATA ENCRYPTION STANDARD (DES)\n");
    printf("=========================================\n");
    self_test();

    for (;;) {
        printf("\nCurrent key: %016llX\n", key);
        printf("1. Set key (16 hex digits)\n2. Encrypt a 64-bit block (hex) with round trace\n"
               "3. Decrypt a 64-bit block (hex) with round trace\n4. Encrypt / decrypt a text message\n"
               "5. Re-run self test\n6. Exit\n");
        read_line("Choice: ", buf, sizeof buf);
        choice = atoi(buf);
        if (choice == 6) return 0;
        if (choice == 1) {
            read_line("Key (hex): ", buf, sizeof buf);
            if (!hex_to_u64(buf, &key)) printf("Invalid hex key.\n");
        } else if (choice == 2 || choice == 3) {
            read_line("Block (hex): ", buf, sizeof buf);
            if (!hex_to_u64(buf, &block)) { printf("Invalid hex.\n"); continue; }
            printf("\n  Result: %016llX\n", des_trace(block, key, choice == 3));
        } else if (choice == 4) text_mode(key);
        else if (choice == 5) self_test();
        else printf("Invalid choice.\n");
    }
}
