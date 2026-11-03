/*
 * ============================================================================
 *  EXPERIMENT 21 : PADDING FOR ECB, CBC AND CFB MODES
 * ============================================================================
 *  Aim
 *  ---
 *  For ECB, CBC and CFB modes the plaintext must be a sequence of one or more
 *  COMPLETE data blocks (or, for CFB, data segments): the total number of bits
 *  of plaintext must be a positive multiple of the block (segment) size.  One
 *  common method of padding appends a 1 bit followed by as few 0 bits (possibly
 *  none) as are needed to complete the final block.  It is good practice for
 *  the sender to pad EVERY message, including messages whose final block is
 *  already complete.
 *      What is the motivation for including a padding block when padding is
 *      not needed?
 *
 *  Answer
 *  ------
 *  So that the receiver can remove the padding UNAMBIGUOUSLY.  The receiver
 *  strips trailing zero bits and then the last '1' bit.  If padding were added
 *  only when needed, a message that is already a whole number of blocks and
 *  happens to END with the bit pattern 1000...0 would be indistinguishable from
 *  a shorter message that was padded - the receiver would wrongly delete real
 *  data.  If a padding block is ALWAYS added, the last '1' bit seen by the
 *  receiver is guaranteed to be the padding marker, so the original length is
 *  always recoverable.  (The cost is at most one extra block.)
 *
 *  Implementation notes
 *  --------------------
 *  - Blocks are DES blocks (64 bits = 8 bytes); the program works on whole
 *    bytes, so the pad is the byte 0x80 (bit pattern 1000 0000) followed by
 *    0x00 bytes - the "1 followed by zeros" rule at byte granularity.
 *  - ECB, CBC and CFB-64 (segment = a full 64-bit block) use this padding.
 *  - CFB-8 has 8-bit segments, so every message is already a multiple of the
 *    segment size and no padding is required.
 *
 *  Menu
 *   1. Padding table: how many pad bytes with "always pad" vs "pad if needed"
 *   2. Demonstration of the ambiguity when padding is only added if needed
 *   3. Encrypt / decrypt your own message in ECB, CBC, CFB-64 or CFB-8
 *
 *  Compile :  gcc 21_padding_ecb_cbc_cfb.c -o padding
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


#define MAXMSG 512

static void read_line(const char *prompt, char *buf, size_t n)
{
    printf("%s", prompt);
    fflush(stdout);
    if (!fgets(buf, (int)n, stdin)) { printf("\n"); exit(0); }
    buf[strcspn(buf, "\r\n")] = '\0';
}

static u64 load64(const u8 *p) { u64 v = 0; int i; for (i = 0; i < 8; i++) v = (v << 8) | p[i]; return v; }
static void store64(u8 *p, u64 v) { int i; for (i = 7; i >= 0; i--) { p[i] = (u8)(v & 0xFF); v >>= 8; } }

static void hex(const char *label, const u8 *d, int n)
{
    int i;
    printf("%s", label);
    for (i = 0; i < n; i++) { printf("%02X", d[i]); if (i % 8 == 7 && i + 1 < n) putchar(' '); }
    putchar('\n');
}

/* ------------------------------ padding ----------------------------------- */
/* pad EVERY message: 0x80 then zeros up to a multiple of 8 (1..8 bytes added) */
static int pad_always(const u8 *in, int n, u8 *out)
{
    int total = (n / 8 + 1) * 8, i;
    memcpy(out, in, (size_t)n);
    out[n] = 0x80;
    for (i = n + 1; i < total; i++) out[i] = 0;
    return total;
}

/* pad only if the last block is incomplete (the practice the question warns against) */
static int pad_if_needed(const u8 *in, int n, u8 *out)
{
    if (n > 0 && n % 8 == 0) { memcpy(out, in, (size_t)n); return n; }
    return pad_always(in, n, out);
}

/* remove padding: strip trailing zeros then one 0x80; returns length or -1 */
static int unpad(const u8 *in, int n)
{
    int i = n - 1;
    while (i >= 0 && in[i] == 0) i--;
    if (i < 0 || in[i] != 0x80) return -1;
    return i;
}

/* ------------------------------- modes ------------------------------------ */
static void ecb(const u8 *in, u8 *out, int n, const u64 *sub, int dec)
{ int i; for (i = 0; i < n; i += 8) store64(out + i, des_block(load64(in + i), sub, dec)); }

static void cbc(const u8 *in, u8 *out, int n, const u64 *sub, u64 iv, int dec)
{
    int i; u64 prev = iv;
    for (i = 0; i < n; i += 8) {
        u64 x = load64(in + i);
        if (!dec) { u64 c = des_block(x ^ prev, sub, 0); store64(out + i, c); prev = c; }
        else      { store64(out + i, des_block(x, sub, 1) ^ prev); prev = x; }
    }
}

/* CFB with 64-bit segments: C_i = P_i xor E(C_(i-1)),  C_0 = IV   (E is used in both directions) */
static void cfb64(const u8 *in, u8 *out, int n, const u64 *sub, u64 iv, int dec)
{
    int i; u64 reg = iv;
    for (i = 0; i < n; i += 8) {
        u64 x = load64(in + i), o = des_block(reg, sub, 0), y = x ^ o;
        store64(out + i, y);
        reg = dec ? x : y;
    }
}

/* CFB with 8-bit segments: shift register moves one byte per step */
static void cfb8(const u8 *in, u8 *out, int n, const u64 *sub, u64 iv, int dec)
{
    int i; u64 reg = iv;
    for (i = 0; i < n; i++) {
        u8 ks = (u8)(des_block(reg, sub, 0) >> 56);          /* leftmost 8 bits */
        u8 y = in[i] ^ ks, cbyte = dec ? in[i] : y;
        out[i] = y;
        reg = (reg << 8) | cbyte;
    }
}

/* ---------------------------- demonstrations ------------------------------ */
static void table(void)
{
    int n;
    u8 d[32] = {0}, o[48];
    printf("\n  message | PAD ALWAYS (recommended)   | PAD ONLY IF NEEDED\n"
             "  length  | pad bytes -> total length  | pad bytes -> total length\n"
             "  --------+----------------------------+---------------------------\n");
    for (n = 0; n <= 17; n++) {
        int a = pad_always(d, n, o), b = pad_if_needed(d, n, o);
        printf("   %3d    |    %d      ->   %3d (%d blocks) |    %d      ->   %3d (%d blocks)%s\n",
               n, a - n, a, a / 8, b - n, b, b / 8, (b == n) ? "   <- ambiguous!" : "");
    }
    printf("\n  With 'pad if needed' a message of 8 or 16 bytes gets NO padding at all.\n");
}

static void ambiguity(const u64 *sub, u64 iv)
{
    const u8 m1[] = { 'A', 'T', 'T', 'A', 'C', 'K', '!' };                       /* 7 bytes: needs padding */
    const u8 m2[] = { 'A', 'T', 'T', 'A', 'C', 'K', '!', 0x80 };                  /* 8 bytes: complete block, ends in 0x80 */
    u8 p1[16], p2[16], c1[16], c2[16], r[16];
    int n1, n2;

    printf("\n  Two different messages:\n");
    printf("   M1 = \"ATTACK!\"          (7 bytes)\n");
    printf("   M2 = \"ATTACK!\" + 0x80   (8 bytes - one complete block whose last byte is 0x80)\n");

    printf("\n  --- Rule A: pad ONLY IF NEEDED ---\n");
    n1 = pad_if_needed(m1, 7, p1);
    n2 = pad_if_needed(m2, 8, p2);
    hex("   padded M1 : ", p1, n1);
    hex("   padded M2 : ", p2, n2);
    cbc(p1, c1, n1, sub, iv, 0);
    cbc(p2, c2, n2, sub, iv, 0);
    hex("   CBC(M1)   : ", c1, n1);
    hex("   CBC(M2)   : ", c2, n2);
    printf("   The two ciphertexts are %s.\n", (n1 == n2 && !memcmp(c1, c2, (size_t)n1)) ? "IDENTICAL" : "different");
    cbc(c1, r, n1, sub, iv, 1);
    printf("   Receiver decrypts to %d bytes, strips padding -> keeps %d byte(s).\n", n1, unpad(r, n1));
    printf("   => The receiver cannot tell whether the sender sent M1 (7 bytes) or M2 (8 bytes);\n"
           "      for M2 it would delete the real byte 0x80 and deliver a corrupted message.\n");

    printf("\n  --- Rule B: pad EVERY message ---\n");
    n1 = pad_always(m1, 7, p1);
    n2 = pad_always(m2, 8, p2);
    hex("   padded M1 : ", p1, n1);
    hex("   padded M2 : ", p2, n2);
    cbc(p1, c1, n1, sub, iv, 0);
    cbc(p2, c2, n2, sub, iv, 0);
    printf("   M1 -> %d bytes, M2 -> %d bytes of ciphertext (M2 got an extra, all-padding block).\n", n1, n2);
    cbc(c1, r, n1, sub, iv, 1);
    printf("   Receiver recovers M1 length = %d (correct)\n", unpad(r, n1));
    cbc(c2, r, n2, sub, iv, 1);
    printf("   Receiver recovers M2 length = %d (correct, real 0x80 byte preserved)\n", unpad(r, n2));
    printf("   => Padding is always unambiguous: the LAST 0x80 byte is always the pad marker.\n");
}

static void crypt_demo(const u64 *sub, u64 iv)
{
    char text[MAXMSG], buf[16];
    u8 pad[MAXMSG + 16], ct[MAXMSG + 16], back[MAXMSG + 16];
    int mode, n, total, len;
    const char *names[] = { "", "ECB", "CBC", "CFB-64", "CFB-8" };

    memset(ct, 0, sizeof ct);
    read_line("Message: ", text, sizeof text);
    read_line("Mode (1 = ECB, 2 = CBC, 3 = CFB-64, 4 = CFB-8): ", buf, sizeof buf);
    mode = atoi(buf);
    if (mode < 1 || mode > 4) { printf("Invalid mode.\n"); return; }

    n = (int)strlen(text);
    if (mode == 4) { memcpy(pad, text, (size_t)n); total = n; printf("\n  CFB-8: 8-bit segments, no padding needed.\n"); }
    else { total = pad_always((const u8 *)text, n, pad); printf("\n  %d bytes -> padded to %d bytes (%d block%s)\n", n, total, total / 8, total > 8 ? "s" : ""); }
    hex("  padded plaintext : ", pad, total);

    switch (mode) {
    case 1: ecb(pad, ct, total, sub, 0); break;
    case 2: cbc(pad, ct, total, sub, iv, 0); break;
    case 3: cfb64(pad, ct, total, sub, iv, 0); break;
    default: cfb8(pad, ct, total, sub, iv, 0); break;
    }
    printf("  mode             : %s   IV = %016llX\n", names[mode], iv);
    hex("  ciphertext       : ", ct, total);

    switch (mode) {
    case 1: ecb(ct, back, total, sub, 1); break;
    case 2: cbc(ct, back, total, sub, iv, 1); break;
    case 3: cfb64(ct, back, total, sub, iv, 1); break;
    default: cfb8(ct, back, total, sub, iv, 1); break;
    }
    len = (mode == 4) ? total : unpad(back, total);
    printf("  decrypted        : \"%.*s\"   (original length %d)\n", len < 0 ? 0 : len, (char *)back, len);
}

int main(void)
{
    u64 key = 0x133457799BBCDFF1ULL, iv = 0x0123456789ABCDEFULL, sub[16];
    char buf[16];
    int choice;

    des_key_schedule(key, sub);
    printf("=========================================\n");
    printf("   PADDING AND THE ECB / CBC / CFB MODES\n");
    printf("=========================================\n");
    printf("(DES, key %016llX, IV %016llX)\n", key, iv);

    for (;;) {
        printf("\n1. Padding table\n2. Why pad even when not needed (ambiguity demo)\n"
               "3. Encrypt / decrypt a message\n4. Exit\n");
        read_line("Choice: ", buf, sizeof buf);
        choice = atoi(buf);
        if (choice == 4) return 0;
        if (choice == 1) table();
        else if (choice == 2) ambiguity(sub, iv);
        else if (choice == 3) crypt_demo(sub, iv);
        else printf("Invalid choice.\n");
    }
}
