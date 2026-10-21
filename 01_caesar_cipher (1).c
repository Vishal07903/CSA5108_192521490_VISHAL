/*
 * ============================================================================
 *  EXPERIMENT 1 : CAESAR CIPHER
 * ============================================================================
 *  Aim
 *  ---
 *  Write a C program for the Caesar cipher, which replaces each letter of the
 *  alphabet with the letter standing k places further down the alphabet,
 *  for k in the range 1 through 25.
 *
 *  Algorithm
 *  ---------
 *      Encryption :  C = (P + k) mod 26
 *      Decryption :  P = (C - k) mod 26
 *
 *  Letters are mapped A..Z -> 0..25.  Case is preserved and every character
 *  that is not a letter (spaces, digits, punctuation) is copied unchanged.
 *
 *  Features
 *  --------
 *   1. Encrypt a message with a chosen key k (1..25)
 *   2. Decrypt a message with a known key
 *   3. Brute-force attack  - try all 25 keys (the key space is tiny)
 *   4. Print the plaintext -> ciphertext alphabet mapping for a key
 *
 *  Compile :  gcc 01_caesar_cipher.c -o caesar
 *  Run     :  ./caesar
 * ============================================================================
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#define MAXLEN 2048

/* ---- small input helpers ------------------------------------------------- */
static void read_line(const char *prompt, char *buf, size_t n)
{
    printf("%s", prompt);
    fflush(stdout);
    if (!fgets(buf, (int)n, stdin)) { printf("\n"); exit(0); }
    buf[strcspn(buf, "\r\n")] = '\0';
}

static int read_int(const char *prompt)
{
    char b[64];
    read_line(prompt, b, sizeof b);
    return atoi(b);
}

/* ---- core operation: shift one character by k positions ------------------ */
static char shift_char(char c, int k)
{
    if (isupper((unsigned char)c))
        return (char)('A' + (((c - 'A') + k) % 26 + 26) % 26);
    if (islower((unsigned char)c))
        return (char)('a' + (((c - 'a') + k) % 26 + 26) % 26);
    return c;                              /* non-letters are untouched */
}

static void caesar_encrypt(const char *plain, char *cipher, int k)
{
    size_t i;
    for (i = 0; plain[i]; i++) cipher[i] = shift_char(plain[i], k);
    cipher[i] = '\0';
}

static void caesar_decrypt(const char *cipher, char *plain, int k)
{
    caesar_encrypt(cipher, plain, -k);     /* decryption = shift by -k */
}

static void show_mapping(int k)
{
    int i;
    printf("\n  plain : ");
    for (i = 0; i < 26; i++) printf("%c ", 'A' + i);
    printf("\n  cipher: ");
    for (i = 0; i < 26; i++) printf("%c ", 'A' + (i + k) % 26);
    printf("\n");
}

static int get_key(void)
{
    int k;
    do {
        k = read_int("Enter key k (1-25): ");
        if (k < 1 || k > 25) printf("  Invalid key. k must be between 1 and 25.\n");
    } while (k < 1 || k > 25);
    return k;
}

int main(void)
{
    char text[MAXLEN], out[MAXLEN];
    int choice, k, i;

    printf("=========================================\n");
    printf("          CAESAR CIPHER  (C = P + k)\n");
    printf("=========================================\n");

    for (;;) {
        printf("\n1. Encrypt\n2. Decrypt\n3. Brute-force attack (all 25 keys)\n"
               "4. Show alphabet mapping\n5. Exit\n");
        choice = read_int("Choice: ");

        switch (choice) {
        case 1:
            read_line("Enter plaintext : ", text, sizeof text);
            k = get_key();
            caesar_encrypt(text, out, k);
            show_mapping(k);
            printf("\nCiphertext : %s\n", out);
            break;
        case 2:
            read_line("Enter ciphertext: ", text, sizeof text);
            k = get_key();
            caesar_decrypt(text, out, k);
            printf("\nPlaintext  : %s\n", out);
            break;
        case 3:
            read_line("Enter ciphertext: ", text, sizeof text);
            printf("\n  key | candidate plaintext\n  ----+--------------------\n");
            for (i = 1; i <= 25; i++) {
                caesar_decrypt(text, out, i);
                printf("  %3d | %s\n", i, out);
            }
            printf("\nLook for the line that reads as meaningful English.\n");
            break;
        case 4:
            k = get_key();
            show_mapping(k);
            break;
        case 5:
            return 0;
        default:
            printf("Invalid choice.\n");
        }
    }
}
