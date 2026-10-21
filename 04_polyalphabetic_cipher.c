/*
 * ============================================================================
 *  EXPERIMENT 4 : POLYALPHABETIC SUBSTITUTION CIPHER  (Vigenere cipher)
 * ============================================================================
 *  Aim
 *  ---
 *  Write a C program for a polyalphabetic substitution cipher, which uses a
 *  separate monoalphabetic substitution (a Caesar shift) for each successive
 *  letter of plaintext, depending on a key.
 *
 *  Algorithm
 *  ---------
 *  The key word is repeated to the length of the message.  Key letter K_i
 *  (A=0 .. Z=25) selects the shift used for plaintext letter P_i:
 *
 *      C_i = (P_i + K_i) mod 26          P_i = (C_i - K_i) mod 26
 *
 *  Only letters consume key characters; spaces and punctuation are copied.
 *
 *  Because the same plaintext letter can map to different ciphertext letters
 *  (e.g. the two 'E's of "ENCRYPTED" differ), single-letter frequency
 *  analysis no longer works directly.
 *
 *  The program also prints a step-by-step table and can display the full
 *  26x26 Vigenere tableau.
 *
 *  Compile :  gcc 04_polyalphabetic_cipher.c -o vigenere
 * ============================================================================
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#define MAXLEN 2048

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

/* strip the key to upper-case letters; returns its length */
static int clean_key(char *key)
{
    int n = 0, i;
    for (i = 0; key[i]; i++)
        if (isalpha((unsigned char)key[i])) key[n++] = (char)toupper((unsigned char)key[i]);
    key[n] = '\0';
    return n;
}

static void vigenere(const char *in, char *out, const char *key, int decrypt, int verbose)
{
    int klen = (int)strlen(key), k = 0, i;

    if (verbose)
        printf("\n  pos | in | key | shift | out\n  ----+----+-----+-------+----\n");

    for (i = 0; in[i]; i++) {
        if (isalpha((unsigned char)in[i])) {
            int base  = isupper((unsigned char)in[i]) ? 'A' : 'a';
            int shift = key[k % klen] - 'A';
            int p     = in[i] - base;
            int c     = decrypt ? (p - shift + 26) % 26 : (p + shift) % 26;
            out[i] = (char)(base + c);
            if (verbose)
                printf("  %3d |  %c |  %c  |  %2d   |  %c\n", i + 1, in[i], key[k % klen], shift, out[i]);
            k++;
        } else {
            out[i] = in[i];
        }
    }
    out[i] = '\0';
}

static void print_tableau(void)
{
    int r, c;
    printf("\n     ");
    for (c = 0; c < 26; c++) printf("%c ", 'A' + c);
    printf("\n     ");
    for (c = 0; c < 26; c++) printf("--");
    printf("\n");
    for (r = 0; r < 26; r++) {
        printf("  %c| ", 'A' + r);
        for (c = 0; c < 26; c++) printf("%c ", 'A' + (r + c) % 26);
        printf("\n");
    }
}

int main(void)
{
    char text[MAXLEN], out[MAXLEN], key[256];
    int choice;

    printf("=========================================\n");
    printf("   POLYALPHABETIC (VIGENERE) CIPHER\n");
    printf("=========================================\n");

    for (;;) {
        printf("\n1. Encrypt\n2. Decrypt\n3. Show Vigenere tableau\n4. Exit\n");
        choice = read_int("Choice: ");
        if (choice == 4) return 0;
        if (choice == 3) { print_tableau(); continue; }
        if (choice != 1 && choice != 2) { printf("Invalid choice.\n"); continue; }

        do {
            read_line("Enter key (letters only): ", key, sizeof key);
        } while (clean_key(key) == 0 && printf("  Key must contain at least one letter.\n"));

        if (choice == 1) {
            read_line("Enter plaintext : ", text, sizeof text);
            vigenere(text, out, key, 0, 1);
            printf("\nKey used   : %s\nCiphertext : %s\n", key, out);
        } else {
            read_line("Enter ciphertext: ", text, sizeof text);
            vigenere(text, out, key, 1, 1);
            printf("\nKey used   : %s\nPlaintext  : %s\n", key, out);
        }
    }
}
