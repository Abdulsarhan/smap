#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdio.h>

typedef enum {
    TYPE_INT,
    TYPE_FLOAT,
    TYPE_STRING
} ValueType;

typedef union {
    int i;
    float f;
    char *s;
} ValueData;

typedef struct {
    ValueType type;
    ValueData data;
} Value;

typedef struct Entry {
    char *key;
    Value value;
    struct Entry *next;
} Entry;

typedef struct {
    Entry **buckets;
    size_t size;
} HashTable;

#ifdef SMAP_STATIC
#define SMAPDEF static
#else
#define SMAPDEF extern
#endif

#ifdef __cplusplus
extern "C" {
#endif

SMAPDEF HashTable* smap_create(size_t size);
SMAPDEF void smap_set(HashTable* table, const char* key, Value val);
SMAPDEF int smap_get(HashTable* table, const char* key, Value* out);
SMAPDEF void smap_free(HashTable* table);

#ifdef __cplusplus
}
#endif

#ifdef SMAP_IMPLEMENTATION

// --- SHA256 implementation start ---

#define SHA256_BLOCK_SIZE 32

typedef struct {
    uint8_t data[64];
    uint32_t datalen;
    uint64_t bitlen;
    uint32_t state[8];
} SHA256_CONTEXT;

#define ROTRIGHT(a,b) (((a) >> (b)) | ((a) << (32-(b))))
#define CH(x,y,z)  (((x) & (y)) ^ (~(x) & (z)))
#define MAJ(x,y,z) (((x) & (y)) ^ ((x) & (z)) ^ ((y) & (z)))
#define EP0(x)     (ROTRIGHT(x,2) ^ ROTRIGHT(x,13) ^ ROTRIGHT(x,22))
#define EP1(x)     (ROTRIGHT(x,6) ^ ROTRIGHT(x,11) ^ ROTRIGHT(x,25))
#define SIG0(x)    (ROTRIGHT(x,7) ^ ROTRIGHT(x,18) ^ ((x) >> 3))
#define SIG1(x)    (ROTRIGHT(x,17) ^ ROTRIGHT(x,19) ^ ((x) >> 10))

static const uint32_t _k[64] = {
  0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,
  0x923f82a4,0xab1c5ed5,0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,
  0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,0xe49b69c1,0xefbe4786,
  0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
  0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,
  0x06ca6351,0x14292967,0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,
  0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,0xa2bfe8a1,0xa81a664b,
  0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
  0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,
  0x5b9cca4f,0x682e6ff3,0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,
  0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
};

static void sha256__transform(SHA256_CONTEXT *ctx, const uint8_t data[]) {
    uint32_t a,b,c,d,e,f,g,h,t1,t2,m[64];
    int i;

    for (i = 0; i < 16; ++i)
        m[i] = (data[i*4] << 24) | (data[i*4+1] << 16) |
               (data[i*4+2] << 8) | (data[i*4+3]);
    for ( ; i < 64; ++i)
        m[i] = SIG1(m[i-2]) + m[i-7] + SIG0(m[i-15]) + m[i-16];

    a = ctx->state[0]; b = ctx->state[1]; c = ctx->state[2]; d = ctx->state[3];
    e = ctx->state[4]; f = ctx->state[5]; g = ctx->state[6]; h = ctx->state[7];

    for (i = 0; i < 64; ++i) {
        t1 = h + EP1(e) + CH(e,f,g) + _k[i] + m[i];
        t2 = EP0(a) + MAJ(a,b,c);
        h = g; g = f; f = e;
        e = d + t1;
        d = c; c = b; b = a;
        a = t1 + t2;
    }

    ctx->state[0] += a; ctx->state[1] += b; ctx->state[2] += c; ctx->state[3] += d;
    ctx->state[4] += e; ctx->state[5] += f; ctx->state[6] += g; ctx->state[7] += h;
}

static void sha256__init(SHA256_CONTEXT *ctx) {
    ctx->datalen = 0;
    ctx->bitlen = 0;
    ctx->state[0] = 0x6a09e667;
    ctx->state[1] = 0xbb67ae85;
    ctx->state[2] = 0x3c6ef372;
    ctx->state[3] = 0xa54ff53a;
    ctx->state[4] = 0x510e527f;
    ctx->state[5] = 0x9b05688c;
    ctx->state[6] = 0x1f83d9ab;
    ctx->state[7] = 0x5be0cd19;
}

static void sha256__update(SHA256_CONTEXT *ctx, const uint8_t *data, size_t len) {
    for (size_t i = 0; i < len; ++i) {
        ctx->data[ctx->datalen] = data[i];
        ctx->datalen++;
        if (ctx->datalen == 64) {
            sha256__transform(ctx, ctx->data);
            ctx->bitlen += 512;
            ctx->datalen = 0;
        }
    }
}

static void sha256__final(SHA256_CONTEXT *ctx, uint8_t hash[SHA256_BLOCK_SIZE]) {
    size_t i = ctx->datalen;

    ctx->data[i++] = 0x80;
    if (i > 56) {
        while (i < 64) ctx->data[i++] = 0x00;
        sha256__transform(ctx, ctx->data);
        i = 0;
    }
    while (i < 56) ctx->data[i++] = 0x00;

    ctx->bitlen += ctx->datalen * 8;
    for (int j = 7; j >= 0; j--)
        ctx->data[63 - j] = (ctx->bitlen >> (j * 8)) & 0xff;

    sha256__transform(ctx, ctx->data);

    for (i = 0; i < 4; i++) {
        for (int j = 0; j < 8; j++) {
            hash[i + j*4] = (ctx->state[j] >> (24 - i * 8)) & 0xff;
        }
    }
}

static void sha256__hash(const char *input, uint8_t output[SHA256_BLOCK_SIZE]) {
    SHA256_CONTEXT ctx;
    sha256__init(&ctx);
    sha256__update(&ctx, (const uint8_t *)input, strlen(input));
    sha256__final(&ctx, output);
}

// --- SHA256 implementation end ---

// --- Hashmap implementation start ---

static uint32_t hash__index(const char *key, size_t table_size) {
    uint8_t hash[SHA256_BLOCK_SIZE];
    sha256__hash(key, hash);

    // Use the first 4 bytes of SHA-256 as a 32-bit integer
    uint32_t h = (hash[0] << 24) | (hash[1] << 16) | (hash[2] << 8) | hash[3];
    return h % table_size;
}

static void free__mem_if_string(Value val) {
    if (val.type == TYPE_STRING) {
        free(val.data.s);
    }
}

SMAPDEF HashTable* smap_create(size_t size) {
    HashTable *table = malloc(sizeof(HashTable));
    if (!table) return NULL;

    table->buckets = calloc(size, sizeof(Entry *));
    if (!table->buckets) {
        free(table);
        return NULL;
    }

    table->size = size;
    return table;
}


SMAPDEF void smap_set(HashTable* table, const char* key, Value val) {
    uint32_t index = hash__index(key, table->size);
    Entry *current = table->buckets[index];

    // Search for an existing key
    while (current != NULL) {
        if (strcmp(current->key, key) == 0) {
            free__mem_if_string(current->value); // clean up old string if needed
            current->value = val;
            return;
        }
        current = current->next;
    }

    // Key not found, insert a new entry at the beginning
    Entry *new_entry = malloc(sizeof(Entry));
    if (!new_entry) return;

    new_entry->key = strdup(key);
    new_entry->value = val;
    new_entry->next = table->buckets[index];
    table->buckets[index] = new_entry;
}

SMAPDEF int smap_get(HashTable* table, const char* key, Value* out) {
    uint32_t index = hash__index(key, table->size);
    Entry *entry = table->buckets[index];
    while (entry) {
        if (strcmp(entry->key, key) == 0) {
            *out = entry->value;
            return 1;
        }
        entry = entry->next;
    }
    return 0;
}

SMAPDEF void smap_free(HashTable* table) {
    for (size_t i = 0; i < table->size; ++i) {
        Entry *entry = table->buckets[i];
        while (entry) {
            Entry *next = entry->next;
            free(entry->key);
            free__mem_if_string(entry->value);
            free(entry);
            entry = next;
        }
    }
    free(table->buckets);
    free(table);
}

#endif
// --- Hashmap implementation end ---
