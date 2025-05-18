# smap

Simple Hashmap implementation that uses a sha256 hash function.
The idea is to reduce collisions when you are hashing stuff so that lookups can be made faster.
> [!WARNING]
> when you smap_set a value that is a string, the pointer to the string is owned by the smap implementation will be freed if overwriten or if the map is freed. The example in the usage section gives a copy of the string to smap to avoid this problem.

> **Note:** when you call smap_set with the same key twice the second value will overwrite the first one.
## usage

```c
#define SMAP_IMPLEMENTATION
#include "smap.h"
#include <stdio.h>
#include <string.h> // for strdup

int main() {
    HashTable* table = smap_create(32);

    Value v1 = { .type = TYPE_INT, .data.i = 42 };
    smap_set(table, "answer", v1);

    Value v2 = { .type = TYPE_STRING, .data.s = strdup("hello") }; // heap-allocated string
    smap_set(table, "greeting", v2);

    Value result;
    if (smap_get(table, "greeting", &result) && result.type == TYPE_STRING) {
        printf("greeting: %s\n", result.data.s);
    }

    smap_free(table);
    return 0;
}
```