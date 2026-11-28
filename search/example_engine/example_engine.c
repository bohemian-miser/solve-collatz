/* Example search engine for search/engine.py: sums popcount(n) for 1 <= n <= N across threads.
 * Copy this layout for a real engine: parse flags, split the range across threads, combine the
 * per-thread results in a fixed order, and print strict JSON with a `canonical` object. */
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_THREADS 64

typedef struct {
    uint64_t lo, hi, sum;
} Chunk;

static void *work(void *arg) {
    Chunk *c = arg;
    for (uint64_t n = c->lo; n <= c->hi; n++) c->sum += (uint64_t)__builtin_popcountll(n);
    return NULL;
}

int main(int argc, char **argv) {
    uint64_t n_max = 1000000;
    int threads = 1;
    for (int i = 1; i + 1 < argc; i += 2) {
        if (strcmp(argv[i], "--n") == 0) n_max = strtoull(argv[i + 1], NULL, 10);
        else if (strcmp(argv[i], "--threads") == 0) threads = atoi(argv[i + 1]);
        else { fprintf(stderr, "unknown flag %s\n", argv[i]); return 2; }
    }
    if (threads < 1 || threads > MAX_THREADS || n_max < 1) return 2;

    pthread_t tid[MAX_THREADS];
    Chunk chunk[MAX_THREADS];
    uint64_t step = n_max / (uint64_t)threads;
    for (int t = 0; t < threads; t++) {
        chunk[t].lo = 1 + (uint64_t)t * step;
        chunk[t].hi = (t == threads - 1) ? n_max : (uint64_t)(t + 1) * step;
        chunk[t].sum = 0;
        pthread_create(&tid[t], NULL, work, &chunk[t]);
    }
    uint64_t total = 0;
    for (int t = 0; t < threads; t++) {
        pthread_join(tid[t], NULL);
        total += chunk[t].sum;
    }
    printf("{\"canonical\":{\"n\":%llu,\"popcount_sum\":%llu},\"threads\":%d}\n",
           (unsigned long long)n_max, (unsigned long long)total, threads);
    return 0;
}
