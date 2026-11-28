/* Profile one dyadic shell [2^s, 2^(s+1)) the way `rangeTop`/`rangeWalk` in
 * Collatz/Known/RangeCheck.lean walk it: for each residue r mod 2^t (bucket key), count the
 * leaves (odd n in the shell whose residue class is not pruned) and the largest number of
 * `drop4x2` iterations any leaf needs. Prints one JSON object on stdout.
 * Usage: shell_profile <s> <t>     (needs 1 <= t <= s <= 60) */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef unsigned __int128 u128;
static int S, T;
static uint64_t *leaves;
static int max_iters;

static int pruned(u128 r, u128 cur, u128 p3, u128 p2) { return p3 < p2 && cur + p3 < r + p2; }

static u128 tstep(u128 c) { return (c & 1) ? (3 * c + 1) >> 1 : c >> 1; }

static void leaf(u128 r, u128 cur, u128 p3, u128 p2) {
    if (pruned(r, cur, p3, p2)) return;
    leaves[(uint64_t)(r & ((((u128)1) << T) - 1))]++;
    u128 target = r + p2, c = cur + p3;
    for (int it = 1;; it++) {
        int done = 0;
        for (int half = 0; half < 2 && !done; half++) {
            for (int i = 0; i < 4; i++) c = tstep(c);
            if (c < target) done = 1;
        }
        if (done) { if (it > max_iters) max_iters = it; return; }
        if (it > 100000) { fprintf(stderr, "no drop for r=%llu\n", (unsigned long long)r); exit(1); }
    }
}

static void walk(int depth, u128 r, u128 cur, u128 p3, u128 p2) {
    if (depth == S) { leaf(r, cur, p3, p2); return; }
    if (pruned(r, cur, p3, p2)) return;
    u128 p2n = 2 * p2, cp3 = cur + p3, rp2 = r + p2;
    if (cur & 1) {
        walk(depth + 1, r, (3 * cur + 1) >> 1, 3 * p3, p2n);
        walk(depth + 1, rp2, cp3 >> 1, p3, p2n);
    } else {
        walk(depth + 1, r, cur >> 1, p3, p2n);
        walk(depth + 1, rp2, (3 * cp3 + 1) >> 1, 3 * p3, p2n);
    }
}

int main(int argc, char **argv) {
    if (argc != 3) { fprintf(stderr, "usage: shell_profile <s> <t>\n"); return 2; }
    S = atoi(argv[1]); T = atoi(argv[2]);
    if (T < 1 || T > S || S > 60) return 2;
    leaves = calloc((size_t)1 << T, sizeof *leaves);
    walk(1, 1, 2, 3, 2); /* root: k = 1, r = 1 (odd n), terrasIter 1 1 = 2, 3^1, 2^1 */
    uint64_t total = 0;
    printf("{\"canonical\":{\"s\":%d,\"t\":%d,\"max_iters\":%d,\"leaves\":[", S, T, max_iters);
    for (uint64_t i = 0; i < ((uint64_t)1 << T); i++) {
        printf(i ? ",%llu" : "%llu", (unsigned long long)leaves[i]);
        total += leaves[i];
    }
    printf("],\"total_leaves\":%llu}}\n", (unsigned long long)total);
    return 0;
}
