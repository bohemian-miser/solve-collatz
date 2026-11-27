/*
 * glide_hunter.c — High-throughput Collatz (3n + 1) stopping-time & extreme-glide hunter.
 *
 * Track B (`Disprove/`) off-kernel search engine for `solve-collatz` (`DISPROVE-003`).
 *
 * Features:
 *   - Strict `__uint128_t` overflow detection (zero silent wraparound; `overflow_count` audited).
 *   - Mod-2^16 affine stopping-time drop sieve (`63,422 / 65,536 = 96.77%` residues drop < n
 *     in <= 26 standard steps with max threshold n_min = 24 and max pre-drop ratio < 116).
 *   - Syracuse odd-step shortcut (`ctz128`) with exact first-drop stopping-time recovery.
 *   - Block-parallel deterministic execution (`R <= L + L/32` guarantees all drop targets < L).
 *   - Mode 1 (`--range-end N`): verifies finite stopping time for all 1 <= n <= N and tracks
 *     exact record stopping times, record total stopping times, and exact peak-ratio glides.
 *   - Mode 2 (`--mersenne-max K`): stress-tests 2^k - 1, 3*2^k - 1, and 27*2^k - 1 up to k <= K
 *     with automatic arbitrary-precision big-int fallback on `__uint128_t` limit.
 *   - Deterministic, SHA-256-ready canonical JSON output.
 */

#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <inttypes.h>
#include <math.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

__extension__ typedef unsigned __int128 u128;

#define SIEVE_BITS 16U
#define SIEVE_SIZE (1U << SIEVE_BITS)
#define SIEVE_MASK (SIEVE_SIZE - 1U)
#define TAU_CACHE_CAP 250000000ULL
#define SEQ_CUTOFF (1ULL << 20)
#define MAX_RECORD_CAP 512U
#define BIGINT_MAX_LIMBS 256U
#define MERSENNE_MAX_STEPS 2000000U

static const u128 U128_SAFE_3N1 = (~(u128)0 - 1U) / 3U;

typedef struct {
    uint64_t pow3;
    uint64_t add_c;
    uint8_t shift_s;
    uint8_t steps;
    uint8_t drops;
    uint8_t min_n;
    double max_pre_drop_ratio;
} sieve_entry_t;

typedef struct {
    uint64_t n;
    uint32_t stopping_time;
    uint32_t total_steps;
    u128 peak;
} record_t;

typedef struct {
    record_t items[MAX_RECORD_CAP];
    size_t count;
} record_list_t;

typedef struct {
    uint64_t limbs[BIGINT_MAX_LIMBS];
    size_t len;
} bigint_t;

typedef struct {
    char family[32];
    uint32_t k;
    uint32_t seed_bits;
    uint32_t stopping_time;
    uint32_t total_steps;
    uint32_t peak_bits;
    double peak_ratio_approx;
    bool used_bigint_fallback;
    bool verified_hits_one;
    char seed_dec[128];
    char peak_dec[256];
} mersenne_record_t;

static sieve_entry_t g_sieve[SIEVE_SIZE];

static inline int ctz128(u128 x) {
    uint64_t lo = (uint64_t)x;
    if (lo != 0U) {
        return __builtin_ctzll(lo);
    }
    uint64_t hi = (uint64_t)(x >> 64);
    return 64 + __builtin_ctzll(hi);
}

static inline uint32_t bitlen128(u128 x) {
    if (x == 0U) {
        return 0U;
    }
    uint64_t hi = (uint64_t)(x >> 64);
    if (hi != 0U) {
        return 128U - (uint32_t)__builtin_clzll(hi);
    }
    return 64U - (uint32_t)__builtin_clzll((uint64_t)x);
}

static void u128_to_str(u128 v, char *buf, size_t bufsz) {
    char tmp[48];
    size_t pos = 0;
    if (v == 0U) {
        snprintf(buf, bufsz, "0");
        return;
    }
    while (v > 0U && pos < sizeof(tmp)) {
        tmp[pos++] = (char)('0' + (unsigned)(v % 10U));
        v /= 10U;
    }
    size_t out = 0;
    while (pos > 0 && out + 1 < bufsz) {
        buf[out++] = tmp[--pos];
    }
    buf[out] = '\0';
}

/* Exact comparison of (p1 / n1) vs (p2 / n2) without floating-point error or u128 overflow. */
static inline int cmp_ratio_u128_u64(u128 p1, uint64_t n1, u128 p2, uint64_t n2) {
    u128 q1 = p1 / n1;
    u128 q2 = p2 / n2;
    if (q1 != q2) {
        return (q1 > q2) ? 1 : -1;
    }
    u128 r1 = (p1 % n1) * (u128)n2;
    u128 r2 = (p2 % n2) * (u128)n1;
    if (r1 != r2) {
        return (r1 > r2) ? 1 : -1;
    }
    return 0;
}

static double ratio_to_double(u128 p, uint64_t n) {
    return (double)p / (double)n;
}

static uint32_t init_sieve(void) {
    uint32_t covered = 0;
    for (uint32_t r = 0; r < SIEVE_SIZE; r++) {
        uint64_t pow3 = 1ULL;
        uint64_t add_c = 0ULL;
        uint32_t val = r;
        uint8_t s = 0;
        uint8_t k = 0;
        double max_ratio = 1.0;
        bool drops = false;
        uint8_t min_n = 0;

        while (s < SIEVE_BITS) {
            if ((val & 1U) == 0U) {
                val >>= 1;
                s++;
            } else {
                k++;
                pow3 *= 3ULL;
                add_c = 3ULL * add_c + (1ULL << s);
                double upper = ((double)pow3 + (double)add_c / (double)SIEVE_SIZE) /
                               (double)(1ULL << s);
                if (upper > max_ratio) {
                    max_ratio = upper;
                }
                val = (3U * val + 1U) >> 1;
                s++;
            }
            if (pow3 < (1ULL << s)) {
                uint64_t denom = (1ULL << s) - pow3;
                uint64_t mn = add_c / denom;
                drops = true;
                min_n = (mn > 255ULL) ? 255U : (uint8_t)mn;
                break;
            }
        }
        g_sieve[r].pow3 = pow3;
        g_sieve[r].add_c = add_c;
        g_sieve[r].shift_s = s;
        g_sieve[r].steps = (uint8_t)(k + s);
        g_sieve[r].drops = drops ? 1U : 0U;
        g_sieve[r].min_n = min_n;
        g_sieve[r].max_pre_drop_ratio = max_ratio;
        if (drops) {
            covered++;
        }
    }
    return covered;
}

/* Compute exact full orbit to 1 for a single u64 seed (used only for rare record seeds). */
static bool exact_orbit_stats_u64(uint64_t n, uint32_t *out_stop, uint32_t *out_total,
                                  u128 *out_peak, uint64_t *overflow_count) {
    if (n == 1ULL) {
        *out_stop = 0U;
        *out_total = 0U;
        *out_peak = 1U;
        return true;
    }
    u128 cur = n;
    u128 peak = n;
    uint32_t total = 0U;
    uint32_t stop = 0U;
    bool have_stop = false;

    while (cur != 1U) {
        if (((uint64_t)cur & 1ULL) == 0ULL) {
            int tz = ctz128(cur);
            u128 nxt = cur >> tz;
            if (!have_stop && nxt < n) {
                uint32_t j = 1U;
                u128 tmp = cur >> 1;
                while (j < (uint32_t)tz && tmp >= n) {
                    tmp >>= 1;
                    j++;
                }
                stop = total + j;
                have_stop = true;
            }
            cur = nxt;
            total += (uint32_t)tz;
        } else {
            if (cur > U128_SAFE_3N1) {
                (*overflow_count)++;
                return false;
            }
            u128 nxt = 3U * cur + 1U;
            if (nxt > peak) {
                peak = nxt;
            }
            int tz = ctz128(nxt);
            u128 reduced = nxt >> tz;
            if (!have_stop && reduced < n) {
                uint32_t j = 1U;
                u128 tmp = nxt >> 1;
                while (j < (uint32_t)tz && tmp >= n) {
                    tmp >>= 1;
                    j++;
                }
                stop = total + 1U + j;
                have_stop = true;
            }
            cur = reduced;
            total += 1U + (uint32_t)tz;
        }
    }
    *out_stop = stop;
    *out_total = total;
    *out_peak = peak;
    return true;
}

static void push_candidate(record_list_t *list, uint64_t n, uint32_t stop, uint32_t total,
                           u128 peak) {
    if (list->count < MAX_RECORD_CAP) {
        list->items[list->count++] = (record_t){n, stop, total, peak};
    }
}

/* Simulate one seed n >= 2 until cur < threshold (where threshold <= n). */
static inline bool verify_seed_until_below(uint64_t n, uint64_t threshold, uint32_t *out_stop,
                                           uint32_t *out_steps_to_cur, uint64_t *out_cur_below,
                                           u128 *out_peak, uint64_t *overflow_count) {
    u128 cur = n;
    u128 peak = n;
    uint32_t steps = 0U;
    uint32_t stop = 0U;
    bool have_stop = false;

    while (cur >= threshold) {
        if (((uint64_t)cur & 1ULL) == 0ULL) {
            int tz = ctz128(cur);
            u128 nxt = cur >> tz;
            if (!have_stop && nxt < n) {
                uint32_t j = 1U;
                u128 tmp = cur >> 1;
                while (j < (uint32_t)tz && tmp >= n) {
                    tmp >>= 1;
                    j++;
                }
                stop = steps + j;
                have_stop = true;
            }
            cur = nxt;
            steps += (uint32_t)tz;
        } else {
            if (cur > U128_SAFE_3N1) {
                (*overflow_count)++;
                return false;
            }
            u128 nxt = 3U * cur + 1U;
            if (nxt > peak) {
                peak = nxt;
            }
            int tz = ctz128(nxt);
            u128 reduced = nxt >> tz;
            if (!have_stop && reduced < n) {
                uint32_t j = 1U;
                u128 tmp = nxt >> 1;
                while (j < (uint32_t)tz && tmp >= n) {
                    tmp >>= 1;
                    j++;
                }
                stop = steps + 1U + j;
                have_stop = true;
            }
            cur = reduced;
            steps += 1U + (uint32_t)tz;
        }
        if (steps > 1000000U) {
            return false;
        }
    }
    *out_stop = stop;
    *out_steps_to_cur = steps;
    *out_cur_below = (uint64_t)cur;
    *out_peak = peak;
    return true;
}

typedef struct {
    uint64_t start_n;
    uint64_t end_n;
    uint64_t block_L;
    uint16_t *tau;
    uint64_t tau_cap;
    uint32_t init_best_stop;
    uint32_t init_best_total;
    u128 init_best_peak;
    uint64_t init_best_peak_n;
    record_list_t cand_stop;
    record_list_t cand_total;
    record_list_t cand_peak;
    uint64_t sieved_count;
    uint64_t overflow_count;
    uint64_t failure_seed;
    bool ok;
} worker_ctx_t;

static void *worker_run(void *arg) {
    worker_ctx_t *ctx = (worker_ctx_t *)arg;
    uint32_t best_stop = ctx->init_best_stop;
    uint32_t best_total = ctx->init_best_total;
    u128 best_peak = ctx->init_best_peak;
    uint64_t best_peak_n = ctx->init_best_peak_n;
    const uint64_t block_L = ctx->block_L;
    uint16_t *const tau = ctx->tau;
    const uint64_t tau_cap = ctx->tau_cap;
    uint64_t sieved = 0ULL;

    for (uint64_t n = ctx->start_n; n <= ctx->end_n; n++) {
        const sieve_entry_t *ent = &g_sieve[n & SIEVE_MASK];
        if (ent->drops && n > (uint64_t)ent->min_n && best_stop > ent->steps &&
            ratio_to_double(best_peak, best_peak_n) > ent->max_pre_drop_ratio) {
            sieved++;
            if (n < tau_cap) {
                uint64_t m = (uint64_t)(((u128)ent->pow3 * (u128)n + (u128)ent->add_c) >>
                                        ent->shift_s);
                uint32_t tot = (uint32_t)ent->steps + (uint32_t)tau[m];
                if (tot >= 65535U) {
                    ctx->overflow_count++;
                    ctx->ok = false;
                    ctx->failure_seed = n;
                    return NULL;
                }
                tau[n] = (uint16_t)tot;
                if (tot > best_total) {
                    best_total = tot;
                    push_candidate(&ctx->cand_total, n, ent->steps, tot, 0U);
                }
            }
            continue;
        }

        uint32_t stop = 0U;
        uint32_t steps_to_cur = 0U;
        uint64_t cur_below = 0ULL;
        u128 peak = 0U;
        if (!verify_seed_until_below(n, block_L, &stop, &steps_to_cur, &cur_below, &peak,
                                     &ctx->overflow_count)) {
            ctx->ok = false;
            ctx->failure_seed = n;
            return NULL;
        }

        uint32_t tot = 0U;
        if (n < tau_cap && cur_below < tau_cap) {
            tot = steps_to_cur + (uint32_t)tau[cur_below];
            if (tot >= 65535U) {
                ctx->overflow_count++;
                ctx->ok = false;
                ctx->failure_seed = n;
                return NULL;
            }
            tau[n] = (uint16_t)tot;
            if (tot > best_total) {
                best_total = tot;
                push_candidate(&ctx->cand_total, n, stop, tot, peak);
            }
        }
        if (stop > best_stop) {
            best_stop = stop;
            push_candidate(&ctx->cand_stop, n, stop, tot, peak);
        }
        if (cmp_ratio_u128_u64(peak, n, best_peak, best_peak_n) > 0) {
            best_peak = peak;
            best_peak_n = n;
            push_candidate(&ctx->cand_peak, n, stop, tot, peak);
        }
    }

    ctx->sieved_count = sieved;
    ctx->ok = true;
    return NULL;
}

typedef struct {
    uint64_t range_end;
    uint64_t verified_count;
    uint64_t sieved_count;
    uint64_t overflow_count;
    uint64_t tau_exact_up_to;
    uint32_t sieve_covered;
    uint32_t threads_used;
    bool all_converged;
    uint64_t failure_seed;
    record_list_t stop_records;
    record_list_t total_records;
    record_list_t peak_records;
    double elapsed_sec;
} mode1_result_t;

static void merge_candidates(const record_list_t *cands, record_list_t *global_recs,
                             uint32_t *best_stop, uint32_t *best_total, u128 *best_peak,
                             uint64_t *best_peak_n, int kind, uint64_t *overflow_count) {
    for (size_t i = 0; i < cands->count; i++) {
        uint64_t n = cands->items[i].n;
        uint32_t stop = 0U;
        uint32_t total = 0U;
        u128 peak = 0U;
        bool accept = false;

        if (kind == 0) {
            if (cands->items[i].stopping_time > *best_stop) {
                accept = true;
            }
        } else if (kind == 1) {
            if (cands->items[i].total_steps > *best_total) {
                accept = true;
            }
        } else {
            if (cmp_ratio_u128_u64(cands->items[i].peak, n, *best_peak, *best_peak_n) > 0) {
                accept = true;
            }
        }
        if (!accept) {
            continue;
        }
        if (!exact_orbit_stats_u64(n, &stop, &total, &peak, overflow_count)) {
            continue;
        }
        if (kind == 0 && stop > *best_stop) {
            *best_stop = stop;
            push_candidate(global_recs, n, stop, total, peak);
        } else if (kind == 1 && total > *best_total) {
            *best_total = total;
            push_candidate(global_recs, n, stop, total, peak);
        } else if (kind == 2 && cmp_ratio_u128_u64(peak, n, *best_peak, *best_peak_n) > 0) {
            *best_peak = peak;
            *best_peak_n = n;
            push_candidate(global_recs, n, stop, total, peak);
        }
    }
}

static bool run_mode1(uint64_t range_end, uint32_t num_threads, mode1_result_t *res) {
    memset(res, 0, sizeof(*res));
    res->range_end = range_end;
    res->sieve_covered = init_sieve();
    if (range_end == 0ULL) {
        res->all_converged = true;
        return true;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    uint64_t tau_cap = (range_end + 1ULL <= TAU_CACHE_CAP) ? (range_end + 1ULL) : TAU_CACHE_CAP;
    uint16_t *tau = (uint16_t *)calloc((size_t)tau_cap, sizeof(uint16_t));
    if (!tau) {
        fprintf(stderr, "ERROR: Failed to allocate tau cache of %" PRIu64 " entries\n", tau_cap);
        return false;
    }
    res->tau_exact_up_to = tau_cap - 1ULL;

    uint32_t best_stop = 0U;
    uint32_t best_total = 0U;
    u128 best_peak = 1U;
    uint64_t best_peak_n = 1ULL;

    /* n = 1 base record */
    tau[1] = 0U;
    push_candidate(&res->stop_records, 1ULL, 0U, 0U, 1U);
    push_candidate(&res->total_records, 1ULL, 0U, 0U, 1U);
    push_candidate(&res->peak_records, 1ULL, 0U, 0U, 1U);
    res->verified_count = 1ULL;

    /* Sequential exact pass up to min(range_end, SEQ_CUTOFF - 1) */
    uint64_t seq_end = (range_end < SEQ_CUTOFF - 1ULL) ? range_end : (SEQ_CUTOFF - 1ULL);
    for (uint64_t n = 2ULL; n <= seq_end; n++) {
        const sieve_entry_t *ent = &g_sieve[n & SIEVE_MASK];
        if (n >= SIEVE_SIZE && ent->drops && n > (uint64_t)ent->min_n &&
            best_stop > ent->steps &&
            ratio_to_double(best_peak, best_peak_n) > ent->max_pre_drop_ratio) {
            res->sieved_count++;
            uint64_t m =
                (uint64_t)(((u128)ent->pow3 * (u128)n + (u128)ent->add_c) >> ent->shift_s);
            uint32_t tot = (uint32_t)ent->steps + (uint32_t)tau[m];
            if (tot >= 65535U) {
                res->overflow_count++;
                res->failure_seed = n;
                free(tau);
                return false;
            }
            tau[n] = (uint16_t)tot;
            if (tot > best_total) {
                uint32_t es = 0U, et = 0U;
                u128 ep = 0U;
                if (!exact_orbit_stats_u64(n, &es, &et, &ep, &res->overflow_count)) {
                    res->failure_seed = n;
                    free(tau);
                    return false;
                }
                best_total = et;
                push_candidate(&res->total_records, n, es, et, ep);
            }
            res->verified_count++;
            continue;
        }

        uint32_t stop = 0U;
        uint32_t steps_to_cur = 0U;
        uint64_t cur_below = 0ULL;
        u128 peak = 0U;
        if (!verify_seed_until_below(n, n, &stop, &steps_to_cur, &cur_below, &peak,
                                     &res->overflow_count)) {
            res->failure_seed = n;
            free(tau);
            return false;
        }
        uint32_t tot = steps_to_cur + (uint32_t)tau[cur_below];
        if (tot >= 65535U) {
            res->overflow_count++;
            res->failure_seed = n;
            free(tau);
            return false;
        }
        tau[n] = (uint16_t)tot;

        bool need_stop = (stop > best_stop);
        bool need_total = (tot > best_total);
        bool need_peak = (cmp_ratio_u128_u64(peak, n, best_peak, best_peak_n) > 0);
        if (need_stop || need_total || need_peak) {
            uint32_t es = 0U, et = 0U;
            u128 ep = 0U;
            if (!exact_orbit_stats_u64(n, &es, &et, &ep, &res->overflow_count)) {
                res->failure_seed = n;
                free(tau);
                return false;
            }
            if (need_stop && es > best_stop) {
                best_stop = es;
                push_candidate(&res->stop_records, n, es, et, ep);
            }
            if (need_total && et > best_total) {
                best_total = et;
                push_candidate(&res->total_records, n, es, et, ep);
            }
            if (need_peak && cmp_ratio_u128_u64(ep, n, best_peak, best_peak_n) > 0) {
                best_peak = ep;
                best_peak_n = n;
                push_candidate(&res->peak_records, n, es, et, ep);
            }
        }
        res->verified_count++;
    }

    /* Block-parallel sweep from SEQ_CUTOFF to range_end: R <= L + L/32 guarantees all drops < L. */
    if (num_threads < 1U) {
        num_threads = 1U;
    }
    if (num_threads > 64U) {
        num_threads = 64U;
    }
    res->threads_used = (range_end >= SEQ_CUTOFF) ? num_threads : 1U;

    worker_ctx_t *ctxs = calloc(num_threads, sizeof(worker_ctx_t));
    pthread_t *tids = calloc(num_threads, sizeof(pthread_t));
    if (!ctxs || !tids) {
        free(ctxs);
        free(tids);
        free(tau);
        return false;
    }

    uint64_t L = SEQ_CUTOFF;
    while (L <= range_end) {
        uint64_t span = L / 32ULL;
        uint64_t R = L + span - 1ULL;
        if (R > range_end || R < L) {
            R = range_end;
        }
        uint64_t total_items = R - L + 1ULL;
        uint32_t active = (total_items < num_threads) ? (uint32_t)total_items : num_threads;
        uint64_t chunk = total_items / active;
        uint64_t rem = total_items % active;

        uint64_t cur_start = L;
        for (uint32_t t = 0; t < active; t++) {
            uint64_t sz = chunk + (t < rem ? 1ULL : 0ULL);
            memset(&ctxs[t], 0, sizeof(worker_ctx_t));
            ctxs[t].start_n = cur_start;
            ctxs[t].end_n = cur_start + sz - 1ULL;
            ctxs[t].block_L = L;
            ctxs[t].tau = tau;
            ctxs[t].tau_cap = tau_cap;
            ctxs[t].init_best_stop = best_stop;
            ctxs[t].init_best_total = best_total;
            ctxs[t].init_best_peak = best_peak;
            ctxs[t].init_best_peak_n = best_peak_n;
            cur_start += sz;
        }

        if (active == 1U) {
            worker_run(&ctxs[0]);
        } else {
            for (uint32_t t = 0; t < active; t++) {
                pthread_create(&tids[t], NULL, worker_run, &ctxs[t]);
            }
            for (uint32_t t = 0; t < active; t++) {
                pthread_join(tids[t], NULL);
            }
        }

        for (uint32_t t = 0; t < active; t++) {
            res->overflow_count += ctxs[t].overflow_count;
            res->sieved_count += ctxs[t].sieved_count;
            if (!ctxs[t].ok) {
                res->all_converged = false;
                res->failure_seed = ctxs[t].failure_seed;
                free(ctxs);
                free(tids);
                free(tau);
                return false;
            }
        }
        for (uint32_t t = 0; t < active; t++) {
            merge_candidates(&ctxs[t].cand_stop, &res->stop_records, &best_stop, &best_total,
                             &best_peak, &best_peak_n, 0, &res->overflow_count);
            merge_candidates(&ctxs[t].cand_total, &res->total_records, &best_stop, &best_total,
                             &best_peak, &best_peak_n, 1, &res->overflow_count);
            merge_candidates(&ctxs[t].cand_peak, &res->peak_records, &best_stop, &best_total,
                             &best_peak, &best_peak_n, 2, &res->overflow_count);
        }
        res->verified_count += total_items;
        L = R + 1ULL;
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    res->elapsed_sec = (double)(t1.tv_sec - t0.tv_sec) +
                       (double)(t1.tv_nsec - t0.tv_nsec) * 1e-9;
    res->all_converged = (res->overflow_count == 0ULL);

    free(ctxs);
    free(tids);
    free(tau);
    return res->all_converged;
}

/* ---------------- Arbitrary-Precision BigInt Fallback for Mode 2 ---------------- */

static void bi_from_u64(bigint_t *a, uint64_t v) {
    memset(a->limbs, 0, sizeof(a->limbs));
    if (v == 0ULL) {
        a->len = 0;
    } else {
        a->limbs[0] = v;
        a->len = 1;
    }
}

static bool bi_is_one(const bigint_t *a) {
    return a->len == 1 && a->limbs[0] == 1ULL;
}

static int bi_cmp(const bigint_t *a, const bigint_t *b) {
    if (a->len != b->len) {
        return (a->len > b->len) ? 1 : -1;
    }
    for (size_t i = a->len; i > 0; i--) {
        uint64_t la = a->limbs[i - 1];
        uint64_t lb = b->limbs[i - 1];
        if (la != lb) {
            return (la > lb) ? 1 : -1;
        }
    }
    return 0;
}

static uint32_t bi_bitlen(const bigint_t *a) {
    if (a->len == 0) {
        return 0U;
    }
    uint64_t top = a->limbs[a->len - 1];
    return (uint32_t)((a->len - 1) * 64U + (64U - (uint32_t)__builtin_clzll(top)));
}

static bool bi_shl(bigint_t *a, uint32_t shift) {
    if (a->len == 0 || shift == 0U) {
        return true;
    }
    uint32_t word_shift = shift / 64U;
    uint32_t bit_shift = shift % 64U;
    size_t new_len = a->len + word_shift + (bit_shift ? 1U : 0U);
    if (new_len > BIGINT_MAX_LIMBS) {
        return false;
    }
    uint64_t out[BIGINT_MAX_LIMBS];
    memset(out, 0, sizeof(out));
    uint64_t carry = 0ULL;
    for (size_t i = 0; i < a->len; i++) {
        uint64_t v = a->limbs[i];
        out[i + word_shift] = (bit_shift == 0U) ? v : ((v << bit_shift) | carry);
        carry = (bit_shift == 0U) ? 0ULL : (v >> (64U - bit_shift));
    }
    if (carry != 0ULL) {
        out[a->len + word_shift] = carry;
    }
    size_t real_len = a->len + word_shift + ((carry != 0ULL) ? 1U : 0U);
    memcpy(a->limbs, out, real_len * sizeof(uint64_t));
    a->len = real_len;
    return true;
}

static bool bi_sub1(bigint_t *a) {
    if (a->len == 0) {
        return false;
    }
    for (size_t i = 0; i < a->len; i++) {
        if (a->limbs[i] > 0ULL) {
            a->limbs[i] -= 1ULL;
            break;
        }
        a->limbs[i] = ~0ULL;
    }
    while (a->len > 0 && a->limbs[a->len - 1] == 0ULL) {
        a->len--;
    }
    return true;
}

static bool bi_mul3_add1(bigint_t *a) {
    u128 carry = 1U;
    for (size_t i = 0; i < a->len; i++) {
        u128 prod = (u128)a->limbs[i] * 3U + carry;
        a->limbs[i] = (uint64_t)prod;
        carry = prod >> 64;
    }
    if (carry != 0U) {
        if (a->len >= BIGINT_MAX_LIMBS) {
            return false;
        }
        a->limbs[a->len++] = (uint64_t)carry;
    }
    return true;
}

static uint32_t bi_rshift_tz(bigint_t *a) {
    size_t zero_words = 0;
    while (zero_words < a->len && a->limbs[zero_words] == 0ULL) {
        zero_words++;
    }
    if (zero_words == a->len) {
        a->len = 0;
        return 0U;
    }
    uint32_t bit_tz = (uint32_t)__builtin_ctzll(a->limbs[zero_words]);
    uint32_t total_tz = (uint32_t)(zero_words * 64U) + bit_tz;
    size_t rem_len = a->len - zero_words;

    if (bit_tz == 0U) {
        memmove(a->limbs, a->limbs + zero_words, rem_len * sizeof(uint64_t));
    } else {
        for (size_t i = 0; i + 1 < rem_len; i++) {
            a->limbs[i] = (a->limbs[zero_words + i] >> bit_tz) |
                          (a->limbs[zero_words + i + 1] << (64U - bit_tz));
        }
        a->limbs[rem_len - 1] = a->limbs[zero_words + rem_len - 1] >> bit_tz;
    }
    a->len = rem_len;
    while (a->len > 0 && a->limbs[a->len - 1] == 0ULL) {
        a->len--;
    }
    return total_tz;
}

static void bi_rshift_one(bigint_t *a) {
    if (a->len == 0) {
        return;
    }
    for (size_t i = 0; i + 1 < a->len; i++) {
        a->limbs[i] = (a->limbs[i] >> 1) | (a->limbs[i + 1] << 63);
    }
    a->limbs[a->len - 1] >>= 1;
    if (a->limbs[a->len - 1] == 0ULL) {
        a->len--;
    }
}

static double bi_to_double(const bigint_t *a) {
    double acc = 0.0;
    for (size_t i = a->len; i > 0; i--) {
        acc = acc * 18446744073709551616.0 + (double)a->limbs[i - 1];
    }
    return acc;
}

static void bi_to_dec(const bigint_t *a, char *buf, size_t bufsz) {
    if (a->len == 0) {
        snprintf(buf, bufsz, "0");
        return;
    }
    if (a->len <= 2) {
        u128 v = (a->len == 1) ? a->limbs[0] : (((u128)a->limbs[1] << 64) | a->limbs[0]);
        u128_to_str(v, buf, bufsz);
        return;
    }
    /* Approximate scientific decimal if > 128 bits so output buffer stays bounded. */
    uint32_t bits = bi_bitlen(a);
    double approx = bi_to_double(a);
    if (isfinite(approx) && approx > 0.0) {
        snprintf(buf, bufsz, "%.6e (~2^%u)", approx, bits);
    } else {
        snprintf(buf, bufsz, "~2^%u", bits);
    }
}

static bool test_mersenne_seed(const char *family, uint64_t mult, uint32_t k,
                               mersenne_record_t *out, uint64_t *u128_fallbacks,
                               uint64_t *silent_overflows) {
    memset(out, 0, sizeof(*out));
    snprintf(out->family, sizeof(out->family), "%s", family);
    out->k = k;

    /* Exact seed n = mult * 2^k - 1 in bigint_t (always exact). */
    bigint_t seed_bi;
    bi_from_u64(&seed_bi, mult);
    if (!bi_shl(&seed_bi, k) || !bi_sub1(&seed_bi)) {
        (*silent_overflows)++;
        return false;
    }
    out->seed_bits = bi_bitlen(&seed_bi);
    bi_to_dec(&seed_bi, out->seed_dec, sizeof(out->seed_dec));

    bool can_u128 = (out->seed_bits <= 127U);
    if (can_u128) {
        u128 n = (((u128)mult) << k) - 1U;
        u128 cur = n;
        u128 peak = n;
        uint32_t total = 0U;
        uint32_t stop = 0U;
        bool have_stop = false;
        bool overflowed_u128 = false;

        while (cur != 1U) {
            if (((uint64_t)cur & 1ULL) == 0ULL) {
                int tz = ctz128(cur);
                u128 nxt = cur >> tz;
                if (!have_stop && nxt < n) {
                    uint32_t j = 1U;
                    u128 tmp = cur >> 1;
                    while (j < (uint32_t)tz && tmp >= n) {
                        tmp >>= 1;
                        j++;
                    }
                    stop = total + j;
                    have_stop = true;
                }
                cur = nxt;
                total += (uint32_t)tz;
            } else {
                if (cur > U128_SAFE_3N1) {
                    overflowed_u128 = true;
                    break;
                }
                u128 nxt = 3U * cur + 1U;
                if (nxt > peak) {
                    peak = nxt;
                }
                int tz = ctz128(nxt);
                u128 reduced = nxt >> tz;
                if (!have_stop && reduced < n) {
                    uint32_t j = 1U;
                    u128 tmp = nxt >> 1;
                    while (j < (uint32_t)tz && tmp >= n) {
                        tmp >>= 1;
                        j++;
                    }
                    stop = total + 1U + j;
                    have_stop = true;
                }
                cur = reduced;
                total += 1U + (uint32_t)tz;
            }
        }
        if (!overflowed_u128) {
            out->stopping_time = stop;
            out->total_steps = total;
            out->peak_bits = bitlen128(peak);
            out->peak_ratio_approx = (double)peak / (double)n;
            out->used_bigint_fallback = false;
            out->verified_hits_one = true;
            u128_to_str(peak, out->peak_dec, sizeof(out->peak_dec));
            return true;
        }
        (*u128_fallbacks)++;
    } else {
        (*u128_fallbacks)++;
    }

    /* Exact arbitrary-precision bigint_t fallback (never overflows within BIGINT_MAX_LIMBS). */
    bigint_t cur = seed_bi;
    bigint_t peak = seed_bi;
    uint32_t total = 0U;
    uint32_t stop = 0U;
    bool have_stop = false;
    out->used_bigint_fallback = true;

    while (!bi_is_one(&cur)) {
        if (total > MERSENNE_MAX_STEPS) {
            return false;
        }
        if ((cur.limbs[0] & 1ULL) == 0ULL) {
            uint32_t tz = bi_rshift_tz(&cur);
            if (!have_stop && bi_cmp(&cur, &seed_bi) < 0) {
                /* Reconstruct exact first step below seed_bi only once. */
                bigint_t tmp = cur;
                (void)bi_shl(&tmp, tz);
                uint32_t j = 1U;
                bi_rshift_one(&tmp);
                while (j < tz && bi_cmp(&tmp, &seed_bi) >= 0) {
                    bi_rshift_one(&tmp);
                    j++;
                }
                stop = total + j;
                have_stop = true;
            }
            total += tz;
        } else {
            if (!bi_mul3_add1(&cur)) {
                (*silent_overflows)++;
                return false;
            }
            if (bi_cmp(&cur, &peak) > 0) {
                peak = cur;
            }
            bigint_t pre_shift = cur;
            uint32_t tz = bi_rshift_tz(&cur);
            if (!have_stop && bi_cmp(&cur, &seed_bi) < 0) {
                uint32_t j = 1U;
                bi_rshift_one(&pre_shift);
                while (j < tz && bi_cmp(&pre_shift, &seed_bi) >= 0) {
                    bi_rshift_one(&pre_shift);
                    j++;
                }
                stop = total + 1U + j;
                have_stop = true;
            }
            total += 1U + tz;
        }
    }

    out->stopping_time = stop;
    out->total_steps = total;
    out->peak_bits = bi_bitlen(&peak);
    out->peak_ratio_approx = bi_to_double(&peak) / bi_to_double(&seed_bi);
    out->verified_hits_one = true;
    bi_to_dec(&peak, out->peak_dec, sizeof(out->peak_dec));
    return true;
}

static void print_record_array(FILE *fp, const record_list_t *list, int indent) {
    char pbuf[48];
    fprintf(fp, "[\n");
    for (size_t i = 0; i < list->count; i++) {
        const record_t *r = &list->items[i];
        u128_to_str(r->peak, pbuf, sizeof(pbuf));
        fprintf(fp,
                "%*s{\"n\": %" PRIu64 ", \"stopping_time\": %u, \"total_steps\": %u, "
                "\"peak\": \"%s\", \"peak_ratio\": %.6f}%s\n",
                indent, "", r->n, r->stopping_time, r->total_steps, pbuf,
                ratio_to_double(r->peak, r->n), (i + 1 < list->count) ? "," : "");
    }
    fprintf(fp, "%*s]", indent - 2, "");
}

static void write_json_output(FILE *fp, const mode1_result_t *m1, bool run_m2,
                              uint32_t mersenne_max, const mersenne_record_t *m2_recs,
                              size_t m2_count, uint64_t u128_fallbacks,
                              uint64_t silent_overflows, double m2_elapsed) {
    uint64_t total_overflows = (m1 ? m1->overflow_count : 0ULL) + silent_overflows;

    fprintf(fp, "{\n");
    fprintf(fp, "  \"canonical\": {\n");
    fprintf(fp, "    \"schema\": \"solve-collatz-glide-hunter/v1\",\n");
    fprintf(fp, "    \"overflow_count\": %" PRIu64 ",\n", total_overflows);
    fprintf(fp, "    \"u128_bigint_fallbacks\": %" PRIu64 ",\n", u128_fallbacks);

    if (m1 && m1->range_end > 0ULL) {
        fprintf(fp, "    \"mode1_range\": {\n");
        fprintf(fp, "      \"range_start\": 1,\n");
        fprintf(fp, "      \"range_end\": %" PRIu64 ",\n", m1->range_end);
        fprintf(fp, "      \"verified_count\": %" PRIu64 ",\n", m1->verified_count);
        fprintf(fp, "      \"all_converged\": %s,\n", m1->all_converged ? "true" : "false");
        fprintf(fp, "      \"tau_exact_up_to\": %" PRIu64 ",\n", m1->tau_exact_up_to);
        fprintf(fp, "      \"sieve_modulus\": %u,\n", SIEVE_SIZE);
        fprintf(fp, "      \"sieve_covered_residues\": %u,\n", m1->sieve_covered);
        fprintf(fp, "      \"sieved_fast_skips\": %" PRIu64 ",\n", m1->sieved_count);
        fprintf(fp, "      \"stopping_time_records\": ");
        print_record_array(fp, &m1->stop_records, 8);
        fprintf(fp, ",\n");
        fprintf(fp, "      \"total_stopping_time_records\": ");
        print_record_array(fp, &m1->total_records, 8);
        fprintf(fp, ",\n");
        fprintf(fp, "      \"peak_ratio_records\": ");
        print_record_array(fp, &m1->peak_records, 8);
        fprintf(fp, "\n    }%s\n", run_m2 ? "," : "");
    }

    if (run_m2) {
        uint32_t max_stop = 0U, max_tot = 0U, max_pbits = 0U;
        double max_pratio = 0.0;
        uint64_t max_stop_k = 0U, max_tot_k = 0U, max_pratio_k = 0U;
        char max_stop_fam[32] = "", max_tot_fam[32] = "", max_pratio_fam[32] = "";
        bool all_ok = true;

        for (size_t i = 0; i < m2_count; i++) {
            const mersenne_record_t *r = &m2_recs[i];
            if (!r->verified_hits_one) {
                all_ok = false;
            }
            if (r->stopping_time > max_stop) {
                max_stop = r->stopping_time;
                max_stop_k = r->k;
                snprintf(max_stop_fam, sizeof(max_stop_fam), "%s", r->family);
            }
            if (r->total_steps > max_tot) {
                max_tot = r->total_steps;
                max_tot_k = r->k;
                snprintf(max_tot_fam, sizeof(max_tot_fam), "%s", r->family);
            }
            if (r->peak_bits > max_pbits) {
                max_pbits = r->peak_bits;
            }
            if (r->peak_ratio_approx > max_pratio) {
                max_pratio = r->peak_ratio_approx;
                max_pratio_k = r->k;
                snprintf(max_pratio_fam, sizeof(max_pratio_fam), "%s", r->family);
            }
        }

        fprintf(fp, "    \"mode2_mersenne\": {\n");
        fprintf(fp, "      \"mersenne_max_k\": %u,\n", mersenne_max);
        fprintf(fp, "      \"families\": [\"2^k-1\", \"3*2^k-1\", \"27*2^k-1\"],\n");
        fprintf(fp, "      \"tested_count\": %zu,\n", m2_count);
        fprintf(fp, "      \"all_converged\": %s,\n", all_ok ? "true" : "false");
        fprintf(fp, "      \"max_stopping_time\": {\"family\": \"%s\", \"k\": %" PRIu64
                    ", \"value\": %u},\n",
                max_stop_fam, max_stop_k, max_stop);
        fprintf(fp, "      \"max_total_steps\": {\"family\": \"%s\", \"k\": %" PRIu64
                    ", \"value\": %u},\n",
                max_tot_fam, max_tot_k, max_tot);
        fprintf(fp, "      \"max_peak_ratio\": {\"family\": \"%s\", \"k\": %" PRIu64
                    ", \"value\": %.6f, \"max_peak_bits\": %u},\n",
                max_pratio_fam, max_pratio_k, max_pratio, max_pbits);
        fprintf(fp, "      \"samples\": [\n");
        /* Emit compact deterministic summary of notable & boundary records. */
        size_t emitted = 0;
        for (size_t i = 0; i < m2_count; i++) {
            const mersenne_record_t *r = &m2_recs[i];
            if (r->k <= 4U || r->k == mersenne_max || (r->k % 10U == 0U) ||
                (strcmp(r->family, max_pratio_fam) == 0 && r->k == max_pratio_k)) {
                fprintf(fp,
                        "%s        {\"family\": \"%s\", \"k\": %u, \"seed_bits\": %u, "
                        "\"stopping_time\": %u, \"total_steps\": %u, \"peak_bits\": %u, "
                        "\"peak_ratio\": %.6f, \"bigint_fallback\": %s, \"seed\": \"%s\", "
                        "\"peak\": \"%s\"}",
                        (emitted > 0) ? ",\n" : "", r->family, r->k, r->seed_bits,
                        r->stopping_time, r->total_steps, r->peak_bits, r->peak_ratio_approx,
                        r->used_bigint_fallback ? "true" : "false", r->seed_dec, r->peak_dec);
                emitted++;
            }
        }
        fprintf(fp, "\n      ]\n");
        fprintf(fp, "    }\n");
    }

    fprintf(fp, "  },\n");
    fprintf(fp, "  \"telemetry\": {\n");
    if (m1 && m1->range_end > 0ULL) {
        double rate = (m1->elapsed_sec > 0.0) ? ((double)m1->verified_count / m1->elapsed_sec) : 0.0;
        fprintf(fp, "    \"mode1_seconds\": %.6f,\n", m1->elapsed_sec);
        fprintf(fp, "    \"mode1_seeds_per_sec\": %.0f,\n", rate);
        fprintf(fp, "    \"threads\": %u%s\n", m1->threads_used, run_m2 ? "," : "");
    }
    if (run_m2) {
        fprintf(fp, "    \"mode2_seconds\": %.6f\n", m2_elapsed);
    }
    fprintf(fp, "  }\n");
    fprintf(fp, "}\n");
}

static uint32_t default_threads(uint64_t range_end) {
    if (range_end < SEQ_CUTOFF) {
        return 1U;
    }
    long cpus = sysconf(_SC_NPROCESSORS_ONLN);
    if (cpus <= 1L) {
        return 1U;
    }
    return (cpus > 16L) ? 16U : (uint32_t)cpus;
}

static bool parse_u64(const char *s, uint64_t *out) {
    if (!s || *s == '\0' || *s == '-') {
        return false;
    }
    char *end = NULL;
    errno = 0;
    unsigned long long val = strtoull(s, &end, 10);
    if (errno != 0 || end == s || *end != '\0') {
        return false;
    }
    *out = (uint64_t)val;
    return true;
}

int main(int argc, char **argv) {
    uint64_t range_end = 0ULL;
    uint32_t mersenne_max = 0U;
    bool run_m1 = false;
    bool run_m2 = false;
    uint32_t threads = 0U;
    const char *json_out = NULL;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--range-end") == 0 && i + 1 < argc) {
            if (!parse_u64(argv[++i], &range_end)) {
                fprintf(stderr, "Invalid --range-end value\n");
                return 2;
            }
            run_m1 = true;
        } else if (strcmp(argv[i], "--mersenne-max") == 0 && i + 1 < argc) {
            uint64_t tmp = 0ULL;
            if (!parse_u64(argv[++i], &tmp) || tmp > 1000ULL) {
                fprintf(stderr, "Invalid --mersenne-max value (0..1000)\n");
                return 2;
            }
            mersenne_max = (uint32_t)tmp;
            run_m2 = (mersenne_max > 0U);
        } else if (strcmp(argv[i], "--threads") == 0 && i + 1 < argc) {
            uint64_t tmp = 0ULL;
            if (!parse_u64(argv[++i], &tmp) || tmp < 1ULL || tmp > 64ULL) {
                fprintf(stderr, "Invalid --threads value (1..64)\n");
                return 2;
            }
            threads = (uint32_t)tmp;
        } else if (strcmp(argv[i], "--json-out") == 0 && i + 1 < argc) {
            json_out = argv[++i];
        } else if (strcmp(argv[i], "--help") == 0 || strcmp(argv[i], "-h") == 0) {
            fprintf(stderr,
                    "Usage: %s [--range-end N] [--mersenne-max K] [--threads T] "
                    "[--json-out PATH|-]\n",
                    argv[0]);
            return 0;
        } else {
            fprintf(stderr, "Unknown argument: %s\n", argv[i]);
            return 2;
        }
    }

    if (!run_m1 && !run_m2) {
        fprintf(stderr, "Specify --range-end N and/or --mersenne-max K\n");
        return 2;
    }

    mode1_result_t m1;
    memset(&m1, 0, sizeof(m1));
    if (run_m1 && range_end > 0ULL) {
        uint32_t use_threads = (threads > 0U) ? threads : default_threads(range_end);
        if (!run_mode1(range_end, use_threads, &m1)) {
            fprintf(stderr, "ALERT: Mode 1 failed or overflowed at seed %" PRIu64 "\n",
                    m1.failure_seed);
            return 10;
        }
    }

    mersenne_record_t *m2_recs = NULL;
    size_t m2_count = 0U;
    uint64_t u128_fallbacks = 0ULL;
    uint64_t silent_overflows = 0ULL;
    double m2_elapsed = 0.0;

    if (run_m2) {
        struct timespec t0, t1;
        clock_gettime(CLOCK_MONOTONIC, &t0);
        size_t total_m2 = (size_t)mersenne_max * 3U;
        m2_recs = calloc(total_m2, sizeof(mersenne_record_t));
        if (!m2_recs) {
            fprintf(stderr, "ERROR: Failed to allocate mode2 results\n");
            return 1;
        }
        static const struct {
            const char *name;
            uint64_t mult;
        } families[3] = {
            {"2^k-1", 1ULL},
            {"3*2^k-1", 3ULL},
            {"27*2^k-1", 27ULL},
        };
        for (size_t f = 0; f < 3; f++) {
            for (uint32_t k = 1U; k <= mersenne_max; k++) {
                if (!test_mersenne_seed(families[f].name, families[f].mult, k,
                                        &m2_recs[m2_count], &u128_fallbacks,
                                        &silent_overflows)) {
                    fprintf(stderr, "ALERT: Mode 2 failed on %s at k=%u\n", families[f].name, k);
                    free(m2_recs);
                    return 11;
                }
                m2_count++;
            }
        }
        clock_gettime(CLOCK_MONOTONIC, &t1);
        m2_elapsed = (double)(t1.tv_sec - t0.tv_sec) +
                     (double)(t1.tv_nsec - t0.tv_nsec) * 1e-9;
    }

    FILE *out_fp = stdout;
    if (json_out && strcmp(json_out, "-") != 0) {
        out_fp = fopen(json_out, "w");
        if (!out_fp) {
            fprintf(stderr, "ERROR: Cannot open %s for writing\n", json_out);
            free(m2_recs);
            return 1;
        }
    }

    write_json_output(out_fp, run_m1 ? &m1 : NULL, run_m2, mersenne_max, m2_recs, m2_count,
                      u128_fallbacks, silent_overflows, m2_elapsed);

    if (out_fp != stdout) {
        fclose(out_fp);
    }
    free(m2_recs);
    return 0;
}
