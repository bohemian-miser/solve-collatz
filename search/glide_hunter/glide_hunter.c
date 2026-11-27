/*
 * glide_hunter.c — High-throughput Collatz (3n + 1) stopping-time & extreme-glide hunter.
 *
 * Track B (`Disprove/`) off-kernel search engine for `solve-collatz` (`DISPROVE-003` Phase 5).
 *
 * Features:
 *   - Strict `uint64_t` -> `__uint128_t` -> `bigint_t` 3-tier arithmetic (zero silent wraparound;
 *     `overflow_count` and `u128_bigint_fallbacks` audited).
 *   - Configurable mod-2^B affine stopping-time drop sieve (`--sieve-bits 0|16|18|20|22|24`):
 *     - mod 2^20: 1,021,248 / 1,048,576 (97.3938%) residues drop < n.
 *     - mod 2^22: 4,101,082 / 4,194,304 (97.7774%) residues drop < n.
 *     - mod 2^24: 16,490,635 / 16,777,216 (98.2918%) residues drop < n, leaving only 286,581
 *       uncovered residues (`1.7082%`), traversed directly via `g_uncovered[]` for n >= tau_cap.
 *   - Syracuse odd-step shortcut (`__builtin_ctzll` / `ctz128`) with exact first-drop recovery.
 *   - Block-parallel deterministic execution (`R <= L + L/32` + explicit `m < block_L` guard).
 *   - Mode 1 (`--range-end N`): verifies finite stopping time for all 1 <= n <= N and tracks
 *     exact record stopping times, record total stopping times, and exact peak-ratio glides.
 *   - Mode 2 (`--mersenne-max K`): multi-threaded structured high-glide stress tests across
 *     Mersenne lifts `2^k*{1,3,27}-1`, extended lifts `2^k*{5,7,9}-1`, `2^k+1`, `2^k-3` (k>=2),
 *     and Terras/Roosendaal lifts `2^k*{703,9663,77671,319804831}-1` up to k <= K with exact
 *     `bigint_t` arithmetic.
 *   - Explicit `--max-steps` budget (zero silent truncation) with Brent cycle detection and
 *     Lean-ready `NontrivialCycleCert` / divergence diagnostics on any non-dropping seed.
 *   - Deterministic, RFC-8259-strict, SHA-256-ready canonical JSON output.
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

#define MAX_SIEVE_BITS 24U
#define MAX_SIEVE_SIZE (1U << MAX_SIEVE_BITS)
#define DEFAULT_SIEVE_BITS 24U
#define TAU_CACHE_CAP 250000000ULL
#define SEQ_CUTOFF (1ULL << 20)
#define MAX_RECORD_CAP 2048U
#define BIGINT_MAX_LIMBS 256U
#define DEFAULT_MAX_STEPS 2000000U
#define MAX_ALLOWED_STEPS 100000000U
#define MAX_MERSENNE_K 4000ULL

static const uint64_t U64_SAFE_3N1 = (UINT64_MAX - 1ULL) / 3ULL;
static const u128 U128_SAFE_3N1 = (~(u128)0 - 1U) / 3U;

/* 16-byte affine pre-drop descriptor (`shift_s == 0` means no guaranteed drop within B halvings). */
typedef struct {
    uint32_t pow3;
    uint32_t add_c;
    float max_pre_drop_ratio;
    uint16_t min_n;
    uint8_t shift_s;
    uint8_t steps;
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
    double log2_glide_ratio;
    double peak_ratio;
    bool used_bigint_fallback;
    bool verified_hits_one;
    char seed_dec[128];
    char peak_dec[256];
} mersenne_record_t;

typedef struct {
    bool triggered;
    char mode[16];
    char kind[32];
    char family[32];
    uint32_t k;
    uint32_t steps_executed;
    uint32_t max_steps_budget;
    uint32_t cycle_period;
    uint32_t peak_bits;
    uint32_t last_bits;
    char seed_dec[128];
    char cycle_start_dec[128];
    char peak_dec[256];
    char last_dec[256];
} failure_diagnostic_t;

/* Dynamic affine table, drop bitset, and sorted uncovered-residue list. */
static sieve_entry_t *g_sieve = NULL;
static uint64_t *g_sieve_fast = NULL;
static uint32_t *g_uncovered = NULL;
static uint32_t g_uncovered_count = 0U;
static uint32_t g_sieve_bits = DEFAULT_SIEVE_BITS;
static uint32_t g_sieve_size = (1U << DEFAULT_SIEVE_BITS);
static uint32_t g_sieve_mask = (1U << DEFAULT_SIEVE_BITS) - 1U;
static uint8_t g_sieve_max_steps = 0U;
static uint16_t g_sieve_max_min_n = 0U;
static double g_sieve_max_ratio = 1.0;

static void free_sieve(void) {
    free(g_sieve);
    free(g_sieve_fast);
    free(g_uncovered);
    g_sieve = NULL;
    g_sieve_fast = NULL;
    g_uncovered = NULL;
    g_uncovered_count = 0U;
}

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
    if (bufsz == 0U) {
        return;
    }
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

static bool init_sieve(uint32_t sieve_bits, uint32_t *out_covered) {
    free_sieve();
    g_sieve_bits = sieve_bits;
    g_sieve_size = (sieve_bits == 0U) ? 1U : (1U << sieve_bits);
    g_sieve_mask = g_sieve_size - 1U;
    g_sieve_max_steps = 0U;
    g_sieve_max_min_n = 0U;
    g_sieve_max_ratio = 1.0;
    *out_covered = 0U;

    if (sieve_bits == 0U) {
        return true;
    }
    if (sieve_bits > MAX_SIEVE_BITS) {
        return false;
    }

    g_sieve = (sieve_entry_t *)malloc((size_t)g_sieve_size * sizeof(sieve_entry_t));
    g_sieve_fast = (uint64_t *)calloc((size_t)(g_sieve_size / 64U), sizeof(uint64_t));
    size_t uncov_cap = (size_t)g_sieve_size / 16U + 1024U;
    if (uncov_cap > (size_t)g_sieve_size) {
        uncov_cap = (size_t)g_sieve_size;
    }
    g_uncovered = (uint32_t *)malloc(uncov_cap * sizeof(uint32_t));
    if (!g_sieve || !g_sieve_fast || !g_uncovered) {
        free_sieve();
        return false;
    }

    uint32_t covered = 0U;
    for (uint32_t r = 0U; r < g_sieve_size; r++) {
        /* For B <= 24, pow3 <= 3^24 < 2^39 and add_c < 2^39, strictly within uint64_t. */
        uint64_t pow3 = 1ULL;
        uint64_t add_c = 0ULL;
        uint64_t val = r;
        uint8_t s = 0U;
        uint8_t k = 0U;
        double max_ratio = 1.0;
        bool drops = false;
        uint16_t min_n = 0U;

        while (s < sieve_bits) {
            if ((val & 1ULL) == 0ULL) {
                val >>= 1;
                s++;
            } else {
                k++;
                pow3 *= 3ULL;
                add_c = 3ULL * add_c + (1ULL << s);
                double upper = ((double)pow3 + (double)add_c / (double)g_sieve_size) /
                               (double)(1ULL << s);
                if (upper > max_ratio) {
                    max_ratio = upper;
                }
                val = (3ULL * val + 1ULL) >> 1;
                s++;
            }
            uint64_t pow2s = 1ULL << s;
            if (pow3 < pow2s) {
                uint64_t denom = pow2s - pow3;
                uint64_t mn = add_c / denom;
                if (mn <= 65535ULL && pow3 <= UINT32_MAX && add_c <= UINT32_MAX) {
                    drops = true;
                    min_n = (uint16_t)mn;
                }
                break;
            }
        }

        if (drops) {
            uint8_t total_steps = (uint8_t)(k + s);
            /* Round pre-drop ratio up by 1e-6 so float comparison is strictly conservative. */
            float safe_ratio = nextafterf((float)(max_ratio * (1.0 + 1e-6)), INFINITY);
            g_sieve[r].pow3 = (uint32_t)pow3;
            g_sieve[r].add_c = (uint32_t)add_c;
            g_sieve[r].max_pre_drop_ratio = safe_ratio;
            g_sieve[r].min_n = min_n;
            g_sieve[r].shift_s = s;
            g_sieve[r].steps = total_steps;
            g_sieve_fast[r >> 6] |= (1ULL << (r & 63U));

            if (total_steps > g_sieve_max_steps) {
                g_sieve_max_steps = total_steps;
            }
            if (min_n > g_sieve_max_min_n) {
                g_sieve_max_min_n = min_n;
            }
            if ((double)safe_ratio > g_sieve_max_ratio) {
                g_sieve_max_ratio = (double)safe_ratio;
            }
            covered++;
        } else {
            g_sieve[r] = (sieve_entry_t){0};
            if (g_uncovered_count >= uncov_cap) {
                uncov_cap *= 2U;
                uint32_t *grown = (uint32_t *)realloc(g_uncovered, uncov_cap * sizeof(uint32_t));
                if (!grown) {
                    free_sieve();
                    return false;
                }
                g_uncovered = grown;
            }
            g_uncovered[g_uncovered_count++] = r;
        }
    }
    *out_covered = covered;
    return true;
}

/* ---------------- Arbitrary-Precision BigInt Fallback & Diagnostics ---------------- */

static void bi_copy(bigint_t *dst, const bigint_t *src) {
    dst->len = src->len;
    if (src->len > 0U) {
        memcpy(dst->limbs, src->limbs, src->len * sizeof(uint64_t));
    }
}

static void bi_from_u64(bigint_t *a, uint64_t v) {
    a->limbs[0] = v;
    a->len = (v == 0ULL) ? 0U : 1U;
}

static void bi_from_u128(bigint_t *a, u128 v) {
    if (v == 0U) {
        a->len = 0U;
        return;
    }
    a->limbs[0] = (uint64_t)v;
    uint64_t hi = (uint64_t)(v >> 64);
    if (hi != 0ULL) {
        a->limbs[1] = hi;
        a->len = 2U;
    } else {
        a->len = 1U;
    }
}

static bool bi_add_u64(bigint_t *a, uint64_t v) {
    if (v == 0ULL) {
        return true;
    }
    if (a->len == 0U) {
        bi_from_u64(a, v);
        return true;
    }
    u128 sum = (u128)a->limbs[0] + (u128)v;
    a->limbs[0] = (uint64_t)sum;
    uint64_t carry = (uint64_t)(sum >> 64);
    size_t i = 1U;
    while (carry != 0ULL && i < a->len) {
        u128 s2 = (u128)a->limbs[i] + (u128)carry;
        a->limbs[i] = (uint64_t)s2;
        carry = (uint64_t)(s2 >> 64);
        i++;
    }
    if (carry != 0ULL) {
        if (a->len >= BIGINT_MAX_LIMBS) {
            return false;
        }
        a->limbs[a->len++] = carry;
    }
    return true;
}

static bool bi_sub_u64(bigint_t *a, uint64_t v) {
    if (v == 0ULL) {
        return true;
    }
    if (a->len == 0U) {
        return false;
    }
    uint64_t borrow = v;
    for (size_t i = 0U; i < a->len && borrow != 0ULL; i++) {
        uint64_t cur = a->limbs[i];
        if (cur >= borrow) {
            a->limbs[i] = cur - borrow;
            borrow = 0ULL;
        } else {
            a->limbs[i] = cur - borrow; /* Unsigned wrap mod 2^64 borrows 1 from next limb. */
            borrow = 1ULL;
        }
    }
    if (borrow != 0ULL) {
        return false;
    }
    while (a->len > 0U && a->limbs[a->len - 1] == 0ULL) {
        a->len--;
    }
    return true;
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

/* Returns log2(a), or 0.0 as a JSON-safe sentinel when a == 0. */
static double bi_log2(const bigint_t *a) {
    if (a->len == 0) {
        return 0.0;
    }
    size_t top_idx = a->len - 1;
    uint64_t top_val = a->limbs[top_idx];
    if (top_val == 0ULL) {
        return 0.0;
    }
    uint32_t bits = bi_bitlen(a);
    if (bits == 0) {
        return 0.0;
    }
    int clz = __builtin_clzll(top_val);
    uint64_t mantissa_bits = 0ULL;
    if (clz <= 63 - 53) {
        mantissa_bits = top_val >> (63 - clz - 53);
    } else {
        int needed = 53 - (63 - clz);
        uint64_t hi = top_val << needed;
        uint64_t lo = (top_idx > 0) ? (a->limbs[top_idx - 1] >> (64 - needed)) : 0ULL;
        mantissa_bits = hi | lo;
    }
    double frac = (double)mantissa_bits / (double)(1ULL << 53);
    return (double)(bits - 1) + log2(frac);
}

static void bi_to_dec(const bigint_t *a, char *buf, size_t bufsz) {
    if (bufsz == 0U) {
        return;
    }
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

static bool bi_collatz_step(bigint_t *a) {
    if (a->len == 0) {
        return false;
    }
    if ((a->limbs[0] & 1ULL) == 0ULL) {
        bi_rshift_one(a);
        return true;
    }
    return bi_mul3_add1(a);
}

/* Brent cycle detection + divergence diagnostics when a seed fails to drop within budget. */
static void diagnose_non_dropping_seed(const bigint_t *seed_bi, const char *mode_name,
                                       const char *family_name, uint32_t k,
                                       uint32_t max_steps_budget, const char *fallback_kind,
                                       failure_diagnostic_t *diag) {
    memset(diag, 0, sizeof(*diag));
    diag->triggered = true;
    snprintf(diag->mode, sizeof(diag->mode), "%s", mode_name);
    snprintf(diag->family, sizeof(diag->family), "%s", family_name ? family_name : "");
    diag->k = k;
    diag->max_steps_budget = max_steps_budget;
    bi_to_dec(seed_bi, diag->seed_dec, sizeof(diag->seed_dec));

    bigint_t tortoise = *seed_bi;
    bigint_t hare = *seed_bi;
    bigint_t peak = *seed_bi;

    if (strcmp(fallback_kind, "step_budget_exceeded") == 0) {
        uint32_t power = 1U;
        uint32_t lam = 1U;
        if (!bi_collatz_step(&hare)) {
            snprintf(diag->kind, sizeof(diag->kind), "bigint_limb_overflow");
            diag->peak_bits = bi_bitlen(&peak);
            diag->last_bits = bi_bitlen(&hare);
            bi_to_dec(&peak, diag->peak_dec, sizeof(diag->peak_dec));
            bi_to_dec(&hare, diag->last_dec, sizeof(diag->last_dec));
            return;
        }
        if (bi_cmp(&hare, &peak) > 0) {
            peak = hare;
        }
        uint32_t steps = 1U;
        bool found_cycle = false;
        while (steps < max_steps_budget && !bi_is_one(&hare)) {
            if (bi_cmp(&tortoise, &hare) == 0) {
                found_cycle = true;
                break;
            }
            if (power == lam) {
                tortoise = hare;
                power <<= 1;
                lam = 0U;
            }
            if (!bi_collatz_step(&hare)) {
                snprintf(diag->kind, sizeof(diag->kind), "bigint_limb_overflow");
                diag->steps_executed = steps;
                diag->peak_bits = bi_bitlen(&peak);
                diag->last_bits = bi_bitlen(&hare);
                bi_to_dec(&peak, diag->peak_dec, sizeof(diag->peak_dec));
                bi_to_dec(&hare, diag->last_dec, sizeof(diag->last_dec));
                return;
            }
            if (bi_cmp(&hare, &peak) > 0) {
                peak = hare;
            }
            lam++;
            steps++;
        }

        diag->steps_executed = steps;
        diag->peak_bits = bi_bitlen(&peak);
        diag->last_bits = bi_bitlen(&hare);
        bi_to_dec(&peak, diag->peak_dec, sizeof(diag->peak_dec));
        bi_to_dec(&hare, diag->last_dec, sizeof(diag->last_dec));

        if (found_cycle && !bi_is_one(&hare)) {
            /* Locate exact cycle entry point `mu` for NontrivialCycleCert. */
            tortoise = *seed_bi;
            hare = *seed_bi;
            for (uint32_t i = 0U; i < lam; i++) {
                (void)bi_collatz_step(&hare);
            }
            while (bi_cmp(&tortoise, &hare) != 0) {
                (void)bi_collatz_step(&tortoise);
                (void)bi_collatz_step(&hare);
            }
            snprintf(diag->kind, sizeof(diag->kind), "nontrivial_cycle");
            diag->cycle_period = lam;
            bi_to_dec(&tortoise, diag->cycle_start_dec, sizeof(diag->cycle_start_dec));
            return;
        }
    }

    snprintf(diag->kind, sizeof(diag->kind), "%s", fallback_kind);
    if (diag->steps_executed == 0U) {
        diag->steps_executed = max_steps_budget;
    }
    if (diag->peak_bits == 0U) {
        diag->peak_bits = bi_bitlen(&peak);
        diag->last_bits = diag->peak_bits;
        bi_to_dec(&peak, diag->peak_dec, sizeof(diag->peak_dec));
        bi_to_dec(&peak, diag->last_dec, sizeof(diag->last_dec));
    }
}

static void print_failure_diagnostic_stderr(const failure_diagnostic_t *diag) {
    if (!diag || !diag->triggered) {
        return;
    }
    fprintf(stderr,
            "DIAGNOSTIC [%s/%s]: seed=%s steps=%u/%u peak_bits=%u last_bits=%u\n",
            diag->mode, diag->kind, diag->seed_dec, diag->steps_executed,
            diag->max_steps_budget, diag->peak_bits, diag->last_bits);
    if (strcmp(diag->kind, "nontrivial_cycle") == 0) {
        fprintf(stderr,
                "-- Lean-ready NontrivialCycleCert (Collatz/Disprove/Cert.lean):\n"
                "import Collatz.Disprove.Cert\n"
                "theorem discovered_nontrivial_cycle : SolveCollatz.CollatzDisproof :=\n"
                "  SolveCollatz.Disprove.NontrivialCycleCert.disproves_collatz\n"
                "    { start := %s\n"
                "      period := %u\n"
                "      start_pos := by decide\n"
                "      period_pos := by decide\n"
                "      returns := by decide\n"
                "      avoids_one := by decide }\n",
                diag->cycle_start_dec, diag->cycle_period);
    }
}

/* Exact bigint_t orbit continuation when u128 hits U128_SAFE_3N1. */
static bool exact_orbit_stats_bi(uint64_t n, const bigint_t *start_cur, const bigint_t *start_peak,
                                 uint32_t start_total, uint32_t start_stop, bool start_have_stop,
                                 uint32_t max_steps, uint32_t *out_stop, uint32_t *out_total,
                                 u128 *out_peak, uint64_t *overflow_count) {
    bigint_t n_bi, cur, peak;
    bi_from_u64(&n_bi, n);
    bi_copy(&cur, start_cur);
    bi_copy(&peak, start_peak);
    uint32_t total = start_total;
    uint32_t stop = start_stop;
    bool have_stop = start_have_stop;

    while (!bi_is_one(&cur)) {
        if (total >= max_steps) {
            return false;
        }
        if ((cur.limbs[0] & 1ULL) == 0ULL) {
            uint32_t tz = bi_rshift_tz(&cur);
            if (!have_stop && bi_cmp(&cur, &n_bi) < 0) {
                bigint_t tmp;
                bi_copy(&tmp, &cur);
                (void)bi_shl(&tmp, tz);
                uint32_t j = 1U;
                bi_rshift_one(&tmp);
                while (j < tz && bi_cmp(&tmp, &n_bi) >= 0) {
                    bi_rshift_one(&tmp);
                    j++;
                }
                stop = total + j;
                have_stop = true;
            }
            total += tz;
        } else {
            if (!bi_mul3_add1(&cur)) {
                (*overflow_count)++;
                return false;
            }
            if (bi_cmp(&cur, &peak) > 0) {
                bi_copy(&peak, &cur);
            }
            bigint_t pre_shift;
            bi_copy(&pre_shift, &cur);
            uint32_t tz = bi_rshift_tz(&cur);
            if (!have_stop && bi_cmp(&cur, &n_bi) < 0) {
                uint32_t j = 1U;
                bi_rshift_one(&pre_shift);
                while (j < tz && bi_cmp(&pre_shift, &n_bi) >= 0) {
                    bi_rshift_one(&pre_shift);
                    j++;
                }
                stop = total + 1U + j;
                have_stop = true;
            }
            total += 1U + tz;
        }
    }
    if (peak.len > 2U) {
        (*overflow_count)++;
        return false;
    }
    *out_stop = stop;
    *out_total = total;
    *out_peak = (peak.len == 0U)
                    ? (u128)0U
                    : ((peak.len == 1U) ? (u128)peak.limbs[0]
                                        : (((u128)peak.limbs[1] << 64) | (u128)peak.limbs[0]));
    return true;
}

/* Compute exact full orbit to 1 for a single u64 seed (used only for rare record seeds). */
static bool exact_orbit_stats_u64(uint64_t n, uint32_t max_steps, uint32_t *out_stop,
                                  uint32_t *out_total, u128 *out_peak,
                                  uint64_t *overflow_count) {
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
        if (total >= max_steps) {
            return false;
        }
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
                bigint_t cur_bi, peak_bi;
                bi_from_u128(&cur_bi, cur);
                bi_from_u128(&peak_bi, peak);
                return exact_orbit_stats_bi(n, &cur_bi, &peak_bi, total, stop, have_stop,
                                            max_steps, out_stop, out_total, out_peak,
                                            overflow_count);
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

static bool push_candidate(record_list_t *list, uint64_t n, uint32_t stop, uint32_t total,
                           u128 peak) {
    if (list->count >= MAX_RECORD_CAP) {
        return false;
    }
    list->items[list->count++] = (record_t){n, stop, total, peak};
    return true;
}

/* Exact bigint_t fallback when Mode 1 exceeds U128_SAFE_3N1. */
static bool verify_seed_until_below_bi(uint64_t n, uint64_t threshold, u128 start_cur_u128,
                                       u128 start_peak_u128, uint32_t start_steps,
                                       uint32_t start_stop, bool start_have_stop,
                                       uint32_t max_steps, uint32_t *out_stop,
                                       uint32_t *out_steps_to_cur, uint64_t *out_cur_below,
                                       u128 *out_peak, uint64_t *overflow_count,
                                       uint64_t *u128_fallbacks, const char **fail_reason) {
    (*u128_fallbacks)++;
    bigint_t n_bi, thresh_bi, cur, peak;
    bi_from_u64(&n_bi, n);
    bi_from_u64(&thresh_bi, threshold);
    bi_from_u128(&cur, start_cur_u128);
    bi_from_u128(&peak, start_peak_u128);
    uint32_t steps = start_steps;
    uint32_t stop = start_stop;
    bool have_stop = start_have_stop;

    while (bi_cmp(&cur, &thresh_bi) >= 0) {
        if ((cur.limbs[0] & 1ULL) == 0ULL) {
            bigint_t pre_shift;
            bi_copy(&pre_shift, &cur);
            uint32_t tz = bi_rshift_tz(&cur);
            if (!have_stop && bi_cmp(&cur, &n_bi) < 0) {
                uint32_t j = 1U;
                bi_rshift_one(&pre_shift);
                while (j < tz && bi_cmp(&pre_shift, &n_bi) >= 0) {
                    bi_rshift_one(&pre_shift);
                    j++;
                }
                stop = steps + j;
                have_stop = true;
            }
            steps += tz;
        } else {
            if (!bi_mul3_add1(&cur)) {
                (*overflow_count)++;
                *fail_reason = "bigint_limb_overflow";
                return false;
            }
            if (bi_cmp(&cur, &peak) > 0) {
                bi_copy(&peak, &cur);
            }
            bigint_t pre_shift;
            bi_copy(&pre_shift, &cur);
            uint32_t tz = bi_rshift_tz(&cur);
            if (!have_stop && bi_cmp(&cur, &n_bi) < 0) {
                uint32_t j = 1U;
                bi_rshift_one(&pre_shift);
                while (j < tz && bi_cmp(&pre_shift, &n_bi) >= 0) {
                    bi_rshift_one(&pre_shift);
                    j++;
                }
                stop = steps + 1U + j;
                have_stop = true;
            }
            steps += 1U + tz;
        }
        if (steps > max_steps) {
            *fail_reason = "step_budget_exceeded";
            return false;
        }
    }
    *out_stop = stop;
    *out_steps_to_cur = steps;
    *out_cur_below = (cur.len == 0U) ? 0ULL : cur.limbs[0];
    *out_peak = (peak.len <= 2U)
                    ? ((peak.len == 0U)
                           ? (u128)0U
                           : ((peak.len == 1U)
                                  ? (u128)peak.limbs[0]
                                  : (((u128)peak.limbs[1] << 64) | (u128)peak.limbs[0])))
                    : (~(u128)0);
    return true;
}

/* Simulate one seed n >= 2 until cur < threshold (where threshold <= n). */
static inline bool verify_seed_until_below(uint64_t n, uint64_t threshold, uint32_t max_steps,
                                           uint32_t *out_stop, uint32_t *out_steps_to_cur,
                                           uint64_t *out_cur_below, u128 *out_peak,
                                           uint64_t *overflow_count, uint64_t *u128_fallbacks,
                                           const char **fail_reason) {
    uint64_t c64 = n;
    uint64_t p64 = n;
    uint32_t steps = 0U;
    uint32_t stop = 0U;
    bool have_stop = false;

    /* Tier 1: fast native uint64_t loop while 3 * c64 + 1 fits in uint64_t. */
    while (c64 >= threshold && c64 <= U64_SAFE_3N1) {
        if ((c64 & 1ULL) == 0ULL) {
            int tz = __builtin_ctzll(c64);
            uint64_t nxt = c64 >> tz;
            if (!have_stop && nxt < n) {
                uint32_t j = 1U;
                uint64_t tmp = c64 >> 1;
                while (j < (uint32_t)tz && tmp >= n) {
                    tmp >>= 1;
                    j++;
                }
                stop = steps + j;
                have_stop = true;
            }
            c64 = nxt;
            steps += (uint32_t)tz;
        } else {
            uint64_t nxt = 3ULL * c64 + 1ULL;
            if (nxt > p64) {
                p64 = nxt;
            }
            int tz = __builtin_ctzll(nxt);
            uint64_t reduced = nxt >> tz;
            if (!have_stop && reduced < n) {
                uint32_t j = 1U;
                uint64_t tmp = nxt >> 1;
                while (j < (uint32_t)tz && tmp >= n) {
                    tmp >>= 1;
                    j++;
                }
                stop = steps + 1U + j;
                have_stop = true;
            }
            c64 = reduced;
            steps += 1U + (uint32_t)tz;
        }
        if (steps > max_steps) {
            *fail_reason = "step_budget_exceeded";
            return false;
        }
    }

    if (c64 < threshold) {
        *out_stop = stop;
        *out_steps_to_cur = steps;
        *out_cur_below = c64;
        *out_peak = (u128)p64;
        return true;
    }

    /* Tier 2: exact u128 continuation when intermediate orbit exceeds 62.4 bits. */
    u128 cur = (u128)c64;
    u128 peak = (u128)p64;
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
                return verify_seed_until_below_bi(n, threshold, cur, peak, steps, stop, have_stop,
                                                  max_steps, out_stop, out_steps_to_cur,
                                                  out_cur_below, out_peak, overflow_count,
                                                  u128_fallbacks, fail_reason);
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
        if (steps > max_steps) {
            *fail_reason = "step_budget_exceeded";
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
    uint32_t max_steps;
    uint32_t init_best_stop;
    uint32_t init_best_total;
    u128 init_best_peak;
    uint64_t init_best_peak_n;
    record_list_t cand_stop;
    record_list_t cand_total;
    record_list_t cand_peak;
    uint64_t sieved_count;
    uint64_t overflow_count;
    uint64_t u128_fallbacks;
    uint64_t failure_seed;
    const char *failure_reason;
    bool ok;
} worker_ctx_t;

static void *worker_run(void *arg) {
    worker_ctx_t *ctx = (worker_ctx_t *)arg;
    const uint32_t init_best_stop = ctx->init_best_stop;
    const double init_best_ratio = ratio_to_double(ctx->init_best_peak, ctx->init_best_peak_n);
    uint32_t best_stop = init_best_stop;
    uint32_t best_total = ctx->init_best_total;
    u128 best_peak = ctx->init_best_peak;
    uint64_t best_peak_n = ctx->init_best_peak_n;
    const uint64_t block_L = ctx->block_L;
    uint16_t *const tau = ctx->tau;
    const uint64_t tau_cap = ctx->tau_cap;
    const uint32_t max_steps = ctx->max_steps;
    const uint32_t sieve_mask = g_sieve_mask;
    const uint64_t sieve_size = (uint64_t)g_sieve_size;
    const bool use_sieve = (g_sieve_bits > 0U);
    const bool fast_l1_eligible = use_sieve && (init_best_stop > g_sieve_max_steps) &&
                                  (init_best_ratio > g_sieve_max_ratio);
    uint64_t fast_thresh = (tau_cap > sieve_size) ? tau_cap : sieve_size;
    if ((uint64_t)g_sieve_max_min_n + 1ULL > fast_thresh) {
        fast_thresh = (uint64_t)g_sieve_max_min_n + 1ULL;
    }
    uint64_t sieved = 0ULL;

    /* Phase A: exact tau-cached or pre-threshold region [start_n, min(end_n, fast_thresh - 1)]. */
    uint64_t phase_a_end = ctx->end_n;
    if (fast_l1_eligible && phase_a_end >= fast_thresh) {
        phase_a_end = (fast_thresh > 0ULL) ? (fast_thresh - 1ULL) : 0ULL;
    }

    for (uint64_t n = ctx->start_n; fast_l1_eligible ? (n <= phase_a_end && fast_thresh > 0ULL)
                                                     : (n <= ctx->end_n);
         n++) {
        if (use_sieve && n >= sieve_size) {
            const sieve_entry_t *ent = &g_sieve[n & sieve_mask];
            if (ent->shift_s > 0U && n > (uint64_t)ent->min_n && init_best_stop > ent->steps &&
                init_best_ratio > (double)ent->max_pre_drop_ratio) {
                if (n >= tau_cap) {
                    sieved++;
                    continue;
                }
                uint64_t m = (uint64_t)(((u128)ent->pow3 * (u128)n + (u128)ent->add_c) >>
                                        ent->shift_s);
                /* Explicit guard: only read tau[m] when m lies strictly below the active parallel block. */
                if (m < block_L) {
                    sieved++;
                    uint32_t tot = (uint32_t)ent->steps + (uint32_t)tau[m];
                    if (tot >= 65535U) {
                        ctx->overflow_count++;
                        ctx->ok = false;
                        ctx->failure_seed = n;
                        ctx->failure_reason = "tau_cache_overflow";
                        return NULL;
                    }
                    tau[n] = (uint16_t)tot;
                    if (tot > best_total) {
                        best_total = tot;
                        if (!push_candidate(&ctx->cand_total, n, ent->steps, tot, 0U)) {
                            ctx->ok = false;
                            ctx->failure_seed = n;
                            ctx->failure_reason = "record_cap_exceeded";
                            return NULL;
                        }
                    }
                    continue;
                }
            }
        }

        uint32_t stop = 0U;
        uint32_t steps_to_cur = 0U;
        uint64_t cur_below = 0ULL;
        u128 peak = 0U;
        const char *fail_reason = "unknown";
        if (!verify_seed_until_below(n, block_L, max_steps, &stop, &steps_to_cur, &cur_below,
                                     &peak, &ctx->overflow_count, &ctx->u128_fallbacks,
                                     &fail_reason)) {
            ctx->ok = false;
            ctx->failure_seed = n;
            ctx->failure_reason = fail_reason;
            return NULL;
        }

        uint32_t tot = 0U;
        if (n < tau_cap && cur_below < tau_cap) {
            tot = steps_to_cur + (uint32_t)tau[cur_below];
            if (tot >= 65535U) {
                ctx->overflow_count++;
                ctx->ok = false;
                ctx->failure_seed = n;
                ctx->failure_reason = "tau_cache_overflow";
                return NULL;
            }
            tau[n] = (uint16_t)tot;
            if (tot > best_total) {
                best_total = tot;
                if (!push_candidate(&ctx->cand_total, n, stop, tot, peak)) {
                    ctx->ok = false;
                    ctx->failure_seed = n;
                    ctx->failure_reason = "record_cap_exceeded";
                    return NULL;
                }
            }
        }
        if (stop > best_stop) {
            best_stop = stop;
            if (!push_candidate(&ctx->cand_stop, n, stop, tot, peak)) {
                ctx->ok = false;
                ctx->failure_seed = n;
                ctx->failure_reason = "record_cap_exceeded";
                return NULL;
            }
        }
        if (cmp_ratio_u128_u64(peak, n, best_peak, best_peak_n) > 0) {
            best_peak = peak;
            best_peak_n = n;
            if (!push_candidate(&ctx->cand_peak, n, stop, tot, peak)) {
                ctx->ok = false;
                ctx->failure_seed = n;
                ctx->failure_reason = "record_cap_exceeded";
                return NULL;
            }
        }
    }

    /* Phase B: jump directly across uncovered residues mod 2^B when n >= max(tau_cap, 2^B). */
    if (fast_l1_eligible && ctx->end_n >= fast_thresh) {
        uint64_t tail_start = (ctx->start_n > fast_thresh) ? ctx->start_n : fast_thresh;
        if (tail_start <= ctx->end_n) {
            uint64_t total_tail = ctx->end_n - tail_start + 1ULL;
            uint64_t processed_uncovered = 0ULL;

            if (g_uncovered_count > 0U) {
                uint64_t base = tail_start & ~((uint64_t)sieve_mask);
                uint32_t start_rem = (uint32_t)(tail_start & (uint64_t)sieve_mask);
                uint32_t lo = 0U;
                uint32_t hi = g_uncovered_count;
                while (lo < hi) {
                    uint32_t mid = lo + ((hi - lo) >> 1);
                    if (g_uncovered[mid] < start_rem) {
                        lo = mid + 1U;
                    } else {
                        hi = mid;
                    }
                }
                uint32_t idx = lo;
                if (idx >= g_uncovered_count) {
                    idx = 0U;
                    if (base <= UINT64_MAX - sieve_size) {
                        base += sieve_size;
                    } else {
                        idx = g_uncovered_count;
                    }
                }
                while (idx < g_uncovered_count) {
                    uint64_t n = base + (uint64_t)g_uncovered[idx];
                    if (n < base || n > ctx->end_n) {
                        break;
                    }
                    processed_uncovered++;

                    uint32_t stop = 0U;
                    uint32_t steps_to_cur = 0U;
                    uint64_t cur_below = 0ULL;
                    u128 peak = 0U;
                    const char *fail_reason = "unknown";
                    if (!verify_seed_until_below(n, block_L, max_steps, &stop, &steps_to_cur,
                                                 &cur_below, &peak, &ctx->overflow_count,
                                                 &ctx->u128_fallbacks, &fail_reason)) {
                        ctx->ok = false;
                        ctx->failure_seed = n;
                        ctx->failure_reason = fail_reason;
                        return NULL;
                    }
                    if (stop > best_stop) {
                        best_stop = stop;
                        if (!push_candidate(&ctx->cand_stop, n, stop, 0U, peak)) {
                            ctx->ok = false;
                            ctx->failure_seed = n;
                            ctx->failure_reason = "record_cap_exceeded";
                            return NULL;
                        }
                    }
                    if (cmp_ratio_u128_u64(peak, n, best_peak, best_peak_n) > 0) {
                        best_peak = peak;
                        best_peak_n = n;
                        if (!push_candidate(&ctx->cand_peak, n, stop, 0U, peak)) {
                            ctx->ok = false;
                            ctx->failure_seed = n;
                            ctx->failure_reason = "record_cap_exceeded";
                            return NULL;
                        }
                    }

                    idx++;
                    if (idx == g_uncovered_count) {
                        idx = 0U;
                        if (base > UINT64_MAX - sieve_size) {
                            break;
                        }
                        base += sieve_size;
                    }
                }
            }
            sieved += (total_tail - processed_uncovered);
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
    uint64_t u128_fallbacks;
    uint64_t tau_exact_up_to;
    uint32_t sieve_bits;
    uint32_t sieve_modulus;
    uint32_t sieve_covered;
    uint32_t threads_used;
    bool all_converged;
    uint64_t failure_seed;
    const char *failure_reason;
    record_list_t stop_records;
    record_list_t total_records;
    record_list_t peak_records;
    double elapsed_sec;
} mode1_result_t;

static bool merge_candidates(const record_list_t *cands, record_list_t *global_recs,
                             uint32_t *best_stop, uint32_t *best_total, u128 *best_peak,
                             uint64_t *best_peak_n, int kind, uint32_t max_steps,
                             uint64_t *overflow_count, uint64_t *failure_seed,
                             const char **failure_reason) {
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
        if (!exact_orbit_stats_u64(n, max_steps, &stop, &total, &peak, overflow_count)) {
            *failure_seed = n;
            *failure_reason = "step_budget_exceeded";
            return false;
        }
        if (kind == 0 && stop > *best_stop) {
            *best_stop = stop;
            if (!push_candidate(global_recs, n, stop, total, peak)) {
                *failure_seed = n;
                *failure_reason = "record_cap_exceeded";
                return false;
            }
        } else if (kind == 1 && total > *best_total) {
            *best_total = total;
            if (!push_candidate(global_recs, n, stop, total, peak)) {
                *failure_seed = n;
                *failure_reason = "record_cap_exceeded";
                return false;
            }
        } else if (kind == 2 && cmp_ratio_u128_u64(peak, n, *best_peak, *best_peak_n) > 0) {
            *best_peak = peak;
            *best_peak_n = n;
            if (!push_candidate(global_recs, n, stop, total, peak)) {
                *failure_seed = n;
                *failure_reason = "record_cap_exceeded";
                return false;
            }
        }
    }
    return true;
}

static bool run_mode1(uint64_t range_end, uint32_t num_threads, uint32_t sieve_bits,
                      uint32_t max_steps, mode1_result_t *res, failure_diagnostic_t *diag) {
    memset(res, 0, sizeof(*res));
    res->range_end = range_end;
    res->sieve_bits = sieve_bits;
    if (!init_sieve(sieve_bits, &res->sieve_covered)) {
        fprintf(stderr, "ERROR: Failed to initialize mod-2^%u sieve\n", sieve_bits);
        res->failure_reason = "allocation_failed";
        return false;
    }
    res->sieve_modulus = g_sieve_size;
    if (range_end == 0ULL) {
        res->all_converged = true;
        free_sieve();
        return true;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    uint64_t tau_cap = (range_end < TAU_CACHE_CAP) ? (range_end + 1ULL) : TAU_CACHE_CAP;
    uint16_t *tau = (uint16_t *)calloc((size_t)tau_cap, sizeof(uint16_t));
    if (!tau) {
        fprintf(stderr, "ERROR: Failed to allocate tau cache of %" PRIu64 " entries\n", tau_cap);
        res->failure_reason = "allocation_failed";
        free_sieve();
        return false;
    }
    res->tau_exact_up_to = tau_cap - 1ULL;

    uint32_t best_stop = 0U;
    uint32_t best_total = 0U;
    u128 best_peak = 1U;
    uint64_t best_peak_n = 1ULL;

    /* n = 1 base record */
    tau[1] = 0U;
    (void)push_candidate(&res->stop_records, 1ULL, 0U, 0U, 1U);
    (void)push_candidate(&res->total_records, 1ULL, 0U, 0U, 1U);
    (void)push_candidate(&res->peak_records, 1ULL, 0U, 0U, 1U);
    res->verified_count = 1ULL;

    /* Sequential exact pass up to min(range_end, SEQ_CUTOFF - 1) */
    uint64_t seq_end = (range_end < SEQ_CUTOFF - 1ULL) ? range_end : (SEQ_CUTOFF - 1ULL);
    for (uint64_t n = 2ULL; n <= seq_end; n++) {
        if (sieve_bits > 0U && n >= g_sieve_size) {
            const sieve_entry_t *ent = &g_sieve[n & g_sieve_mask];
            if (ent->shift_s > 0U && n > (uint64_t)ent->min_n && best_stop > ent->steps &&
                ratio_to_double(best_peak, best_peak_n) > (double)ent->max_pre_drop_ratio) {
                res->sieved_count++;
                uint64_t m = (uint64_t)(((u128)ent->pow3 * (u128)n + (u128)ent->add_c) >>
                                        ent->shift_s);
                uint32_t tot = (uint32_t)ent->steps + (uint32_t)tau[m];
                if (tot >= 65535U) {
                    res->overflow_count++;
                    res->failure_seed = n;
                    res->failure_reason = "tau_cache_overflow";
                    bigint_t sbi;
                    bi_from_u64(&sbi, n);
                    diagnose_non_dropping_seed(&sbi, "mode1", "", 0U, max_steps,
                                               res->failure_reason, diag);
                    free(tau);
                    free_sieve();
                    return false;
                }
                tau[n] = (uint16_t)tot;
                if (tot > best_total) {
                    uint32_t es = 0U, et = 0U;
                    u128 ep = 0U;
                    if (!exact_orbit_stats_u64(n, max_steps, &es, &et, &ep,
                                               &res->overflow_count)) {
                        res->failure_seed = n;
                        res->failure_reason = "step_budget_exceeded";
                        bigint_t sbi;
                        bi_from_u64(&sbi, n);
                        diagnose_non_dropping_seed(&sbi, "mode1", "", 0U, max_steps,
                                                   res->failure_reason, diag);
                        free(tau);
                        free_sieve();
                        return false;
                    }
                    best_total = et;
                    if (!push_candidate(&res->total_records, n, es, et, ep)) {
                        res->failure_seed = n;
                        res->failure_reason = "record_cap_exceeded";
                        free(tau);
                        free_sieve();
                        return false;
                    }
                }
                res->verified_count++;
                continue;
            }
        }

        uint32_t stop = 0U;
        uint32_t steps_to_cur = 0U;
        uint64_t cur_below = 0ULL;
        u128 peak = 0U;
        const char *fail_reason = "unknown";
        if (!verify_seed_until_below(n, n, max_steps, &stop, &steps_to_cur, &cur_below, &peak,
                                     &res->overflow_count, &res->u128_fallbacks, &fail_reason)) {
            res->failure_seed = n;
            res->failure_reason = fail_reason;
            bigint_t sbi;
            bi_from_u64(&sbi, n);
            diagnose_non_dropping_seed(&sbi, "mode1", "", 0U, max_steps, fail_reason, diag);
            free(tau);
            free_sieve();
            return false;
        }
        uint32_t tot = steps_to_cur + (uint32_t)tau[cur_below];
        if (tot >= 65535U) {
            res->overflow_count++;
            res->failure_seed = n;
            res->failure_reason = "tau_cache_overflow";
            bigint_t sbi;
            bi_from_u64(&sbi, n);
            diagnose_non_dropping_seed(&sbi, "mode1", "", 0U, max_steps, res->failure_reason, diag);
            free(tau);
            free_sieve();
            return false;
        }
        tau[n] = (uint16_t)tot;

        bool need_stop = (stop > best_stop);
        bool need_total = (tot > best_total);
        bool need_peak = (cmp_ratio_u128_u64(peak, n, best_peak, best_peak_n) > 0);
        if (need_stop || need_total || need_peak) {
            uint32_t es = 0U, et = 0U;
            u128 ep = 0U;
            if (!exact_orbit_stats_u64(n, max_steps, &es, &et, &ep, &res->overflow_count)) {
                res->failure_seed = n;
                res->failure_reason = "step_budget_exceeded";
                bigint_t sbi;
                bi_from_u64(&sbi, n);
                diagnose_non_dropping_seed(&sbi, "mode1", "", 0U, max_steps,
                                           res->failure_reason, diag);
                free(tau);
                free_sieve();
                return false;
            }
            if (need_stop && es > best_stop) {
                best_stop = es;
                if (!push_candidate(&res->stop_records, n, es, et, ep)) {
                    res->failure_seed = n;
                    res->failure_reason = "record_cap_exceeded";
                    free(tau);
                    free_sieve();
                    return false;
                }
            }
            if (need_total && et > best_total) {
                best_total = et;
                if (!push_candidate(&res->total_records, n, es, et, ep)) {
                    res->failure_seed = n;
                    res->failure_reason = "record_cap_exceeded";
                    free(tau);
                    free_sieve();
                    return false;
                }
            }
            if (need_peak && cmp_ratio_u128_u64(ep, n, best_peak, best_peak_n) > 0) {
                best_peak = ep;
                best_peak_n = n;
                if (!push_candidate(&res->peak_records, n, es, et, ep)) {
                    res->failure_seed = n;
                    res->failure_reason = "record_cap_exceeded";
                    free(tau);
                    free_sieve();
                    return false;
                }
            }
        }
        res->verified_count++;
    }

    /* Block-parallel sweep from SEQ_CUTOFF to range_end: R <= L + L/32 + m < block_L guard. */
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
        free_sieve();
        res->failure_reason = "allocation_failed";
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
            ctxs[t].max_steps = max_steps;
            ctxs[t].init_best_stop = best_stop;
            ctxs[t].init_best_total = best_total;
            ctxs[t].init_best_peak = best_peak;
            ctxs[t].init_best_peak_n = best_peak_n;
            cur_start += sz;
        }

        if (active == 1U) {
            worker_run(&ctxs[0]);
        } else {
            uint32_t spawned = 0U;
            bool thread_err = false;
            for (uint32_t t = 0; t < active; t++) {
                int rc = pthread_create(&tids[t], NULL, worker_run, &ctxs[t]);
                if (rc != 0) {
                    fprintf(stderr, "ERROR: pthread_create(%u) failed: %s\n", t, strerror(rc));
                    thread_err = true;
                    break;
                }
                spawned++;
            }
            for (uint32_t t = 0; t < spawned; t++) {
                int rc = pthread_join(tids[t], NULL);
                if (rc != 0) {
                    fprintf(stderr, "ERROR: pthread_join(%u) failed: %s\n", t, strerror(rc));
                    thread_err = true;
                }
            }
            if (thread_err) {
                res->all_converged = false;
                res->failure_reason = "pthread_failure";
                free(ctxs);
                free(tids);
                free(tau);
                free_sieve();
                return false;
            }
        }

        for (uint32_t t = 0; t < active; t++) {
            res->overflow_count += ctxs[t].overflow_count;
            res->sieved_count += ctxs[t].sieved_count;
            res->u128_fallbacks += ctxs[t].u128_fallbacks;
            if (!ctxs[t].ok) {
                res->all_converged = false;
                res->failure_seed = ctxs[t].failure_seed;
                res->failure_reason = ctxs[t].failure_reason;
                bigint_t sbi;
                bi_from_u64(&sbi, ctxs[t].failure_seed);
                diagnose_non_dropping_seed(&sbi, "mode1", "", 0U, max_steps,
                                           ctxs[t].failure_reason, diag);
                free(ctxs);
                free(tids);
                free(tau);
                free_sieve();
                return false;
            }
        }
        for (uint32_t t = 0; t < active; t++) {
            if (!merge_candidates(&ctxs[t].cand_stop, &res->stop_records, &best_stop, &best_total,
                                  &best_peak, &best_peak_n, 0, max_steps, &res->overflow_count,
                                  &res->failure_seed, &res->failure_reason) ||
                !merge_candidates(&ctxs[t].cand_total, &res->total_records, &best_stop,
                                  &best_total, &best_peak, &best_peak_n, 1, max_steps,
                                  &res->overflow_count, &res->failure_seed, &res->failure_reason) ||
                !merge_candidates(&ctxs[t].cand_peak, &res->peak_records, &best_stop, &best_total,
                                  &best_peak, &best_peak_n, 2, max_steps, &res->overflow_count,
                                  &res->failure_seed, &res->failure_reason)) {
                bigint_t sbi;
                bi_from_u64(&sbi, res->failure_seed);
                diagnose_non_dropping_seed(&sbi, "mode1", "", 0U, max_steps,
                                           res->failure_reason, diag);
                free(ctxs);
                free(tids);
                free(tau);
                free_sieve();
                return false;
            }
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
    free_sieve();
    return res->all_converged;
}

static bool test_mersenne_seed(const char *family, uint64_t mult, int64_t offset, uint32_t k,
                               uint32_t max_steps, mersenne_record_t *out,
                               uint64_t *silent_overflows, failure_diagnostic_t *diag) {
    memset(out, 0, sizeof(*out));
    snprintf(out->family, sizeof(out->family), "%s", family);
    out->k = k;

    /* Exact seed n = mult * 2^k + offset in bigint_t (always exact). */
    bigint_t seed_bi;
    bi_from_u64(&seed_bi, mult);
    bool ok_seed = bi_shl(&seed_bi, k);
    if (ok_seed) {
        if (offset >= 0) {
            ok_seed = bi_add_u64(&seed_bi, (uint64_t)offset);
        } else {
            ok_seed = bi_sub_u64(&seed_bi, (uint64_t)(-offset));
        }
    }
    if (!ok_seed || seed_bi.len == 0U) {
        (*silent_overflows)++;
        diagnose_non_dropping_seed(&seed_bi, "mode2", family, k, max_steps,
                                   "bigint_limb_overflow", diag);
        return false;
    }
    out->seed_bits = bi_bitlen(&seed_bi);
    bi_to_dec(&seed_bi, out->seed_dec, sizeof(out->seed_dec));

    bool can_u128 = (out->seed_bits <= 127U) && (seed_bi.len <= 2U);
    if (can_u128) {
        u128 n = (seed_bi.len == 1U)
                     ? (u128)seed_bi.limbs[0]
                     : (((u128)seed_bi.limbs[1] << 64) | (u128)seed_bi.limbs[0]);
        u128 cur = n;
        u128 peak = n;
        uint32_t total = 0U;
        uint32_t stop = 0U;
        bool have_stop = false;
        bool overflowed_u128 = false;
        bool hit_budget_u128 = false;

        while (cur != 1U) {
            if (total >= max_steps) {
                hit_budget_u128 = true;
                break;
            }
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
        if (hit_budget_u128) {
            diagnose_non_dropping_seed(&seed_bi, "mode2", family, k, max_steps,
                                       "step_budget_exceeded", diag);
            return false;
        }
        if (!overflowed_u128) {
            out->stopping_time = stop;
            out->total_steps = total;
            out->peak_bits = bitlen128(peak);
            bigint_t peak_bi;
            bi_from_u128(&peak_bi, peak);
            double l2_seed = bi_log2(&seed_bi);
            double l2_peak = bi_log2(&peak_bi);
            out->log2_glide_ratio = l2_peak - l2_seed;
            out->peak_ratio = (out->log2_glide_ratio < 996.0) ? exp2(out->log2_glide_ratio) : 0.0;
            out->used_bigint_fallback = false;
            out->verified_hits_one = true;
            u128_to_str(peak, out->peak_dec, sizeof(out->peak_dec));
            return true;
        }
    }

    /* Exact arbitrary-precision bigint_t fallback (never overflows within BIGINT_MAX_LIMBS). */
    bigint_t cur, peak;
    bi_copy(&cur, &seed_bi);
    bi_copy(&peak, &seed_bi);
    uint32_t total = 0U;
    uint32_t stop = 0U;
    bool have_stop = false;
    out->used_bigint_fallback = true;

    while (!bi_is_one(&cur)) {
        if (total >= max_steps) {
            diagnose_non_dropping_seed(&seed_bi, "mode2", family, k, max_steps,
                                       "step_budget_exceeded", diag);
            return false;
        }
        if ((cur.limbs[0] & 1ULL) == 0ULL) {
            bigint_t pre_shift;
            if (!have_stop) {
                bi_copy(&pre_shift, &cur);
            }
            uint32_t tz = bi_rshift_tz(&cur);
            if (!have_stop && bi_cmp(&cur, &seed_bi) < 0) {
                uint32_t j = 1U;
                bi_rshift_one(&pre_shift);
                while (j < tz && bi_cmp(&pre_shift, &seed_bi) >= 0) {
                    bi_rshift_one(&pre_shift);
                    j++;
                }
                stop = total + j;
                have_stop = true;
            }
            total += tz;
        } else {
            if (!bi_mul3_add1(&cur)) {
                (*silent_overflows)++;
                diagnose_non_dropping_seed(&seed_bi, "mode2", family, k, max_steps,
                                           "bigint_limb_overflow", diag);
                return false;
            }
            if (bi_cmp(&cur, &peak) > 0) {
                bi_copy(&peak, &cur);
            }
            bigint_t pre_shift;
            if (!have_stop) {
                bi_copy(&pre_shift, &cur);
            }
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
    double l2_seed = bi_log2(&seed_bi);
    double l2_peak = bi_log2(&peak);
    out->log2_glide_ratio = l2_peak - l2_seed;
    out->peak_ratio = (out->log2_glide_ratio < 996.0) ? exp2(out->log2_glide_ratio) : 0.0;
    out->verified_hits_one = true;
    bi_to_dec(&peak, out->peak_dec, sizeof(out->peak_dec));
    return true;
}

typedef struct {
    const char *family;
    uint64_t mult;
    int64_t offset;
    uint32_t k;
} mode2_job_t;

typedef struct {
    const mode2_job_t *jobs;
    size_t total_jobs;
    size_t tid;
    size_t num_threads;
    uint32_t max_steps;
    mersenne_record_t *recs;
    uint8_t *ok_flags;
    uint64_t silent_overflows;
    bool failed;
    size_t first_fail_idx;
    failure_diagnostic_t first_diag;
} mode2_worker_ctx_t;

static void *mode2_worker_run(void *arg) {
    mode2_worker_ctx_t *ctx = (mode2_worker_ctx_t *)arg;
    for (size_t i = ctx->tid; i < ctx->total_jobs; i += ctx->num_threads) {
        const mode2_job_t *job = &ctx->jobs[i];
        failure_diagnostic_t local_diag;
        memset(&local_diag, 0, sizeof(local_diag));
        bool ok = test_mersenne_seed(job->family, job->mult, job->offset, job->k, ctx->max_steps,
                                     &ctx->recs[i], &ctx->silent_overflows, &local_diag);
        ctx->ok_flags[i] = ok ? 1U : 0U;
        if (!ok) {
            ctx->failed = true;
            ctx->first_fail_idx = i;
            ctx->first_diag = local_diag;
            return NULL;
        }
    }
    return NULL;
}

static void print_record_array(FILE *fp, const record_list_t *list, int indent) {
    char pbuf[48];
    fprintf(fp, "[\n");
    for (size_t i = 0; i < list->count; i++) {
        const record_t *r = &list->items[i];
        u128_to_str(r->peak, pbuf, sizeof(pbuf));
        double r_double = ratio_to_double(r->peak, r->n);
        if (!isfinite(r_double)) {
            r_double = 0.0;
        }
        fprintf(fp,
                "%*s{\"n\": %" PRIu64 ", \"stopping_time\": %u, \"total_steps\": %u, "
                "\"peak\": \"%s\", \"peak_ratio\": %.6f}%s\n",
                indent, "", r->n, r->stopping_time, r->total_steps, pbuf,
                r_double, (i + 1 < list->count) ? "," : "");
    }
    fprintf(fp, "%*s]", indent - 2, "");
}

static void write_json_output(FILE *fp, const mode1_result_t *m1, bool run_m2,
                              uint32_t mersenne_max, uint32_t max_steps,
                              const mersenne_record_t *m2_recs, size_t m2_count,
                              uint64_t u128_fallbacks, uint64_t silent_overflows,
                              double m2_elapsed, const failure_diagnostic_t *diag) {
    uint64_t total_overflows = (m1 ? m1->overflow_count : 0ULL) + silent_overflows;

    fprintf(fp, "{\n");
    fprintf(fp, "  \"canonical\": {\n");
    fprintf(fp, "    \"schema\": \"solve-collatz-glide-hunter/v1\",\n");
    fprintf(fp, "    \"max_steps_budget\": %u,\n", max_steps);
    fprintf(fp, "    \"overflow_count\": %" PRIu64 ",\n", total_overflows);
    fprintf(fp, "    \"u128_bigint_fallbacks\": %" PRIu64 ",\n", u128_fallbacks);

    if (m1 && m1->range_end > 0ULL) {
        fprintf(fp, "    \"mode1_range\": {\n");
        fprintf(fp, "      \"range_start\": 1,\n");
        fprintf(fp, "      \"range_end\": %" PRIu64 ",\n", m1->range_end);
        fprintf(fp, "      \"verified_count\": %" PRIu64 ",\n", m1->verified_count);
        fprintf(fp, "      \"all_converged\": %s,\n", m1->all_converged ? "true" : "false");
        fprintf(fp, "      \"tau_exact_up_to\": %" PRIu64 ",\n", m1->tau_exact_up_to);
        fprintf(fp, "      \"sieve_bits\": %u,\n", m1->sieve_bits);
        fprintf(fp, "      \"sieve_modulus\": %u,\n", m1->sieve_modulus);
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
        fprintf(fp, "\n    }%s\n", (run_m2 || (diag && diag->triggered)) ? "," : "");
    }

    if (run_m2) {
        uint32_t max_stop = 0U, max_tot = 0U, max_pbits = 0U;
        double max_l2 = 0.0;
        uint64_t max_stop_k = 0U, max_tot_k = 0U, max_l2_k = 0U, max_pbits_k = 0U;
        char max_stop_fam[32] = "", max_tot_fam[32] = "", max_l2_fam[32] = "";
        char max_pbits_fam[32] = "";
        bool all_ok = (m2_count > 0U);

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
                max_pbits_k = r->k;
                snprintf(max_pbits_fam, sizeof(max_pbits_fam), "%s", r->family);
            }
            if (r->log2_glide_ratio > max_l2) {
                max_l2 = r->log2_glide_ratio;
                max_l2_k = r->k;
                snprintf(max_l2_fam, sizeof(max_l2_fam), "%s", r->family);
            }
        }
        if (!isfinite(max_l2)) {
            max_l2 = 0.0;
        }

        fprintf(fp, "    \"mode2_mersenne\": {\n");
        fprintf(fp, "      \"mersenne_max_k\": %u,\n", mersenne_max);
        fprintf(fp,
                "      \"families\": [\"2^k-1\", \"3*2^k-1\", \"27*2^k-1\", "
                "\"5*2^k-1\", \"7*2^k-1\", \"9*2^k-1\", \"2^k+1\", \"2^k-3\", "
                "\"703*2^k-1\", \"9663*2^k-1\", \"77671*2^k-1\", \"319804831*2^k-1\"],\n");
        fprintf(fp,
                "      \"family_groups\": {\n"
                "        \"mersenne_lifts\": [\"2^k-1\", \"3*2^k-1\", \"27*2^k-1\"],\n"
                "        \"extended_lifts\": [\"5*2^k-1\", \"7*2^k-1\", \"9*2^k-1\", \"2^k+1\", \"2^k-3\"],\n"
                "        \"terras_roosendaal_lifts\": [\"703*2^k-1\", \"9663*2^k-1\", "
                "\"77671*2^k-1\", \"319804831*2^k-1\"]\n"
                "      },\n");
        fprintf(fp, "      \"tested_count\": %zu,\n", m2_count);
        fprintf(fp, "      \"all_converged\": %s,\n", all_ok ? "true" : "false");
        fprintf(fp, "      \"max_stopping_time\": {\"family\": \"%s\", \"k\": %" PRIu64
                    ", \"value\": %u},\n",
                max_stop_fam, max_stop_k, max_stop);
        fprintf(fp, "      \"max_total_steps\": {\"family\": \"%s\", \"k\": %" PRIu64
                    ", \"value\": %u},\n",
                max_tot_fam, max_tot_k, max_tot);
        fprintf(fp, "      \"max_peak_ratio\": {\"family\": \"%s\", \"k\": %" PRIu64
                    ", \"log2_glide_ratio\": %.6f, \"max_peak_bits\": %u},\n",
                max_l2_fam, max_l2_k, max_l2, max_pbits);
        fprintf(fp, "      \"samples\": [\n");
        size_t emitted = 0;
        for (size_t i = 0; i < m2_count; i++) {
            const mersenne_record_t *r = &m2_recs[i];
            bool is_record = (strcmp(r->family, max_l2_fam) == 0 && r->k == max_l2_k) ||
                             (strcmp(r->family, max_stop_fam) == 0 && r->k == max_stop_k) ||
                             (strcmp(r->family, max_tot_fam) == 0 && r->k == max_tot_k) ||
                             (strcmp(r->family, max_pbits_fam) == 0 && r->k == max_pbits_k);
            if (r->k <= 2U || r->k == mersenne_max || (r->k % 100U == 0U) || is_record) {
                char ratio_buf[64];
                if (r->peak_ratio > 0.0 && isfinite(r->peak_ratio)) {
                    snprintf(ratio_buf, sizeof(ratio_buf), "%.6e", r->peak_ratio);
                } else {
                    snprintf(ratio_buf, sizeof(ratio_buf), "null");
                }
                double l2_safe = isfinite(r->log2_glide_ratio) ? r->log2_glide_ratio : 0.0;
                fprintf(fp,
                        "%s        {\"family\": \"%s\", \"k\": %u, \"seed_bits\": %u, "
                        "\"stopping_time\": %u, \"total_steps\": %u, \"peak_bits\": %u, "
                        "\"log2_glide_ratio\": %.6f, \"peak_ratio\": %s, \"bigint_fallback\": %s, "
                        "\"seed\": \"%s\", \"peak\": \"%s\"}",
                        (emitted > 0) ? ",\n" : "", r->family, r->k, r->seed_bits,
                        r->stopping_time, r->total_steps, r->peak_bits, l2_safe,
                        ratio_buf,
                        r->used_bigint_fallback ? "true" : "false", r->seed_dec, r->peak_dec);
                emitted++;
            }
        }
        fprintf(fp, "\n      ]\n");
        fprintf(fp, "    }%s\n", (diag && diag->triggered) ? "," : "");
    }

    if (diag && diag->triggered) {
        fprintf(fp, "    \"failure_diagnostic\": {\n");
        fprintf(fp, "      \"mode\": \"%s\",\n", diag->mode);
        fprintf(fp, "      \"kind\": \"%s\",\n", diag->kind);
        fprintf(fp, "      \"family\": \"%s\",\n", diag->family);
        fprintf(fp, "      \"k\": %u,\n", diag->k);
        fprintf(fp, "      \"seed\": \"%s\",\n", diag->seed_dec);
        fprintf(fp, "      \"steps_executed\": %u,\n", diag->steps_executed);
        fprintf(fp, "      \"max_steps_budget\": %u,\n", diag->max_steps_budget);
        fprintf(fp, "      \"peak_bits\": %u,\n", diag->peak_bits);
        fprintf(fp, "      \"last_bits\": %u,\n", diag->last_bits);
        fprintf(fp, "      \"peak\": \"%s\",\n", diag->peak_dec);
        fprintf(fp, "      \"last_value\": \"%s\",\n", diag->last_dec);
        fprintf(fp, "      \"cycle_start\": \"%s\",\n", diag->cycle_start_dec);
        fprintf(fp, "      \"cycle_period\": %u\n", diag->cycle_period);
        fprintf(fp, "    }\n");
    }

    fprintf(fp, "  },\n");
    fprintf(fp, "  \"telemetry\": {\n");
    if (m1 && m1->range_end > 0ULL) {
        double rate = (m1->elapsed_sec > 0.0) ? ((double)m1->verified_count / m1->elapsed_sec) : 0.0;
        if (!isfinite(rate)) {
            rate = 0.0;
        }
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
    return (cpus > 8L) ? 8U : (uint32_t)cpus;
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
    uint32_t sieve_bits = DEFAULT_SIEVE_BITS;
    uint32_t max_steps = DEFAULT_MAX_STEPS;
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
            if (!parse_u64(argv[++i], &tmp) || tmp > MAX_MERSENNE_K) {
                fprintf(stderr, "Invalid --mersenne-max value (0..%llu)\n",
                        (unsigned long long)MAX_MERSENNE_K);
                return 2;
            }
            mersenne_max = (uint32_t)tmp;
            run_m2 = (mersenne_max > 0U);
        } else if (strcmp(argv[i], "--sieve-bits") == 0 && i + 1 < argc) {
            uint64_t tmp = 0ULL;
            if (!parse_u64(argv[++i], &tmp) ||
                (tmp != 0ULL && tmp != 16ULL && tmp != 18ULL && tmp != 20ULL && tmp != 22ULL &&
                 tmp != 24ULL)) {
                fprintf(stderr,
                        "Invalid --sieve-bits value (supported: 0, 16, 18, 20, 22, 24)\n");
                return 2;
            }
            sieve_bits = (uint32_t)tmp;
        } else if (strcmp(argv[i], "--max-steps") == 0 && i + 1 < argc) {
            uint64_t tmp = 0ULL;
            if (!parse_u64(argv[++i], &tmp) || tmp < 1ULL || tmp > MAX_ALLOWED_STEPS) {
                fprintf(stderr, "Invalid --max-steps value (1..%u)\n", MAX_ALLOWED_STEPS);
                return 2;
            }
            max_steps = (uint32_t)tmp;
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
                    "Usage: %s [--range-end N] [--mersenne-max K] [--sieve-bits 0|16|18|20|22|24] "
                    "[--max-steps S] [--threads T] [--json-out PATH|-]\n",
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
    failure_diagnostic_t diag;
    memset(&diag, 0, sizeof(diag));
    int exit_code = 0;

    if (run_m1 && range_end > 0ULL) {
        uint32_t use_threads = (threads > 0U) ? threads : default_threads(range_end);
        if (!run_mode1(range_end, use_threads, sieve_bits, max_steps, &m1, &diag)) {
            fprintf(stderr, "ALERT: Mode 1 failed (%s) at seed %" PRIu64 "\n",
                    m1.failure_reason ? m1.failure_reason : "unknown", m1.failure_seed);
            print_failure_diagnostic_stderr(&diag);
            exit_code = 10;
        }
    }

    mersenne_record_t *m2_recs = NULL;
    size_t m2_count = 0U;
    uint64_t u128_fallbacks = m1.u128_fallbacks;
    uint64_t silent_overflows = 0ULL;
    double m2_elapsed = 0.0;
    bool ran_m2 = false;

    if (run_m2 && exit_code == 0) {
        ran_m2 = true;
        struct timespec t0, t1;
        clock_gettime(CLOCK_MONOTONIC, &t0);
        static const struct {
            const char *name;
            uint64_t mult;
            int64_t offset;
            uint32_t min_k;
        } families[12] = {
            {"2^k-1", 1ULL, -1, 1U},
            {"3*2^k-1", 3ULL, -1, 1U},
            {"27*2^k-1", 27ULL, -1, 1U},
            {"5*2^k-1", 5ULL, -1, 1U},
            {"7*2^k-1", 7ULL, -1, 1U},
            {"9*2^k-1", 9ULL, -1, 1U},
            {"2^k+1", 1ULL, 1, 1U},
            {"2^k-3", 1ULL, -3, 2U},
            {"703*2^k-1", 703ULL, -1, 1U},
            {"9663*2^k-1", 9663ULL, -1, 1U},
            {"77671*2^k-1", 77671ULL, -1, 1U},
            {"319804831*2^k-1", 319804831ULL, -1, 1U},
        };
        const size_t num_families = sizeof(families) / sizeof(families[0]);
        size_t total_m2_cap = (size_t)mersenne_max * num_families;
        mode2_job_t *jobs = calloc(total_m2_cap, sizeof(mode2_job_t));
        m2_recs = calloc(total_m2_cap, sizeof(mersenne_record_t));
        uint8_t *ok_flags = calloc(total_m2_cap, sizeof(uint8_t));
        if (!jobs || !m2_recs || !ok_flags) {
            fprintf(stderr, "ERROR: Failed to allocate mode2 results\n");
            free(jobs);
            free(m2_recs);
            free(ok_flags);
            return 1;
        }
        size_t total_jobs = 0U;
        for (size_t f = 0; f < num_families; f++) {
            for (uint32_t k = families[f].min_k; k <= mersenne_max; k++) {
                jobs[total_jobs++] = (mode2_job_t){
                    families[f].name, families[f].mult, families[f].offset, k};
            }
        }

        uint32_t m2_threads = (threads > 0U) ? threads : default_threads(SEQ_CUTOFF);
        if (m2_threads < 1U) {
            m2_threads = 1U;
        }
        if (m2_threads > 64U) {
            m2_threads = 64U;
        }
        if (total_jobs < (size_t)m2_threads) {
            m2_threads = (total_jobs > 0U) ? (uint32_t)total_jobs : 1U;
        }

        mode2_worker_ctx_t *wctxs = calloc(m2_threads, sizeof(mode2_worker_ctx_t));
        pthread_t *tids = calloc(m2_threads, sizeof(pthread_t));
        if (!wctxs || !tids) {
            fprintf(stderr, "ERROR: Failed to allocate mode2 threads\n");
            free(wctxs);
            free(tids);
            free(jobs);
            free(m2_recs);
            free(ok_flags);
            return 1;
        }
        for (uint32_t t = 0U; t < m2_threads; t++) {
            wctxs[t].jobs = jobs;
            wctxs[t].total_jobs = total_jobs;
            wctxs[t].tid = t;
            wctxs[t].num_threads = m2_threads;
            wctxs[t].max_steps = max_steps;
            wctxs[t].recs = m2_recs;
            wctxs[t].ok_flags = ok_flags;
        }
        if (m2_threads == 1U) {
            mode2_worker_run(&wctxs[0]);
        } else {
            uint32_t spawned = 0U;
            bool thread_err = false;
            for (uint32_t t = 0U; t < m2_threads; t++) {
                int rc = pthread_create(&tids[t], NULL, mode2_worker_run, &wctxs[t]);
                if (rc != 0) {
                    fprintf(stderr, "ERROR: mode2 pthread_create(%u) failed: %s\n", t,
                            strerror(rc));
                    thread_err = true;
                    break;
                }
                spawned++;
            }
            for (uint32_t t = 0U; t < spawned; t++) {
                int rc = pthread_join(tids[t], NULL);
                if (rc != 0) {
                    fprintf(stderr, "ERROR: mode2 pthread_join(%u) failed: %s\n", t,
                            strerror(rc));
                    thread_err = true;
                }
            }
            if (thread_err) {
                free(wctxs);
                free(tids);
                free(jobs);
                free(m2_recs);
                free(ok_flags);
                return 1;
            }
        }

        size_t best_fail_idx = total_jobs;
        failure_diagnostic_t fail_diag;
        memset(&fail_diag, 0, sizeof(fail_diag));
        for (uint32_t t = 0U; t < m2_threads; t++) {
            silent_overflows += wctxs[t].silent_overflows;
            if (wctxs[t].failed && wctxs[t].first_fail_idx < best_fail_idx) {
                best_fail_idx = wctxs[t].first_fail_idx;
                fail_diag = wctxs[t].first_diag;
            }
        }
        if (best_fail_idx < total_jobs) {
            fprintf(stderr, "ALERT: Mode 2 failed on %s at k=%u\n", jobs[best_fail_idx].family,
                    jobs[best_fail_idx].k);
            diag = fail_diag;
            print_failure_diagnostic_stderr(&diag);
            m2_count = best_fail_idx + 1U;
            exit_code = 11;
        } else {
            m2_count = total_jobs;
        }
        for (size_t i = 0U; i < m2_count; i++) {
            if (m2_recs[i].used_bigint_fallback) {
                u128_fallbacks++;
            }
        }

        free(wctxs);
        free(tids);
        free(jobs);
        free(ok_flags);
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

    write_json_output(out_fp, run_m1 ? &m1 : NULL, ran_m2, mersenne_max, max_steps, m2_recs,
                      m2_count, u128_fallbacks, silent_overflows, m2_elapsed, &diag);

    if (out_fp != stdout) {
        fclose(out_fp);
    }
    free(m2_recs);
    return exit_code;
}
