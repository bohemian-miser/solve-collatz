/*
 * mcircuit_hunter.c — High-throughput C11 canonical m-circuit Diophantine cycle hunter (m = 2, 3, 4).
 *
 * Track B (`Disprove/`) off-kernel search engine for `solve-collatz` (`DISPROVE-002 Phase 2`).
 *
 * Mathematical foundation (Simons-de Weger 2005 / Eliahou 1993):
 *   An m-circuit consists of m rising-then-falling blocks j = 0..m-1, where block j has
 *   k_j >= 1 odd steps (k_j - 1 single halvings followed by l_j >= 2 halvings, so block
 *   halving sum is s_j = k_j - 1 + l_j >= k_j + 1).
 *   Let K = sum k_j, K_{j+1} = sum_{r=0}^j k_r, S_0 = 0, S_j = sum_{r=0}^{j-1} s_r, S = sum s_j.
 *   Then any periodic point n_0 at the start of block 0 satisfies:
 *       (2^S - 3^K) * n_0 = C(v) = sum_{j=0}^{m-1} 3^{K - K_{j+1}} * 2^{S_j} * (3^{k_j} - 2^{k_j}).
 *
 *   For any non-trivial positive cycle (all odd elements n_j >= 3):
 *     - Block transition: 2^{s_j} * n_{j+1} = 3^{k_j} * n_j + (3^{k_j} - 2^{k_j}) < (4/3) * 3^{k_j} * n_j.
 *     - Multiplying over j = 0..m-1 yields the exact Simons-de Weger m-circuit upper bound:
 *           2^S < (4/3)^m * 3^K   <=>   2^S * 3^m < 4^m * 3^K.
 *     - The looser general Eliahou bound (used in `search/cycle_hunter.py`) is:
 *           2^S * 3^K <= 10^K   (with S = S_min(K) always included).
 *
 * Arithmetic & UB safety:
 *   - Strict overflow guards enforce K <= 80 (3^80 < 2^127 < 2^128) and S <= 127
 *     before any `u128` shift or power computation; skipped shells increment `overflow_guard_skips`.
 *   - Overflow-free `add_mod128` and `mul_mod128` for all D < 2^127.
 *   - Innermost loop updates only via two `add_mod128` ops (zero inner-loop multiplications).
 *   - Lock-free pthread execution with deterministic canonical sorting at merge.
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

#define MAX_M 4U
#define MAX_K_LIMIT 80U
#define MAX_S_LIMIT 127U
#define TOP_NEAR_PER_M 5U
#define MAX_HITS_PER_WORKER 64U

typedef enum {
    BOUND_SIMONS = 0,
    BOUND_ELIAHOU = 1
} bound_mode_t;

/* 320-bit unsigned big-int (5 x 64-bit limbs) for exact S_max precomputation & hit verification. */
typedef struct {
    uint64_t w[5];
} u320_t;

typedef struct {
    uint32_t m;
    uint32_t k;
    uint32_t s;
    uint32_t k_vec[MAX_M];
    uint32_t l_vec[MAX_M];
    u128 denom;
    u128 rem;
    u128 dist_num;
    long double dist_approx;
} candidate_record_t;

typedef struct {
    uint32_t m;
    uint32_t k;
    uint32_t s;
    uint32_t k_vec[MAX_M];
    uint32_t l_vec[MAX_M];
    u128 denom;
    u320_t n_cand;
    bool is_trivial;
} hit_record_t;

typedef struct {
    uint32_t m;
    uint32_t k;
    uint32_t s;
    uint32_t k0;
    uint32_t k1; /* used for m == 4 */
} work_task_t;

typedef struct {
    const work_task_t *tasks;
    size_t task_count;
    uint32_t thread_id;
    uint32_t num_threads;
    uint64_t tested[MAX_M + 1];
    hit_record_t hits[MAX_HITS_PER_WORKER];
    size_t hit_count;
    candidate_record_t near[MAX_M + 1][TOP_NEAR_PER_M];
    size_t near_count[MAX_M + 1];
} worker_ctx_t;

/* Precomputed exact tables for K <= 80, S <= 127. */
static u128 g_pow3[MAX_K_LIMIT + 1U];
static u128 g_pow2[MAX_S_LIMIT + 1U];
static uint32_t g_s_min[MAX_K_LIMIT + 1U];
static uint32_t g_s_max_eliahou[MAX_K_LIMIT + 1U];
static uint32_t g_s_max_simons[MAX_M + 1U][MAX_K_LIMIT + 1U];

static inline u128 add_mod128(u128 a, u128 b, u128 m) {
    return (a >= m - b) ? (a - (m - b)) : (a + b);
}

static inline u128 mul_mod128(u128 a, u128 b, u128 m) {
    if (m <= 1U) {
        return 0U;
    }
    a %= m;
    b %= m;
    u128 res = 0U;
    while (b > 0U) {
        if (b & 1U) {
            res = add_mod128(res, a, m);
        }
        b >>= 1U;
        if (b > 0U) {
            a = add_mod128(a, a, m);
        }
    }
    return res;
}

static u320_t u320_from_u128(u128 v) {
    u320_t r;
    memset(&r, 0, sizeof(r));
    r.w[0] = (uint64_t)v;
    r.w[1] = (uint64_t)(v >> 64);
    return r;
}

static u320_t u320_mul_u64(u320_t a, uint64_t m) {
    u320_t r;
    memset(&r, 0, sizeof(r));
    u128 carry = 0U;
    for (size_t i = 0; i < 5; i++) {
        u128 prod = (u128)a.w[i] * (u128)m + carry;
        r.w[i] = (uint64_t)prod;
        carry = prod >> 64;
    }
    return r;
}

static u320_t u320_add(u320_t a, u320_t b) {
    u320_t r;
    u128 carry = 0U;
    for (size_t i = 0; i < 5; i++) {
        u128 s = (u128)a.w[i] + (u128)b.w[i] + carry;
        r.w[i] = (uint64_t)s;
        carry = s >> 64;
    }
    return r;
}

static u320_t u320_shl(u320_t a, uint32_t shift) {
    u320_t r;
    memset(&r, 0, sizeof(r));
    uint32_t ws = shift / 64U;
    uint32_t bs = shift % 64U;
    for (size_t i = 0; i < 5; i++) {
        if (i + ws >= 5U) {
            continue;
        }
        r.w[i + ws] |= (a.w[i] << bs);
        if (bs > 0U && i + ws + 1U < 5U) {
            r.w[i + ws + 1U] |= (a.w[i] >> (64U - bs));
        }
    }
    return r;
}

static int u320_cmp(u320_t a, u320_t b) {
    for (size_t i = 5; i > 0; i--) {
        if (a.w[i - 1] != b.w[i - 1]) {
            return (a.w[i - 1] > b.w[i - 1]) ? 1 : -1;
        }
    }
    return 0;
}

/* Exact u320 division by u128 D (1 <= D < 2^128), returning quotient and remainder. */
static void u320_divmod_u128(u320_t num, u128 denom, u320_t *out_q, u128 *out_rem) {
    u320_t q;
    memset(&q, 0, sizeof(q));
    u128 rem = 0U;
    for (int bit = 319; bit >= 0; bit--) {
        uint32_t wi = (uint32_t)bit / 64U;
        uint32_t bi = (uint32_t)bit % 64U;
        uint64_t b = (num.w[wi] >> bi) & 1ULL;
        /* rem = 2 * rem + b, checking for >= denom without u128 overflow (denom < 2^127). */
        rem = (rem << 1) | (u128)b;
        if (rem >= denom) {
            rem -= denom;
            q.w[wi] |= (1ULL << bi);
        }
    }
    *out_q = q;
    *out_rem = rem;
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

static void u320_to_str(u320_t v, char *buf, size_t bufsz) {
    if (v.w[2] == 0ULL && v.w[3] == 0ULL && v.w[4] == 0ULL) {
        u128_to_str(((u128)v.w[1] << 64) | (u128)v.w[0], buf, bufsz);
        return;
    }
    char tmp[112];
    size_t pos = 0;
    while ((v.w[0] | v.w[1] | v.w[2] | v.w[3] | v.w[4]) != 0ULL && pos < sizeof(tmp)) {
        u320_t q;
        u128 rem = 0U;
        u320_divmod_u128(v, 10U, &q, &rem);
        tmp[pos++] = (char)('0' + (unsigned)rem);
        v = q;
    }
    size_t out = 0;
    while (pos > 0 && out + 1 < bufsz) {
        buf[out++] = tmp[--pos];
    }
    buf[out] = '\0';
}

static void init_tables(void) {
    g_pow3[0] = 1U;
    for (uint32_t i = 1; i <= MAX_K_LIMIT; i++) {
        g_pow3[i] = g_pow3[i - 1] * 3U;
    }
    g_pow2[0] = 1U;
    for (uint32_t i = 1; i <= MAX_S_LIMIT; i++) {
        g_pow2[i] = g_pow2[i - 1] << 1;
    }

    u320_t p10 = u320_from_u128(1U);
    u320_t p3_big = u320_from_u128(1U);
    g_s_min[0] = 1U;
    g_s_max_eliahou[0] = 0U;
    for (uint32_t m = 1; m <= MAX_M; m++) {
        g_s_max_simons[m][0] = 0U;
    }

    for (uint32_t k = 1; k <= MAX_K_LIMIT; k++) {
        p10 = u320_mul_u64(p10, 10ULL);
        p3_big = u320_mul_u64(p3_big, 3ULL);

        uint32_t s_min = 0U;
        while (s_min <= MAX_S_LIMIT && g_pow2[s_min] <= g_pow3[k]) {
            s_min++;
        }
        g_s_min[k] = s_min;

        /* Exact Eliahou bound: s == s_min OR 3^k * 2^s <= 10^k */
        uint32_t s_eliahou = s_min;
        while (true) {
            u320_t lhs = u320_shl(p3_big, s_eliahou + 1U);
            if (u320_cmp(lhs, p10) <= 0) {
                s_eliahou++;
            } else {
                break;
            }
        }
        g_s_max_eliahou[k] = s_eliahou;

        /* Exact Simons-de Weger m-circuit bound: 2^S * 3^m < 4^m * 3^k */
        for (uint32_t m = 1; m <= MAX_M; m++) {
            u320_t rhs = u320_shl(p3_big, 2U * m); /* 4^m * 3^k */
            uint32_t p3m = 1U;
            for (uint32_t r = 0; r < m; r++) {
                p3m *= 3U;
            }
            uint32_t s_sim = s_min;
            /* Check if s_sim itself violates bound (empty range if so, e.g. k < m). */
            u320_t lhs0 = u320_shl(u320_from_u128(p3m), s_sim);
            if (u320_cmp(lhs0, rhs) >= 0) {
                g_s_max_simons[m][k] = s_min - 1U;
                continue;
            }
            while (true) {
                u320_t nxt = u320_shl(u320_from_u128(p3m), s_sim + 1U);
                if (u320_cmp(nxt, rhs) < 0) {
                    s_sim++;
                } else {
                    break;
                }
            }
            g_s_max_simons[m][k] = s_sim;
        }
    }
}

/* Exact closed-form m-circuit numerator C(v) in u320_t, used for self-test & hit recovery. */
static u320_t exact_mcircuit_numerator(uint32_t m, const uint32_t *k_vec, const uint32_t *l_vec) {
    uint32_t K = 0U;
    for (uint32_t j = 0; j < m; j++) {
        K += k_vec[j];
    }
    u320_t total;
    memset(&total, 0, sizeof(total));
    uint32_t k_pref = 0U;
    uint32_t s_pref = 0U;
    for (uint32_t j = 0; j < m; j++) {
        k_pref += k_vec[j];
        u128 term_factor = g_pow3[K - k_pref] * (g_pow3[k_vec[j]] - g_pow2[k_vec[j]]);
        u320_t term = u320_shl(u320_from_u128(term_factor), s_pref);
        total = u320_add(total, term);
        s_pref += (k_vec[j] - 1U) + l_vec[j];
    }
    return total;
}

/* Direct step-by-step C(v) = sum_{i=0}^{K-1} 3^{K-1-i} * 2^{prefix_s_i} for self-test. */
static u320_t step_by_step_numerator(uint32_t m, const uint32_t *k_vec, const uint32_t *l_vec) {
    uint32_t K = 0U;
    for (uint32_t j = 0; j < m; j++) {
        K += k_vec[j];
    }
    u320_t total;
    memset(&total, 0, sizeof(total));
    uint32_t s_pref = 0U;
    uint32_t odd_idx = 0U;
    for (uint32_t j = 0; j < m; j++) {
        for (uint32_t r = 0; r < k_vec[j]; r++) {
            uint32_t exp_val = (r + 1U < k_vec[j]) ? 1U : l_vec[j];
            u320_t term = u320_shl(u320_from_u128(g_pow3[K - 1U - odd_idx]), s_pref);
            total = u320_add(total, term);
            s_pref += exp_val;
            odd_idx++;
        }
    }
    return total;
}

static inline int cmp_pair(uint32_t k_a, uint32_t l_a, uint32_t k_b, uint32_t l_b) {
    if (k_a != k_b) {
        return (k_a < k_b) ? -1 : 1;
    }
    if (l_a != l_b) {
        return (l_a < l_b) ? -1 : 1;
    }
    return 0;
}

static inline int cmp_rotations(uint32_t m, const uint32_t *kv, const uint32_t *lv, uint32_t rot) {
    for (uint32_t i = 0; i < m; i++) {
        uint32_t ri = (i + rot) % m;
        int c = cmp_pair(kv[i], lv[i], kv[ri], lv[ri]);
        if (c != 0) {
            return c;
        }
    }
    return 0;
}

static inline bool is_canonical_m(uint32_t m, const uint32_t *kv, const uint32_t *lv) {
    for (uint32_t rot = 1U; rot < m; rot++) {
        if (cmp_rotations(m, kv, lv, rot) > 0) {
            return false;
        }
    }
    return true;
}

static int cmp_near_record(const candidate_record_t *a, const candidate_record_t *b) {
    if (a->dist_approx < b->dist_approx) {
        return -1;
    }
    if (a->dist_approx > b->dist_approx) {
        return 1;
    }
    if (a->m != b->m) {
        return (a->m < b->m) ? -1 : 1;
    }
    if (a->k != b->k) {
        return (a->k < b->k) ? -1 : 1;
    }
    if (a->s != b->s) {
        return (a->s < b->s) ? -1 : 1;
    }
    for (uint32_t i = 0; i < a->m; i++) {
        int c = cmp_pair(a->k_vec[i], a->l_vec[i], b->k_vec[i], b->l_vec[i]);
        if (c != 0) {
            return c;
        }
    }
    return 0;
}

static int cmp_near_qsort(const void *pa, const void *pb) {
    return cmp_near_record((const candidate_record_t *)pa, (const candidate_record_t *)pb);
}

static int cmp_hit_qsort(const void *pa, const void *pb) {
    const hit_record_t *a = (const hit_record_t *)pa;
    const hit_record_t *b = (const hit_record_t *)pb;
    if (a->m != b->m) {
        return (a->m < b->m) ? -1 : 1;
    }
    if (a->k != b->k) {
        return (a->k < b->k) ? -1 : 1;
    }
    if (a->s != b->s) {
        return (a->s < b->s) ? -1 : 1;
    }
    for (uint32_t i = 0; i < a->m; i++) {
        int c = cmp_pair(a->k_vec[i], a->l_vec[i], b->k_vec[i], b->l_vec[i]);
        if (c != 0) {
            return c;
        }
    }
    return 0;
}

static void record_near_miss(worker_ctx_t *ctx, uint32_t m, uint32_t k, uint32_t s,
                             const uint32_t *kv, const uint32_t *lv, u128 denom, u128 rem) {
    if (denom <= 1U || rem == 0U) {
        return;
    }
    u128 dist_num = (rem <= denom - rem) ? rem : (denom - rem);
    long double dist_approx = (long double)dist_num / (long double)denom;

    candidate_record_t cand;
    memset(&cand, 0, sizeof(cand));
    cand.m = m;
    cand.k = k;
    cand.s = s;
    for (uint32_t i = 0; i < m; i++) {
        cand.k_vec[i] = kv[i];
        cand.l_vec[i] = lv[i];
    }
    cand.denom = denom;
    cand.rem = rem;
    cand.dist_num = dist_num;
    cand.dist_approx = dist_approx;

    size_t cnt = ctx->near_count[m];
    candidate_record_t *arr = ctx->near[m];
    if (cnt < TOP_NEAR_PER_M) {
        arr[cnt] = cand;
        ctx->near_count[m] = cnt + 1U;
        return;
    }
    size_t worst_idx = 0U;
    for (size_t i = 1U; i < TOP_NEAR_PER_M; i++) {
        if (cmp_near_record(&arr[i], &arr[worst_idx]) > 0) {
            worst_idx = i;
        }
    }
    if (cmp_near_record(&cand, &arr[worst_idx]) < 0) {
        arr[worst_idx] = cand;
    }
}

static void record_hit(worker_ctx_t *ctx, uint32_t m, uint32_t k, uint32_t s,
                       const uint32_t *kv, const uint32_t *lv, u128 denom) {
    u320_t c_exact = exact_mcircuit_numerator(m, kv, lv);
    u320_t q;
    u128 rem = 0U;
    u320_divmod_u128(c_exact, denom, &q, &rem);
    if (rem != 0U) {
        /* Defensive cross-check: should never happen if modular check returned 0. */
        return;
    }
    u128 n_low = ((u128)q.w[1] << 64) | (u128)q.w[0];
    bool is_triv = (q.w[2] == 0ULL && q.w[3] == 0ULL && q.w[4] == 0ULL &&
                    (n_low == 1U || n_low == 2U || n_low == 4U));
    if (ctx->hit_count < MAX_HITS_PER_WORKER) {
        hit_record_t *h = &ctx->hits[ctx->hit_count++];
        memset(h, 0, sizeof(*h));
        h->m = m;
        h->k = k;
        h->s = s;
        for (uint32_t i = 0; i < m; i++) {
            h->k_vec[i] = kv[i];
            h->l_vec[i] = lv[i];
        }
        h->denom = denom;
        h->n_cand = q;
        h->is_trivial = is_triv;
    }
}

static void run_task_m2(worker_ctx_t *ctx, const work_task_t *t) {
    uint32_t k = t->k;
    uint32_t s = t->s;
    uint32_t k0 = t->k0;
    uint32_t k1 = k - k0;
    uint32_t rem_l = s - k + 2U;
    if (rem_l < 4U) {
        return;
    }

    u128 denom = g_pow2[s] - g_pow3[k];
    u128 c0_mod = (g_pow3[k0] - g_pow2[k0]) % denom;
    u128 c1_mod = (g_pow3[k1] - g_pow2[k1]) % denom;
    u128 base0 = mul_mod128(g_pow3[k1] % denom, c0_mod, denom);

    uint32_t l0_max = rem_l - 2U;
    if (k0 == k1 && rem_l / 2U < l0_max) {
        l0_max = rem_l / 2U;
    }
    if (l0_max < 2U) {
        return;
    }

    uint32_t s0_start = (k0 - 1U) + 2U;
    u128 p2_s0 = g_pow2[s0_start] % denom;
    u128 term1 = mul_mod128(p2_s0, c1_mod, denom);

    uint32_t kv[MAX_M] = {k0, k1, 0U, 0U};
    uint32_t lv[MAX_M] = {0U, 0U, 0U, 0U};

    for (uint32_t l0 = 2U; l0 <= l0_max; l0++) {
        uint32_t l1 = rem_l - l0;
        u128 rem = add_mod128(base0, term1, denom);
        ctx->tested[2]++;
        if (rem == 0U) {
            lv[0] = l0;
            lv[1] = l1;
            record_hit(ctx, 2U, k, s, kv, lv, denom);
        } else if (denom > 1U) {
            lv[0] = l0;
            lv[1] = l1;
            record_near_miss(ctx, 2U, k, s, kv, lv, denom, rem);
        }
        term1 = add_mod128(term1, term1, denom);
    }
}

static void run_task_m3(worker_ctx_t *ctx, const work_task_t *t) {
    uint32_t k = t->k;
    uint32_t s = t->s;
    uint32_t k0 = t->k0;
    uint32_t rem_l = s - k + 3U;
    if (rem_l < 6U) {
        return;
    }

    u128 denom = g_pow2[s] - g_pow3[k];
    u128 c0_mod = (g_pow3[k0] - g_pow2[k0]) % denom;

    uint32_t kv[MAX_M] = {k0, 0U, 0U, 0U};
    uint32_t lv[MAX_M] = {0U, 0U, 0U, 0U};

    for (uint32_t k1 = k0; k1 <= k - 2U * k0; k1++) {
        uint32_t k2 = k - k0 - k1;
        if (k2 < k0) {
            continue;
        }
        kv[1] = k1;
        kv[2] = k2;

        u128 c1_mod = (g_pow3[k1] - g_pow2[k1]) % denom;
        u128 c2_mod = (g_pow3[k2] - g_pow2[k2]) % denom;
        u128 base0 = mul_mod128(g_pow3[k1 + k2] % denom, c0_mod, denom);
        u128 p3_k2_c1 = mul_mod128(g_pow3[k2] % denom, c1_mod, denom);

        uint32_t l0_max = rem_l - 4U;
        for (uint32_t l0 = 2U; l0 <= l0_max; l0++) {
            uint32_t s0 = (k0 - 1U) + l0;
            u128 term1 = mul_mod128(g_pow2[s0] % denom, p3_k2_c1, denom);
            u128 base1 = add_mod128(base0, term1, denom);

            uint32_t l1_start = (k1 == k0) ? l0 : 2U;
            uint32_t l1_max = rem_l - l0 - 2U;
            if (l1_start > l1_max) {
                continue;
            }
            uint32_t s01_start = s0 + (k1 - 1U) + l1_start;
            u128 term2 = mul_mod128(g_pow2[s01_start] % denom, c2_mod, denom);

            lv[0] = l0;
            for (uint32_t l1 = l1_start; l1 <= l1_max; l1++) {
                uint32_t l2 = rem_l - l0 - l1;
                lv[1] = l1;
                lv[2] = l2;
                if (is_canonical_m(3U, kv, lv)) {
                    u128 rem = add_mod128(base1, term2, denom);
                    ctx->tested[3]++;
                    if (rem == 0U) {
                        record_hit(ctx, 3U, k, s, kv, lv, denom);
                    } else if (denom > 1U) {
                        record_near_miss(ctx, 3U, k, s, kv, lv, denom, rem);
                    }
                }
                term2 = add_mod128(term2, term2, denom);
            }
        }
    }
}

static void run_task_m4(worker_ctx_t *ctx, const work_task_t *t) {
    uint32_t k = t->k;
    uint32_t s = t->s;
    uint32_t k0 = t->k0;
    uint32_t k1 = t->k1;
    uint32_t rem_l = s - k + 4U;
    if (rem_l < 8U) {
        return;
    }

    u128 denom = g_pow2[s] - g_pow3[k];
    u128 c0_mod = (g_pow3[k0] - g_pow2[k0]) % denom;
    u128 c1_mod = (g_pow3[k1] - g_pow2[k1]) % denom;

    uint32_t kv[MAX_M] = {k0, k1, 0U, 0U};
    uint32_t lv[MAX_M] = {0U, 0U, 0U, 0U};

    for (uint32_t k2 = k0; k2 <= k - 2U * k0 - k1; k2++) {
        uint32_t k3 = k - k0 - k1 - k2;
        if (k3 < k0) {
            continue;
        }
        kv[2] = k2;
        kv[3] = k3;

        u128 c2_mod = (g_pow3[k2] - g_pow2[k2]) % denom;
        u128 c3_mod = (g_pow3[k3] - g_pow2[k3]) % denom;
        u128 base0 = mul_mod128(g_pow3[k1 + k2 + k3] % denom, c0_mod, denom);
        u128 p3_23_c1 = mul_mod128(g_pow3[k2 + k3] % denom, c1_mod, denom);
        u128 p3_3_c2 = mul_mod128(g_pow3[k3] % denom, c2_mod, denom);

        uint32_t l0_max = rem_l - 6U;
        for (uint32_t l0 = 2U; l0 <= l0_max; l0++) {
            uint32_t s0 = (k0 - 1U) + l0;
            u128 term1 = mul_mod128(g_pow2[s0] % denom, p3_23_c1, denom);
            u128 base1 = add_mod128(base0, term1, denom);

            uint32_t l1_start = (k1 == k0) ? l0 : 2U;
            uint32_t l1_max = rem_l - l0 - 4U;
            if (l1_start > l1_max) {
                continue;
            }

            uint32_t s01_start = s0 + (k1 - 1U) + l1_start;
            u128 term2 = mul_mod128(g_pow2[s01_start] % denom, p3_3_c2, denom);

            lv[0] = l0;
            for (uint32_t l1 = l1_start; l1 <= l1_max; l1++) {
                u128 base2 = add_mod128(base1, term2, denom);
                uint32_t s01 = s0 + (k1 - 1U) + l1;

                uint32_t l2_start = (k2 == k0) ? l0 : 2U;
                uint32_t rem_23 = rem_l - l0 - l1;
                uint32_t l2_max = (rem_23 >= 2U) ? (rem_23 - 2U) : 0U;
                if (k3 == k0) {
                    if (rem_23 < l0 + 2U) {
                        l2_max = 0U;
                    } else if (rem_23 - l0 < l2_max) {
                        l2_max = rem_23 - l0;
                    }
                }
                if (l2_start <= l2_max) {
                    uint32_t s012_start = s01 + (k2 - 1U) + l2_start;
                    u128 term3 = mul_mod128(g_pow2[s012_start] % denom, c3_mod, denom);
                    lv[1] = l1;
                    for (uint32_t l2 = l2_start; l2 <= l2_max; l2++) {
                        uint32_t l3 = rem_l - l0 - l1 - l2;
                        lv[2] = l2;
                        lv[3] = l3;
                        if (is_canonical_m(4U, kv, lv)) {
                            u128 rem = add_mod128(base2, term3, denom);
                            ctx->tested[4]++;
                            if (rem == 0U) {
                                record_hit(ctx, 4U, k, s, kv, lv, denom);
                            } else if (denom > 1U) {
                                record_near_miss(ctx, 4U, k, s, kv, lv, denom, rem);
                            }
                        }
                        term3 = add_mod128(term3, term3, denom);
                    }
                }
                term2 = add_mod128(term2, term2, denom);
            }
        }
    }
}

static void *worker_entry(void *arg) {
    worker_ctx_t *ctx = (worker_ctx_t *)arg;
    for (size_t idx = ctx->thread_id; idx < ctx->task_count; idx += ctx->num_threads) {
        const work_task_t *t = &ctx->tasks[idx];
        if (t->m == 2U) {
            run_task_m2(ctx, t);
        } else if (t->m == 3U) {
            run_task_m3(ctx, t);
        } else if (t->m == 4U) {
            run_task_m4(ctx, t);
        }
    }
    return NULL;
}

static int run_self_test(void) {
    /* 1. add_mod128 and mul_mod128 near 2^127 boundary */
    u128 big_m = ((u128)1 << 127) - 1U; /* 2^127 - 1 (Mersenne prime M_127) */
    u128 a = big_m - 5U;
    u128 b = big_m - 7U;
    if (add_mod128(a, b, big_m) != big_m - 12U) {
        fprintf(stderr, "FAIL: add_mod128 near 2^127-1\n");
        return 1;
    }
    if (mul_mod128(a, b, big_m) != 35U) {
        fprintf(stderr, "FAIL: mul_mod128 (-5)*(-7) mod (2^127-1)\n");
        return 1;
    }

    /* 2. Closed-form m-circuit numerator identity vs step-by-step C(v) on m = 1, 2, 3, 4 */
    {
        const uint32_t k1[1] = {5};
        const uint32_t l1[1] = {4};
        if (u320_cmp(exact_mcircuit_numerator(1, k1, l1), step_by_step_numerator(1, k1, l1)) != 0) {
            fprintf(stderr, "FAIL: 1-circuit closed-form vs step-by-step\n");
            return 1;
        }
        const uint32_t k2[2] = {4, 3};
        const uint32_t l2[2] = {2, 4};
        if (u320_cmp(exact_mcircuit_numerator(2, k2, l2), step_by_step_numerator(2, k2, l2)) != 0) {
            fprintf(stderr, "FAIL: 2-circuit closed-form vs step-by-step\n");
            return 1;
        }
        const uint32_t k3[3] = {2, 5, 3};
        const uint32_t l3[3] = {3, 2, 4};
        if (u320_cmp(exact_mcircuit_numerator(3, k3, l3), step_by_step_numerator(3, k3, l3)) != 0) {
            fprintf(stderr, "FAIL: 3-circuit closed-form vs step-by-step\n");
            return 1;
        }
        const uint32_t k4[4] = {1, 3, 2, 4};
        const uint32_t l4[4] = {2, 5, 2, 3};
        if (u320_cmp(exact_mcircuit_numerator(4, k4, l4), step_by_step_numerator(4, k4, l4)) != 0) {
            fprintf(stderr, "FAIL: 4-circuit closed-form vs step-by-step\n");
            return 1;
        }
    }

    /* 3. Positive detection of trivial 1-circuit (k0=1, l0=2 -> K=1, S=2, D=1, n=1) */
    {
        const uint32_t kv[1] = {1};
        const uint32_t lv[1] = {2};
        u320_t c_val = exact_mcircuit_numerator(1U, kv, lv);
        u128 denom = g_pow2[2] - g_pow3[1];
        u320_t q;
        u128 rem = 0U;
        u320_divmod_u128(c_val, denom, &q, &rem);
        if (rem != 0U || q.w[0] != 1ULL || q.w[1] != 0ULL) {
            fprintf(stderr, "FAIL: trivial 1-circuit detection (expected n=1)\n");
            return 1;
        }
    }

    /* 4. Negative 3n+1 cycle detection: n = -17 is a 2-circuit (k=[4,3], l=[2,4], K=7, S=11) */
    {
        const uint32_t kv[2] = {4, 3};
        const uint32_t lv[2] = {2, 4};
        u320_t c_val = exact_mcircuit_numerator(2U, kv, lv);
        u128 abs_denom = g_pow3[7] - g_pow2[11]; /* 2187 - 2048 = 139 */
        u320_t q;
        u128 rem = 0U;
        u320_divmod_u128(c_val, abs_denom, &q, &rem);
        if (abs_denom != 139U || rem != 0U || q.w[0] != 17ULL || q.w[1] != 0ULL) {
            fprintf(stderr, "FAIL: negative 2-circuit -17 detection\n");
            return 1;
        }
    }

    /* 5. High-K guard check: K=80, S=127 exact mod evaluation without UB */
    {
        const uint32_t kv[2] = {40, 40};
        const uint32_t lv[2] = {25, 24}; /* S = 39+25 + 39+24 = 127 */
        u128 denom = g_pow2[127] - g_pow3[80];
        u320_t c_val = exact_mcircuit_numerator(2U, kv, lv);
        u320_t q;
        u128 rem_exact = 0U;
        u320_divmod_u128(c_val, denom, &q, &rem_exact);

        u128 c0_mod = (g_pow3[40] - g_pow2[40]) % denom;
        u128 t0 = mul_mod128(g_pow3[40] % denom, c0_mod, denom);
        u128 t1 = mul_mod128(g_pow2[64] % denom, c0_mod, denom);
        u128 rem_fast = add_mod128(t0, t1, denom);
        if (rem_exact != rem_fast) {
            fprintf(stderr, "FAIL: K=80, S=127 fast modular vs exact u320 mismatch\n");
            return 1;
        }
    }

    printf("[OK] mcircuit_hunter C11 self-test: mod128, closed-form, n=1, n=-17, K=80/S=127 passed\n");
    return 0;
}

static void print_u32_vec(FILE *fp, const uint32_t *v, uint32_t len) {
    fprintf(fp, "[");
    for (uint32_t i = 0; i < len; i++) {
        fprintf(fp, "%u%s", v[i], (i + 1U < len) ? ", " : "");
    }
    fprintf(fp, "]");
}

static bool parse_u32(const char *s, uint32_t *out) {
    if (!s || *s == '\0' || *s == '-') {
        return false;
    }
    char *end = NULL;
    errno = 0;
    unsigned long val = strtoul(s, &end, 10);
    if (errno != 0 || end == s || *end != '\0' || val > UINT32_MAX) {
        return false;
    }
    *out = (uint32_t)val;
    return true;
}

int main(int argc, char **argv) {
    init_tables();

    uint32_t k_max[MAX_M + 1] = {0, 0, 80, 79, 58};
    uint32_t threads = 8U;
    bound_mode_t bound_mode = BOUND_SIMONS;
    bool self_test = false;
    const char *json_out = NULL;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--self-test") == 0) {
            self_test = true;
        } else if (strcmp(argv[i], "--k2-max") == 0 && i + 1 < argc) {
            if (!parse_u32(argv[++i], &k_max[2])) {
                fprintf(stderr, "Invalid --k2-max\n");
                return 2;
            }
        } else if (strcmp(argv[i], "--k3-max") == 0 && i + 1 < argc) {
            if (!parse_u32(argv[++i], &k_max[3])) {
                fprintf(stderr, "Invalid --k3-max\n");
                return 2;
            }
        } else if (strcmp(argv[i], "--k4-max") == 0 && i + 1 < argc) {
            if (!parse_u32(argv[++i], &k_max[4])) {
                fprintf(stderr, "Invalid --k4-max\n");
                return 2;
            }
        } else if (strcmp(argv[i], "--threads") == 0 && i + 1 < argc) {
            if (!parse_u32(argv[++i], &threads) || threads < 1U || threads > 64U) {
                fprintf(stderr, "Invalid --threads (1..64)\n");
                return 2;
            }
        } else if (strcmp(argv[i], "--bound") == 0 && i + 1 < argc) {
            const char *b = argv[++i];
            if (strcmp(b, "simons") == 0) {
                bound_mode = BOUND_SIMONS;
            } else if (strcmp(b, "eliahou") == 0) {
                bound_mode = BOUND_ELIAHOU;
            } else {
                fprintf(stderr, "Invalid --bound (simons|eliahou)\n");
                return 2;
            }
        } else if (strcmp(argv[i], "--json-out") == 0 && i + 1 < argc) {
            json_out = argv[++i];
        } else if (strcmp(argv[i], "--help") == 0 || strcmp(argv[i], "-h") == 0) {
            fprintf(stderr,
                    "Usage: %s [--self-test] [--k2-max K] [--k3-max K] [--k4-max K] "
                    "[--bound simons|eliahou] [--threads N] [--json-out PATH|-]\n",
                    argv[0]);
            return 0;
        } else {
            fprintf(stderr, "Unknown argument: %s\n", argv[i]);
            return 2;
        }
    }

    if (self_test) {
        return run_self_test();
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    uint64_t guard_skips[MAX_M + 1] = {0};
    size_t task_cap = 4096U;
    size_t task_count = 0U;
    work_task_t *tasks = malloc(task_cap * sizeof(work_task_t));
    if (!tasks) {
        fprintf(stderr, "ERROR: Failed to allocate task array\n");
        return 1;
    }

    for (uint32_t m = 2U; m <= 4U; m++) {
        uint32_t km = k_max[m];
        if (km < m) {
            continue;
        }
        for (uint32_t k = m; k <= km; k++) {
            if (k > MAX_K_LIMIT) {
                guard_skips[m]++;
                continue;
            }
            uint32_t s_lo = g_s_min[k];
            uint32_t s_hi = (bound_mode == BOUND_ELIAHOU) ? g_s_max_eliahou[k] : g_s_max_simons[m][k];
            if (s_hi < s_lo) {
                continue;
            }
            for (uint32_t s = s_lo; s <= s_hi; s++) {
                if (s > MAX_S_LIMIT) {
                    guard_skips[m]++;
                    continue;
                }
                uint32_t rem_l = s - k + m;
                if (rem_l < 2U * m) {
                    continue;
                }
                if (m == 2U || m == 3U) {
                    for (uint32_t k0 = 1U; k0 <= k / m; k0++) {
                        if (task_count == task_cap) {
                            task_cap *= 2U;
                            work_task_t *tmp = realloc(tasks, task_cap * sizeof(work_task_t));
                            if (!tmp) {
                                free(tasks);
                                return 1;
                            }
                            tasks = tmp;
                        }
                        tasks[task_count++] = (work_task_t){m, k, s, k0, 0U};
                    }
                } else {
                    for (uint32_t k0 = 1U; k0 <= k / 4U; k0++) {
                        for (uint32_t k1 = k0; k1 <= k - 3U * k0; k1++) {
                            if (task_count == task_cap) {
                                task_cap *= 2U;
                                work_task_t *tmp = realloc(tasks, task_cap * sizeof(work_task_t));
                                if (!tmp) {
                                    free(tasks);
                                    return 1;
                                }
                                tasks = tmp;
                            }
                            tasks[task_count++] = (work_task_t){4U, k, s, k0, k1};
                        }
                    }
                }
            }
        }
    }

    uint32_t active_threads = (task_count == 0U) ? 1U : threads;
    if (task_count > 0U && active_threads > task_count) {
        active_threads = (uint32_t)task_count;
    }

    worker_ctx_t *ctxs = calloc(active_threads, sizeof(worker_ctx_t));
    pthread_t *tids = calloc(active_threads, sizeof(pthread_t));
    if (!ctxs || !tids) {
        free(tasks);
        free(ctxs);
        free(tids);
        return 1;
    }

    for (uint32_t t = 0; t < active_threads; t++) {
        ctxs[t].tasks = tasks;
        ctxs[t].task_count = task_count;
        ctxs[t].thread_id = t;
        ctxs[t].num_threads = active_threads;
    }

    if (active_threads == 1U) {
        worker_entry(&ctxs[0]);
    } else {
        for (uint32_t t = 0; t < active_threads; t++) {
            if (pthread_create(&tids[t], NULL, worker_entry, &ctxs[t]) != 0) {
                fprintf(stderr, "ERROR: pthread_create failed\n");
                free(tasks);
                free(ctxs);
                free(tids);
                return 1;
            }
        }
        for (uint32_t t = 0; t < active_threads; t++) {
            pthread_join(tids[t], NULL);
        }
    }

    /* Deterministic merge across workers */
    uint64_t total_tested_m[MAX_M + 1] = {0};
    uint64_t total_tested_all = 0ULL;
    uint64_t total_skips_all = 0ULL;
    for (uint32_t m = 2U; m <= 4U; m++) {
        total_skips_all += guard_skips[m];
    }

    size_t all_hits_cap = 0U;
    for (uint32_t t = 0; t < active_threads; t++) {
        for (uint32_t m = 2U; m <= 4U; m++) {
            total_tested_m[m] += ctxs[t].tested[m];
        }
        all_hits_cap += ctxs[t].hit_count;
    }
    for (uint32_t m = 2U; m <= 4U; m++) {
        total_tested_all += total_tested_m[m];
    }

    hit_record_t *all_hits = all_hits_cap ? malloc(all_hits_cap * sizeof(hit_record_t)) : NULL;
    size_t all_hits_count = 0U;
    for (uint32_t t = 0; t < active_threads; t++) {
        for (size_t i = 0; i < ctxs[t].hit_count; i++) {
            all_hits[all_hits_count++] = ctxs[t].hits[i];
        }
    }
    if (all_hits_count > 1U) {
        qsort(all_hits, all_hits_count, sizeof(hit_record_t), cmp_hit_qsort);
    }

    size_t nontrivial_hits = 0U;
    for (size_t i = 0; i < all_hits_count; i++) {
        if (!all_hits[i].is_trivial) {
            nontrivial_hits++;
        }
    }

    candidate_record_t merged_near[MAX_M + 1][TOP_NEAR_PER_M];
    size_t merged_near_count[MAX_M + 1] = {0};
    size_t max_worker_near = (size_t)active_threads * TOP_NEAR_PER_M;
    candidate_record_t *scratch = malloc(max_worker_near * sizeof(candidate_record_t));
    if (!scratch) {
        free(all_hits);
        free(tasks);
        free(ctxs);
        free(tids);
        return 1;
    }

    for (uint32_t m = 2U; m <= 4U; m++) {
        size_t sc = 0U;
        for (uint32_t t = 0; t < active_threads; t++) {
            for (size_t i = 0; i < ctxs[t].near_count[m]; i++) {
                scratch[sc++] = ctxs[t].near[m][i];
            }
        }
        if (sc > 1U) {
            qsort(scratch, sc, sizeof(candidate_record_t), cmp_near_qsort);
        }
        size_t keep = (sc < TOP_NEAR_PER_M) ? sc : TOP_NEAR_PER_M;
        merged_near_count[m] = keep;
        for (size_t i = 0; i < keep; i++) {
            merged_near[m][i] = scratch[i];
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (double)(t1.tv_sec - t0.tv_sec) + (double)(t1.tv_nsec - t0.tv_nsec) * 1e-9;

    FILE *fp = stdout;
    if (json_out && strcmp(json_out, "-") != 0) {
        fp = fopen(json_out, "w");
        if (!fp) {
            perror("fopen json_out");
            free(scratch);
            free(all_hits);
            free(tasks);
            free(ctxs);
            free(tids);
            return 1;
        }
    }

    const char *bound_name = (bound_mode == BOUND_ELIAHOU) ? "eliahou" : "simons";
    fprintf(fp, "{\n");
    fprintf(fp, "  \"canonical\": {\n");
    fprintf(fp, "    \"schema\": \"solve-collatz-mcircuit-hunter/v1\",\n");
    fprintf(fp, "    \"engine\": \"mcircuit_hunter.c\",\n");
    fprintf(fp, "    \"bound_mode\": \"%s\",\n", bound_name);
    fprintf(fp, "    \"k_limit_u128\": %u,\n", MAX_K_LIMIT);
    fprintf(fp, "    \"s_limit_u128\": %u,\n", MAX_S_LIMIT);
    fprintf(fp, "    \"overflow_guard_skips\": %" PRIu64 ",\n", total_skips_all);
    fprintf(fp, "    \"total_candidates_tested\": %" PRIu64 ",\n", total_tested_all);
    fprintf(fp, "    \"total_hits\": %zu,\n", nontrivial_hits);
    fprintf(fp, "    \"families\": [\n");
    for (uint32_t m = 2U; m <= 4U; m++) {
        uint32_t km = k_max[m];
        uint32_t kmin_eff = (km >= m) ? m : 0U;
        uint32_t kmax_eff = (km >= m) ? km : 0U;
        size_t fam_hits = 0U;
        for (size_t i = 0; i < all_hits_count; i++) {
            if (all_hits[i].m == m && !all_hits[i].is_trivial) {
                fam_hits++;
            }
        }
        fprintf(fp, "      {\n");
        fprintf(fp, "        \"m\": %u,\n", m);
        fprintf(fp, "        \"k_min\": %u,\n", kmin_eff);
        fprintf(fp, "        \"k_max\": %u,\n", kmax_eff);
        if (bound_mode == BOUND_ELIAHOU) {
            fprintf(fp, "        \"s_rule\": \"S_min(K) <= S <= floor(K*log2(10/3)) via 3^K*2^S <= 10^K (S <= 127)\",\n");
        } else {
            fprintf(fp, "        \"s_rule\": \"S_min(K) <= S < K*log2(3) + %u*log2(4/3) via 2^S*3^%u < 4^%u*3^K (S <= 127)\",\n", m, m, m);
        }
        fprintf(fp, "        \"candidates_tested\": %" PRIu64 ",\n", total_tested_m[m]);
        fprintf(fp, "        \"overflow_guard_skips\": %" PRIu64 ",\n", guard_skips[m]);
        fprintf(fp, "        \"hits_found\": %zu,\n", fam_hits);
        fprintf(fp, "        \"near_misses\": [\n");
        for (size_t i = 0; i < merged_near_count[m]; i++) {
            const candidate_record_t *nr = &merged_near[m][i];
            char d_buf[64], r_buf[64], dn_buf[64];
            u128_to_str(nr->denom, d_buf, sizeof(d_buf));
            u128_to_str(nr->rem, r_buf, sizeof(r_buf));
            u128_to_str(nr->dist_num, dn_buf, sizeof(dn_buf));
            double da = isfinite((double)nr->dist_approx) ? (double)nr->dist_approx : 0.0;
            fprintf(fp, "          {\"m\": %u, \"k\": %u, \"s\": %u, \"k_vec\": ", nr->m, nr->k, nr->s);
            print_u32_vec(fp, nr->k_vec, nr->m);
            fprintf(fp, ", \"l_vec\": ");
            print_u32_vec(fp, nr->l_vec, nr->m);
            fprintf(fp, ", \"denom\": \"%s\", \"rem\": \"%s\", \"dist_num\": \"%s\", \"dist_approx\": %.12e}%s\n",
                    d_buf, r_buf, dn_buf, da, (i + 1U < merged_near_count[m]) ? "," : "");
        }
        fprintf(fp, "        ]\n");
        fprintf(fp, "      }%s\n", (m < 4U) ? "," : "");
    }
    fprintf(fp, "    ],\n");
    fprintf(fp, "    \"hits\": [\n");
    size_t printed_hits = 0U;
    for (size_t i = 0; i < all_hits_count; i++) {
        const hit_record_t *h = &all_hits[i];
        if (h->is_trivial) {
            continue;
        }
        char d_buf[64], n_buf[128];
        u128_to_str(h->denom, d_buf, sizeof(d_buf));
        u320_to_str(h->n_cand, n_buf, sizeof(n_buf));
        fprintf(fp, "%s      {\"m\": %u, \"k\": %u, \"s\": %u, \"k_vec\": ",
                (printed_hits > 0U) ? ",\n" : "", h->m, h->k, h->s);
        print_u32_vec(fp, h->k_vec, h->m);
        fprintf(fp, ", \"l_vec\": ");
        print_u32_vec(fp, h->l_vec, h->m);
        fprintf(fp, ", \"denom\": \"%s\", \"n\": \"%s\"}", d_buf, n_buf);
        printed_hits++;
    }
    if (printed_hits > 0U) {
        fprintf(fp, "\n");
    }
    fprintf(fp, "    ]\n");
    fprintf(fp, "  },\n");
    fprintf(fp, "  \"telemetry\": {\n");
    fprintf(fp, "    \"threads\": %u,\n", active_threads);
    fprintf(fp, "    \"elapsed_seconds\": %.6f\n", elapsed);
    fprintf(fp, "  }\n");
    fprintf(fp, "}\n");

    if (fp != stdout) {
        fclose(fp);
    }

    free(scratch);
    free(all_hits);
    free(tasks);
    free(ctxs);
    free(tids);
    return (nontrivial_hits > 0U) ? 10 : 0;
}
