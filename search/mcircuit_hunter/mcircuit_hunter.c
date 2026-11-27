/*
 * mcircuit_hunter.c — High-throughput C11 canonical m-circuit Diophantine cycle hunter (m = 2..6).
 *
 * Track B (`Disprove/`) off-kernel search engine for `solve-collatz` (`DISPROVE-002 Phase 4`).
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
 *     - For m = 5, 243 * 2^S < 1024 * 3^K; for m = 6, 729 * 2^S < 4096 * 3^K
 *       (checked via exact 1024-bit integer arithmetic).
 *     - The looser general Eliahou bound (used in `search/cycle_hunter.py`) is:
 *           2^S * 3^K <= 10^K   (with S = S_min(K) always included).
 *
 * Arithmetic & UB safety:
 *   - Tier 0: Fast `u128` path for K <= 80, S <= 127 (D < 2^127).
 *   - Tier 1: Multi-limb `u256_t` modular engine for K <= 160, S <= 255 (D < 2^255).
 *   - Tier 2: Multi-limb `u512_t` modular engine lifting the ceiling to K <= 256, S <= 511
 *             (D < 2^511), covering m = 2..6 up to K <= 240+ with zero overflow_guard_skips.
 *   - Exact `u1024_t` (16 x 64-bit limbs) for precomputation (up to 10^256) & hit recovery.
 *   - Innermost loops update only via `add_mod` (zero inner-loop multiplications) and fast
 *     threshold-guarded near-miss tracking.
 *   - Lock-free pthread execution with strict error handling and deterministic merge.
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

#define MAX_M 6U
#define MAX_K_U128 80U
#define MAX_S_U128 127U
#define MAX_K_U256 160U
#define MAX_S_U256 255U
#define MAX_K_LIMIT 256U
#define MAX_S_LIMIT 511U
#define TOP_NEAR_PER_M 5U
#define MAX_HITS_PER_WORKER 64U

typedef enum {
    BOUND_SIMONS = 0,
    BOUND_ELIAHOU = 1
} bound_mode_t;

/* Multi-limb little-endian unsigned integers: 256-bit, 512-bit, and 1024-bit. */
typedef struct {
    uint64_t w[4];
} u256_t;

typedef struct {
    uint64_t w[8];
} u512_t;

typedef struct {
    uint64_t w[16];
} u1024_t;

typedef struct {
    uint32_t m;
    uint32_t k;
    uint32_t s;
    uint32_t k_vec[MAX_M];
    uint32_t l_vec[MAX_M];
    u512_t denom;
    u512_t rem;
    u512_t dist_num;
    long double dist_approx;
} candidate_record_t;

typedef struct {
    uint32_t m;
    uint32_t k;
    uint32_t s;
    uint32_t k_vec[MAX_M];
    uint32_t l_vec[MAX_M];
    u512_t denom;
    u1024_t n_cand;
    bool is_trivial;
} hit_record_t;

typedef struct {
    uint32_t m;
    uint32_t k;
    uint32_t s;
    uint32_t k0;
    uint32_t k1; /* used for m == 4, m == 5, and m == 6 */
} work_task_t;

typedef struct {
    const work_task_t *tasks;
    size_t task_count;
    uint32_t thread_id;
    uint32_t num_threads;
    uint32_t min_tier; /* 0 = auto, 1 = force >= u256, 2 = force u512 */
    uint64_t tested[MAX_M + 1];
    hit_record_t hits[MAX_HITS_PER_WORKER];
    size_t hit_count;
    candidate_record_t near[MAX_M + 1][TOP_NEAR_PER_M];
    size_t near_count[MAX_M + 1];
    size_t near_worst_idx[MAX_M + 1];
    long double near_worst_dist[MAX_M + 1];
} worker_ctx_t;

/* Precomputed exact tables for u128, u256, and u512 tiers. */
static u128 g_pow3_128[MAX_K_U128 + 1U];
static u128 g_pow2_128[MAX_S_U128 + 1U];
static u256_t g_pow3_256[MAX_K_U256 + 1U];
static u256_t g_pow2_256[MAX_S_U256 + 1U];
static u512_t g_pow3_512[MAX_K_LIMIT + 1U];
static u512_t g_pow2_512[MAX_S_LIMIT + 1U];
static uint32_t g_s_min[MAX_K_LIMIT + 1U];
static uint32_t g_s_max_eliahou[MAX_K_LIMIT + 1U];
static uint32_t g_s_max_simons[MAX_M + 1U][MAX_K_LIMIT + 1U];

/* -------------------------------------------------------------------------- */
/* Overflow-free u128 and shared multi-limb modular arithmetic                */
/* -------------------------------------------------------------------------- */

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

static inline bool limbs_is_zero(const uint64_t *a, size_t n) {
    uint64_t acc = 0ULL;
    for (size_t i = 0; i < n; i++) {
        acc |= a[i];
    }
    return acc == 0ULL;
}

static inline int limbs_cmp(const uint64_t *a, const uint64_t *b, size_t n) {
    for (size_t i = n; i > 0; i--) {
        if (a[i - 1U] != b[i - 1U]) {
            return (a[i - 1U] > b[i - 1U]) ? 1 : -1;
        }
    }
    return 0;
}

static inline void limbs_add(uint64_t *r, const uint64_t *a, const uint64_t *b, size_t n) {
    u128 carry = 0U;
    for (size_t i = 0; i < n; i++) {
        u128 s = (u128)a[i] + (u128)b[i] + carry;
        r[i] = (uint64_t)s;
        carry = s >> 64;
    }
}

static inline void limbs_sub(uint64_t *r, const uint64_t *a, const uint64_t *b, size_t n) {
    uint64_t borrow = 0ULL;
    for (size_t i = 0; i < n; i++) {
        uint64_t sub_amt = b[i] + borrow;
        uint64_t next_borrow = ((sub_amt < b[i]) || (a[i] < sub_amt)) ? 1ULL : 0ULL;
        r[i] = a[i] - sub_amt;
        borrow = next_borrow;
    }
}

static inline void limbs_shl1(uint64_t *r, const uint64_t *a, size_t n) {
    uint64_t carry = 0ULL;
    for (size_t i = 0; i < n; i++) {
        uint64_t next_carry = a[i] >> 63;
        r[i] = (a[i] << 1) | carry;
        carry = next_carry;
    }
}

static inline void limbs_shr1(uint64_t *r, const uint64_t *a, size_t n) {
    uint64_t carry = 0ULL;
    for (size_t i = n; i > 0; i--) {
        uint64_t cur = a[i - 1U];
        r[i - 1U] = (cur >> 1) | carry;
        carry = cur << 63;
    }
}

static inline void limbs_shl(uint64_t *r, const uint64_t *a, uint32_t shift, size_t n) {
    memset(r, 0, n * sizeof(uint64_t));
    uint32_t ws = shift / 64U;
    uint32_t bs = shift % 64U;
    for (size_t i = 0; i < n; i++) {
        if (i + ws >= n) {
            continue;
        }
        r[i + ws] |= (a[i] << bs);
        if (bs > 0U && i + ws + 1U < n) {
            r[i + ws + 1U] |= (a[i] >> (64U - bs));
        }
    }
}

static inline void limbs_mul_u64(uint64_t *r, const uint64_t *a, uint64_t m, size_t n) {
    u128 carry = 0U;
    for (size_t i = 0; i < n; i++) {
        u128 prod = (u128)a[i] * (u128)m + carry;
        r[i] = (uint64_t)prod;
        carry = prod >> 64;
    }
}

static inline int limbs_highest_bit(const uint64_t *a, size_t n) {
    for (size_t i = n; i > 0; i--) {
        uint64_t v = a[i - 1U];
        if (v != 0ULL) {
            int b = 0;
            while (v >>= 1) {
                b++;
            }
            return (int)((i - 1U) * 64U) + b;
        }
    }
    return -1;
}

static inline void limbs_mod(uint64_t *rem, const uint64_t *a, const uint64_t *m, size_t n) {
    memset(rem, 0, n * sizeof(uint64_t));
    if (limbs_is_zero(m, n)) {
        return;
    }
    if (limbs_cmp(a, m, n) < 0) {
        memcpy(rem, a, n * sizeof(uint64_t));
        return;
    }
    uint64_t hi = 0ULL;
    for (size_t i = 2; i < n; i++) {
        hi |= a[i] | m[i];
    }
    if (hi == 0ULL) {
        u128 a128 = ((u128)a[1] << 64) | (u128)a[0];
        u128 m128 = ((u128)m[1] << 64) | (u128)m[0];
        u128 r128 = a128 % m128;
        rem[0] = (uint64_t)r128;
        rem[1] = (uint64_t)(r128 >> 64);
        return;
    }
    int top = limbs_highest_bit(a, n);
    for (int bit = top; bit >= 0; bit--) {
        uint32_t wi = (uint32_t)bit / 64U;
        uint32_t bi = (uint32_t)bit % 64U;
        uint64_t b = (a[wi] >> bi) & 1ULL;
        bool carry = (rem[n - 1U] >> 63) != 0ULL;
        limbs_shl1(rem, rem, n);
        rem[0] |= b;
        if (carry || limbs_cmp(rem, m, n) >= 0) {
            limbs_sub(rem, rem, m, n);
        }
    }
}

static inline void limbs_add_mod(uint64_t *r, const uint64_t *a, const uint64_t *b,
                                 const uint64_t *m, size_t n) {
    uint64_t diff[16];
    limbs_sub(diff, m, b, n);
    if (limbs_cmp(a, diff, n) >= 0) {
        limbs_sub(r, a, diff, n);
    } else {
        limbs_add(r, a, b, n);
    }
}

static inline void limbs_mul_mod(uint64_t *res, const uint64_t *a_in, const uint64_t *b_in,
                                 const uint64_t *m, size_t n) {
    memset(res, 0, n * sizeof(uint64_t));
    uint64_t one[16] = {1ULL};
    if (limbs_cmp(m, one, n) <= 0) {
        return;
    }
    uint64_t a[16], b[16];
    limbs_mod(a, a_in, m, n);
    limbs_mod(b, b_in, m, n);
    while (!limbs_is_zero(b, n)) {
        if (b[0] & 1ULL) {
            limbs_add_mod(res, res, a, m, n);
        }
        limbs_shr1(b, b, n);
        if (!limbs_is_zero(b, n)) {
            limbs_add_mod(a, a, a, m, n);
        }
    }
}

static inline long double limbs_to_ld(const uint64_t *w, size_t n) {
    long double acc = 0.0L;
    for (size_t i = n; i > 0; i--) {
        acc = ldexpl(acc, 64) + (long double)w[i - 1U];
    }
    return acc;
}

/* Type-safe u256_t inline wrappers */
static inline u256_t u256_zero(void) {
    u256_t r = {{0ULL}};
    return r;
}

static inline u256_t u256_from_u64(uint64_t v) {
    u256_t r = {{v, 0ULL, 0ULL, 0ULL}};
    return r;
}

static inline u256_t u256_from_u128(u128 v) {
    u256_t r = {{(uint64_t)v, (uint64_t)(v >> 64), 0ULL, 0ULL}};
    return r;
}

static inline bool u256_is_zero(u256_t a) { return limbs_is_zero(a.w, 4U); }
static inline int u256_cmp(u256_t a, u256_t b) { return limbs_cmp(a.w, b.w, 4U); }

static inline u256_t u256_sub(u256_t a, u256_t b) {
    u256_t r;
    limbs_sub(r.w, a.w, b.w, 4U);
    return r;
}

static inline u256_t u256_shl1(u256_t a) {
    u256_t r;
    limbs_shl1(r.w, a.w, 4U);
    return r;
}

static inline u256_t u256_shr1(u256_t a) {
    u256_t r;
    limbs_shr1(r.w, a.w, 4U);
    return r;
}

static inline u256_t u256_shl(u256_t a, uint32_t shift) {
    u256_t r;
    limbs_shl(r.w, a.w, shift, 4U);
    return r;
}

static inline u256_t u256_mul_u64(u256_t a, uint64_t m) {
    u256_t r;
    limbs_mul_u64(r.w, a.w, m, 4U);
    return r;
}

static inline u256_t u256_mod(u256_t a, u256_t m) {
    u256_t r;
    limbs_mod(r.w, a.w, m.w, 4U);
    return r;
}

static inline u256_t u256_add_mod(u256_t a, u256_t b, u256_t m) {
    u256_t r;
    limbs_add_mod(r.w, a.w, b.w, m.w, 4U);
    return r;
}

static inline u256_t u256_mul_mod(u256_t a, u256_t b, u256_t m) {
    u256_t r;
    limbs_mul_mod(r.w, a.w, b.w, m.w, 4U);
    return r;
}

static inline long double u256_to_ld(u256_t v) { return limbs_to_ld(v.w, 4U); }

/* Type-safe u512_t inline wrappers */
static inline u512_t u512_zero(void) {
    u512_t r = {{0ULL}};
    return r;
}

static inline u512_t u512_from_u64(uint64_t v) {
    u512_t r = {{v, 0ULL}};
    return r;
}

static inline u512_t u512_from_u128(u128 v) {
    u512_t r = {{(uint64_t)v, (uint64_t)(v >> 64), 0ULL}};
    return r;
}

static inline u512_t u512_from_u256(u256_t v) {
    u512_t r = {{v.w[0], v.w[1], v.w[2], v.w[3], 0ULL, 0ULL, 0ULL, 0ULL}};
    return r;
}

static inline bool u512_is_zero(u512_t a) { return limbs_is_zero(a.w, 8U); }
static inline int u512_cmp(u512_t a, u512_t b) { return limbs_cmp(a.w, b.w, 8U); }

static inline u512_t u512_sub(u512_t a, u512_t b) {
    u512_t r;
    limbs_sub(r.w, a.w, b.w, 8U);
    return r;
}

static inline u512_t u512_shl1(u512_t a) {
    u512_t r;
    limbs_shl1(r.w, a.w, 8U);
    return r;
}

static inline u512_t u512_shr1(u512_t a) {
    u512_t r;
    limbs_shr1(r.w, a.w, 8U);
    return r;
}

static inline u512_t u512_shl(u512_t a, uint32_t shift) {
    u512_t r;
    limbs_shl(r.w, a.w, shift, 8U);
    return r;
}

static inline u512_t u512_mul_u64(u512_t a, uint64_t m) {
    u512_t r;
    limbs_mul_u64(r.w, a.w, m, 8U);
    return r;
}

static inline u512_t u512_mod(u512_t a, u512_t m) {
    u512_t r;
    limbs_mod(r.w, a.w, m.w, 8U);
    return r;
}

static inline u512_t u512_add_mod(u512_t a, u512_t b, u512_t m) {
    u512_t r;
    limbs_add_mod(r.w, a.w, b.w, m.w, 8U);
    return r;
}

static inline u512_t u512_mul_mod(u512_t a, u512_t b, u512_t m) {
    u512_t r;
    limbs_mul_mod(r.w, a.w, b.w, m.w, 8U);
    return r;
}

static inline long double u512_to_ld(u512_t v) { return limbs_to_ld(v.w, 8U); }

/* -------------------------------------------------------------------------- */
/* Exact 1024-bit arithmetic for S_max bounds & hit recovery                  */
/* -------------------------------------------------------------------------- */

static u1024_t u1024_from_u512(u512_t v) {
    u1024_t r;
    memset(&r, 0, sizeof(r));
    memcpy(r.w, v.w, sizeof(v.w));
    return r;
}

static u1024_t u1024_mul_u64(u1024_t a, uint64_t m) {
    u1024_t r;
    limbs_mul_u64(r.w, a.w, m, 16U);
    return r;
}

static u1024_t u1024_mul_u512(u512_t a, u512_t b) {
    u1024_t r;
    memset(&r, 0, sizeof(r));
    for (size_t i = 0; i < 8; i++) {
        u128 carry = 0U;
        for (size_t j = 0; j < 8; j++) {
            u128 prod = (u128)a.w[i] * (u128)b.w[j] + (u128)r.w[i + j] + carry;
            r.w[i + j] = (uint64_t)prod;
            carry = prod >> 64;
        }
        r.w[i + 8] = (uint64_t)carry;
    }
    return r;
}

static u1024_t u1024_add(u1024_t a, u1024_t b) {
    u1024_t r;
    limbs_add(r.w, a.w, b.w, 16U);
    return r;
}

static u1024_t u1024_shl(u1024_t a, uint32_t shift) {
    u1024_t r;
    limbs_shl(r.w, a.w, shift, 16U);
    return r;
}

static int u1024_cmp(u1024_t a, u1024_t b) { return limbs_cmp(a.w, b.w, 16U); }

/* Exact u1024 division by u512 denom (1 <= denom < 2^512), returning quotient and remainder. */
static void u1024_divmod_u512(u1024_t num, u512_t denom, u1024_t *out_q, u512_t *out_rem) {
    u1024_t q;
    memset(&q, 0, sizeof(q));
    u512_t rem = u512_zero();
    int top = limbs_highest_bit(num.w, 16U);
    for (int bit = top; bit >= 0; bit--) {
        uint32_t wi = (uint32_t)bit / 64U;
        uint32_t bi = (uint32_t)bit % 64U;
        uint64_t b = (num.w[wi] >> bi) & 1ULL;
        bool carry = (rem.w[7] >> 63) != 0ULL;
        rem = u512_shl1(rem);
        rem.w[0] |= b;
        if (carry || u512_cmp(rem, denom) >= 0) {
            rem = u512_sub(rem, denom);
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

static void u1024_to_str(u1024_t v, char *buf, size_t bufsz) {
    bool is_u128 = true;
    for (size_t i = 2; i < 16; i++) {
        if (v.w[i] != 0ULL) {
            is_u128 = false;
            break;
        }
    }
    if (is_u128) {
        u128_to_str(((u128)v.w[1] << 64) | (u128)v.w[0], buf, bufsz);
        return;
    }
    char tmp[360];
    size_t pos = 0;
    u512_t ten = u512_from_u64(10ULL);
    while (pos < sizeof(tmp) && !limbs_is_zero(v.w, 16U)) {
        u1024_t q;
        u512_t rem;
        u1024_divmod_u512(v, ten, &q, &rem);
        tmp[pos++] = (char)('0' + (unsigned)rem.w[0]);
        v = q;
    }
    size_t out = 0;
    while (pos > 0 && out + 1 < bufsz) {
        buf[out++] = tmp[--pos];
    }
    buf[out] = '\0';
}

static void u512_to_str(u512_t v, char *buf, size_t bufsz) {
    u1024_to_str(u1024_from_u512(v), buf, bufsz);
}

/* -------------------------------------------------------------------------- */
/* Table precomputation & exact numerator verification                        */
/* -------------------------------------------------------------------------- */

static void init_tables(void) {
    g_pow3_128[0] = 1U;
    for (uint32_t i = 1; i <= MAX_K_U128; i++) {
        g_pow3_128[i] = g_pow3_128[i - 1] * 3U;
    }
    g_pow2_128[0] = 1U;
    for (uint32_t i = 1; i <= MAX_S_U128; i++) {
        g_pow2_128[i] = g_pow2_128[i - 1] << 1;
    }

    g_pow3_256[0] = u256_from_u64(1ULL);
    for (uint32_t i = 1; i <= MAX_K_U256; i++) {
        g_pow3_256[i] = u256_mul_u64(g_pow3_256[i - 1], 3ULL);
    }
    g_pow2_256[0] = u256_from_u64(1ULL);
    for (uint32_t i = 1; i <= MAX_S_U256; i++) {
        g_pow2_256[i] = u256_shl1(g_pow2_256[i - 1]);
    }

    g_pow3_512[0] = u512_from_u64(1ULL);
    for (uint32_t i = 1; i <= MAX_K_LIMIT; i++) {
        g_pow3_512[i] = u512_mul_u64(g_pow3_512[i - 1], 3ULL);
    }
    g_pow2_512[0] = u512_from_u64(1ULL);
    for (uint32_t i = 1; i <= MAX_S_LIMIT; i++) {
        g_pow2_512[i] = u512_shl1(g_pow2_512[i - 1]);
    }

    u1024_t p10 = u1024_from_u512(u512_from_u64(1ULL));
    u1024_t p3_big = u1024_from_u512(u512_from_u64(1ULL));
    g_s_min[0] = 1U;
    g_s_max_eliahou[0] = 0U;
    for (uint32_t m = 1; m <= MAX_M; m++) {
        g_s_max_simons[m][0] = 0U;
    }

    for (uint32_t k = 1; k <= MAX_K_LIMIT; k++) {
        p10 = u1024_mul_u64(p10, 10ULL);
        p3_big = u1024_mul_u64(p3_big, 3ULL);

        uint32_t s_min = 0U;
        while (s_min <= MAX_S_LIMIT && u512_cmp(g_pow2_512[s_min], g_pow3_512[k]) <= 0) {
            s_min++;
        }
        g_s_min[k] = s_min;

        /* Exact Eliahou bound: s == s_min OR 3^k * 2^s <= 10^k */
        uint32_t s_eliahou = s_min;
        while (s_eliahou < MAX_S_LIMIT) {
            u1024_t lhs = u1024_shl(p3_big, s_eliahou + 1U);
            if (u1024_cmp(lhs, p10) <= 0) {
                s_eliahou++;
            } else {
                break;
            }
        }
        g_s_max_eliahou[k] = s_eliahou;

        /* Exact Simons-de Weger m-circuit bound: 2^S * 3^m < 4^m * 3^k */
        for (uint32_t m = 1; m <= MAX_M; m++) {
            u1024_t rhs = u1024_shl(p3_big, 2U * m); /* 4^m * 3^k */
            uint64_t p3m = 1ULL;
            for (uint32_t r = 0; r < m; r++) {
                p3m *= 3ULL;
            }
            u1024_t p3m_big = u1024_from_u512(u512_from_u64(p3m));
            uint32_t s_sim = s_min;
            u1024_t lhs0 = u1024_shl(p3m_big, s_sim);
            if (u1024_cmp(lhs0, rhs) >= 0) {
                g_s_max_simons[m][k] = s_min - 1U;
                continue;
            }
            while (s_sim < MAX_S_LIMIT) {
                u1024_t nxt = u1024_shl(p3m_big, s_sim + 1U);
                if (u1024_cmp(nxt, rhs) < 0) {
                    s_sim++;
                } else {
                    break;
                }
            }
            g_s_max_simons[m][k] = s_sim;
        }
    }
}

/* Exact closed-form m-circuit numerator C(v) in u1024_t, used for self-test & hit recovery. */
static u1024_t exact_mcircuit_numerator(uint32_t m, const uint32_t *k_vec, const uint32_t *l_vec) {
    uint32_t K = 0U;
    for (uint32_t j = 0; j < m; j++) {
        K += k_vec[j];
    }
    u1024_t total;
    memset(&total, 0, sizeof(total));
    uint32_t k_pref = 0U;
    uint32_t s_pref = 0U;
    for (uint32_t j = 0; j < m; j++) {
        k_pref += k_vec[j];
        u512_t diff_j = u512_sub(g_pow3_512[k_vec[j]], g_pow2_512[k_vec[j]]);
        u1024_t term_factor = u1024_mul_u512(g_pow3_512[K - k_pref], diff_j);
        u1024_t term = u1024_shl(term_factor, s_pref);
        total = u1024_add(total, term);
        s_pref += (k_vec[j] - 1U) + l_vec[j];
    }
    return total;
}

/* Direct step-by-step C(v) = sum_{i=0}^{K-1} 3^{K-1-i} * 2^{prefix_s_i} for self-test. */
static u1024_t step_by_step_numerator(uint32_t m, const uint32_t *k_vec, const uint32_t *l_vec) {
    uint32_t K = 0U;
    for (uint32_t j = 0; j < m; j++) {
        K += k_vec[j];
    }
    u1024_t total;
    memset(&total, 0, sizeof(total));
    uint32_t s_pref = 0U;
    uint32_t odd_idx = 0U;
    for (uint32_t j = 0; j < m; j++) {
        for (uint32_t r = 0; r < k_vec[j]; r++) {
            uint32_t exp_val = (r + 1U < k_vec[j]) ? 1U : l_vec[j];
            u1024_t term = u1024_shl(u1024_from_u512(g_pow3_512[K - 1U - odd_idx]), s_pref);
            total = u1024_add(total, term);
            s_pref += exp_val;
            odd_idx++;
        }
    }
    return total;
}

/* -------------------------------------------------------------------------- */
/* Canonical rotation symmetry & deterministic ordering                       */
/* -------------------------------------------------------------------------- */

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

static inline u256_t u256_from_ld_ceil(long double x) {
    if (x <= 4.0L) {
        return u256_from_u64(4ULL);
    }
    int exp2 = 0;
    long double mant = frexpl(x, &exp2);
    if (exp2 <= 63) {
        return u256_from_u64((uint64_t)ceill(x));
    }
    if (exp2 > 254) {
        u256_t maxv = {{UINT64_MAX, UINT64_MAX, UINT64_MAX, UINT64_MAX}};
        return maxv;
    }
    uint64_t top63 = (uint64_t)ldexpl(mant, 63);
    return u256_shl(u256_from_u64(top63 + 1ULL), (uint32_t)(exp2 - 63));
}

static inline u512_t u512_from_ld_ceil(long double x) {
    if (x <= 4.0L) {
        return u512_from_u64(4ULL);
    }
    int exp2 = 0;
    long double mant = frexpl(x, &exp2);
    if (exp2 <= 63) {
        return u512_from_u64((uint64_t)ceill(x));
    }
    if (exp2 > 510) {
        u512_t maxv = {{UINT64_MAX, UINT64_MAX, UINT64_MAX, UINT64_MAX,
                        UINT64_MAX, UINT64_MAX, UINT64_MAX, UINT64_MAX}};
        return maxv;
    }
    uint64_t top63 = (uint64_t)ldexpl(mant, 63);
    return u512_shl(u512_from_u64(top63 + 1ULL), (uint32_t)(exp2 - 63));
}

static inline long double near_bound_ld(const worker_ctx_t *ctx, uint32_t m, long double denom_ld) {
    return ctx->near_worst_dist[m] * denom_ld * (1.0L + 1e-12L) + 4.0L;
}

static inline u128 compute_near_thresh_u128(const worker_ctx_t *ctx, uint32_t m,
                                             u128 denom, long double denom_ld) {
    u128 half = denom >> 1;
    if (ctx->near_count[m] < TOP_NEAR_PER_M) {
        return half;
    }
    long double bound_ld = near_bound_ld(ctx, m, denom_ld);
    if (!isfinite(bound_ld) || bound_ld >= denom_ld * 0.5L) {
        return half;
    }
    if (bound_ld <= 4.0L) {
        return 4U;
    }
    int exp2 = 0;
    long double mant = frexpl(bound_ld, &exp2);
    if (exp2 <= 63) {
        return (u128)((uint64_t)ceill(bound_ld));
    }
    if (exp2 >= 127) {
        return half;
    }
    uint64_t top63 = (uint64_t)ldexpl(mant, 63);
    u128 t = ((u128)(top63 + 1ULL)) << (uint32_t)(exp2 - 63);
    return (t < half) ? t : half;
}

static inline u256_t compute_near_thresh_u256(const worker_ctx_t *ctx, uint32_t m,
                                               u256_t denom, long double denom_ld) {
    u256_t half = u256_shr1(denom);
    if (ctx->near_count[m] < TOP_NEAR_PER_M) {
        return half;
    }
    long double bound_ld = near_bound_ld(ctx, m, denom_ld);
    if (!isfinite(bound_ld) || bound_ld >= denom_ld * 0.5L) {
        return half;
    }
    u256_t t = u256_from_ld_ceil(bound_ld);
    return (u256_cmp(t, half) < 0) ? t : half;
}

static inline u512_t compute_near_thresh_u512(const worker_ctx_t *ctx, uint32_t m,
                                               u512_t denom, long double denom_ld) {
    u512_t half = u512_shr1(denom);
    if (ctx->near_count[m] < TOP_NEAR_PER_M) {
        return half;
    }
    long double bound_ld = near_bound_ld(ctx, m, denom_ld);
    if (!isfinite(bound_ld) || bound_ld >= denom_ld * 0.5L) {
        return half;
    }
    u512_t t = u512_from_ld_ceil(bound_ld);
    return (u512_cmp(t, half) < 0) ? t : half;
}

static void record_near_miss(worker_ctx_t *ctx, uint32_t m, uint32_t k, uint32_t s,
                             const uint32_t *kv, const uint32_t *lv,
                             u512_t denom, u512_t rem) {
    if (u512_cmp(denom, u512_from_u64(1ULL)) <= 0 || u512_is_zero(rem)) {
        return;
    }
    u512_t diff = u512_sub(denom, rem);
    u512_t dist_num = (u512_cmp(rem, diff) <= 0) ? rem : diff;
    long double dist_approx = u512_to_ld(dist_num) / u512_to_ld(denom);

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
        cnt++;
        ctx->near_count[m] = cnt;
        if (cnt == TOP_NEAR_PER_M) {
            size_t wi = 0U;
            for (size_t i = 1U; i < TOP_NEAR_PER_M; i++) {
                if (cmp_near_record(&arr[i], &arr[wi]) > 0) {
                    wi = i;
                }
            }
            ctx->near_worst_idx[m] = wi;
            ctx->near_worst_dist[m] = arr[wi].dist_approx;
        }
        return;
    }
    size_t worst_idx = ctx->near_worst_idx[m];
    if (cmp_near_record(&cand, &arr[worst_idx]) < 0) {
        arr[worst_idx] = cand;
        size_t wi = 0U;
        for (size_t i = 1U; i < TOP_NEAR_PER_M; i++) {
            if (cmp_near_record(&arr[i], &arr[wi]) > 0) {
                wi = i;
            }
        }
        ctx->near_worst_idx[m] = wi;
        ctx->near_worst_dist[m] = arr[wi].dist_approx;
    }
}

static void record_hit(worker_ctx_t *ctx, uint32_t m, uint32_t k, uint32_t s,
                       const uint32_t *kv, const uint32_t *lv, u512_t denom) {
    u1024_t c_exact = exact_mcircuit_numerator(m, kv, lv);
    u1024_t q;
    u512_t rem;
    u1024_divmod_u512(c_exact, denom, &q, &rem);
    if (!u512_is_zero(rem)) {
        return;
    }
    bool high_zero = true;
    for (size_t i = 1; i < 16; i++) {
        if (q.w[i] != 0ULL) {
            high_zero = false;
            break;
        }
    }
    bool is_triv = high_zero && (q.w[0] == 1ULL || q.w[0] == 2ULL || q.w[0] == 4ULL);
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

/* -------------------------------------------------------------------------- */
/* Instantiate u128, u256, and u512 solvers from shared `mcircuit_solver_impl.h` */
/* -------------------------------------------------------------------------- */

#define MC_T u128
#define MC_FN(x) x##_u128
#define MC_POW3(k) g_pow3_128[k]
#define MC_POW2(s) g_pow2_128[s]
#define MC_ADD(a, b, m) add_mod128((a), (b), (m))
#define MC_MUL(a, b, m) mul_mod128((a), (b), (m))
#define MC_SUB(a, b) ((a) - (b))
#define MC_MOD(a, m) ((a) % (m))
#define MC_IS_ZERO(a) ((a) == 0U)
#define MC_GT_ONE(a) ((a) > 1U)
#define MC_TO_LD(a) ((long double)(a))
#define MC_CMP(a, b) (((a) < (b)) ? -1 : (((a) > (b)) ? 1 : 0))
#define MC_NEAR_THRESH(ctx, m, denom, denom_ld) compute_near_thresh_u128((ctx), (m), (denom), (denom_ld))
#define MC_RECORD_HIT(ctx, m, k, s, kv, lv, denom) \
    record_hit((ctx), (m), (k), (s), (kv), (lv), u512_from_u128(denom))
#define MC_RECORD_NEAR(ctx, m, k, s, kv, lv, denom, rem) \
    record_near_miss((ctx), (m), (k), (s), (kv), (lv), u512_from_u128(denom), u512_from_u128(rem))
#include "mcircuit_solver_impl.h"
#undef MC_T
#undef MC_FN
#undef MC_POW3
#undef MC_POW2
#undef MC_ADD
#undef MC_MUL
#undef MC_SUB
#undef MC_MOD
#undef MC_IS_ZERO
#undef MC_GT_ONE
#undef MC_TO_LD
#undef MC_CMP
#undef MC_NEAR_THRESH
#undef MC_RECORD_HIT
#undef MC_RECORD_NEAR

#define MC_T u256_t
#define MC_FN(x) x##_u256
#define MC_POW3(k) g_pow3_256[k]
#define MC_POW2(s) g_pow2_256[s]
#define MC_ADD(a, b, m) u256_add_mod((a), (b), (m))
#define MC_MUL(a, b, m) u256_mul_mod((a), (b), (m))
#define MC_SUB(a, b) u256_sub((a), (b))
#define MC_MOD(a, m) u256_mod((a), (m))
#define MC_IS_ZERO(a) u256_is_zero(a)
#define MC_GT_ONE(a) (u256_cmp((a), u256_from_u64(1ULL)) > 0)
#define MC_TO_LD(a) u256_to_ld(a)
#define MC_CMP(a, b) u256_cmp((a), (b))
#define MC_NEAR_THRESH(ctx, m, denom, denom_ld) compute_near_thresh_u256((ctx), (m), (denom), (denom_ld))
#define MC_RECORD_HIT(ctx, m, k, s, kv, lv, denom) \
    record_hit((ctx), (m), (k), (s), (kv), (lv), u512_from_u256(denom))
#define MC_RECORD_NEAR(ctx, m, k, s, kv, lv, denom, rem) \
    record_near_miss((ctx), (m), (k), (s), (kv), (lv), u512_from_u256(denom), u512_from_u256(rem))
#include "mcircuit_solver_impl.h"
#undef MC_T
#undef MC_FN
#undef MC_POW3
#undef MC_POW2
#undef MC_ADD
#undef MC_MUL
#undef MC_SUB
#undef MC_MOD
#undef MC_IS_ZERO
#undef MC_GT_ONE
#undef MC_TO_LD
#undef MC_CMP
#undef MC_NEAR_THRESH
#undef MC_RECORD_HIT
#undef MC_RECORD_NEAR

#define MC_T u512_t
#define MC_FN(x) x##_u512
#define MC_POW3(k) g_pow3_512[k]
#define MC_POW2(s) g_pow2_512[s]
#define MC_ADD(a, b, m) u512_add_mod((a), (b), (m))
#define MC_MUL(a, b, m) u512_mul_mod((a), (b), (m))
#define MC_SUB(a, b) u512_sub((a), (b))
#define MC_MOD(a, m) u512_mod((a), (m))
#define MC_IS_ZERO(a) u512_is_zero(a)
#define MC_GT_ONE(a) (u512_cmp((a), u512_from_u64(1ULL)) > 0)
#define MC_TO_LD(a) u512_to_ld(a)
#define MC_CMP(a, b) u512_cmp((a), (b))
#define MC_NEAR_THRESH(ctx, m, denom, denom_ld) compute_near_thresh_u512((ctx), (m), (denom), (denom_ld))
#define MC_RECORD_HIT(ctx, m, k, s, kv, lv, denom) \
    record_hit((ctx), (m), (k), (s), (kv), (lv), (denom))
#define MC_RECORD_NEAR(ctx, m, k, s, kv, lv, denom, rem) \
    record_near_miss((ctx), (m), (k), (s), (kv), (lv), (denom), (rem))
#include "mcircuit_solver_impl.h"
#undef MC_T
#undef MC_FN
#undef MC_POW3
#undef MC_POW2
#undef MC_ADD
#undef MC_MUL
#undef MC_SUB
#undef MC_MOD
#undef MC_IS_ZERO
#undef MC_GT_ONE
#undef MC_TO_LD
#undef MC_CMP
#undef MC_NEAR_THRESH
#undef MC_RECORD_HIT
#undef MC_RECORD_NEAR

typedef void (*task_runner_fn)(worker_ctx_t *, const work_task_t *);

static void *worker_entry(void *arg) {
    static const task_runner_fn runners[3][MAX_M + 1] = {
        {NULL, NULL, run_task_m2_u128, run_task_m3_u128, run_task_m4_u128, run_task_m5_u128,
         run_task_m6_u128},
        {NULL, NULL, run_task_m2_u256, run_task_m3_u256, run_task_m4_u256, run_task_m5_u256,
         run_task_m6_u256},
        {NULL, NULL, run_task_m2_u512, run_task_m3_u512, run_task_m4_u512, run_task_m5_u512,
         run_task_m6_u512},
    };
    worker_ctx_t *ctx = (worker_ctx_t *)arg;
    for (size_t idx = ctx->thread_id; idx < ctx->task_count; idx += ctx->num_threads) {
        const work_task_t *t = &ctx->tasks[idx];
        uint32_t tier = ctx->min_tier;
        if (tier < 1U && (t->k > MAX_K_U128 || t->s > MAX_S_U128)) {
            tier = 1U;
        }
        if (tier < 2U && (t->k > MAX_K_U256 || t->s > MAX_S_U256)) {
            tier = 2U;
        }
        if (t->m >= 2U && t->m <= MAX_M && tier < 3U) {
            runners[tier][t->m](ctx, t);
        }
    }
    return NULL;
}

/* -------------------------------------------------------------------------- */
/* Internal C11 self-tests                                                    */
/* -------------------------------------------------------------------------- */

static int run_self_test(void) {
    /* 1. add_mod128 and mul_mod128 near 2^127 boundary */
    {
        u128 big_m = ((u128)1 << 127) - 1U;
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
    }

    /* 2. u256 and u512 modular arithmetic near 2^255-19, 2^256-189, 2^511-1, 2^512-569 */
    {
        u256_t p255 = {{UINT64_MAX - 18ULL, UINT64_MAX, UINT64_MAX, (1ULL << 63) - 1ULL}};
        u256_t a = u256_sub(p255, u256_from_u64(11ULL));
        u256_t b = u256_sub(p255, u256_from_u64(13ULL));
        if (u256_cmp(u256_add_mod(a, b, p255), u256_sub(p255, u256_from_u64(24ULL))) != 0 ||
            u256_cmp(u256_mul_mod(a, b, p255), u256_from_u64(143ULL)) != 0) {
            fprintf(stderr, "FAIL: u256 mod near 2^255-19\n");
            return 1;
        }

        u256_t p256 = {{UINT64_MAX - 188ULL, UINT64_MAX, UINT64_MAX, UINT64_MAX}};
        u256_t x = u256_sub(p256, u256_from_u64(9ULL));
        u256_t y = u256_sub(p256, u256_from_u64(17ULL));
        if (u256_cmp(u256_add_mod(x, y, p256), u256_sub(p256, u256_from_u64(26ULL))) != 0 ||
            u256_cmp(u256_mul_mod(x, y, p256), u256_from_u64(153ULL)) != 0) {
            fprintf(stderr, "FAIL: u256 mod near 2^256-189\n");
            return 1;
        }

        u512_t p511 = {{UINT64_MAX, UINT64_MAX, UINT64_MAX, UINT64_MAX,
                        UINT64_MAX, UINT64_MAX, UINT64_MAX, (1ULL << 63) - 1ULL}};
        u512_t u = u512_sub(p511, u512_from_u64(19ULL));
        u512_t v = u512_sub(p511, u512_from_u64(23ULL));
        if (u512_cmp(u512_add_mod(u, v, p511), u512_sub(p511, u512_from_u64(42ULL))) != 0 ||
            u512_cmp(u512_mul_mod(u, v, p511), u512_from_u64(437ULL)) != 0) {
            fprintf(stderr, "FAIL: u512 mod near 2^511-1\n");
            return 1;
        }

        u512_t p512 = {{UINT64_MAX - 568ULL, UINT64_MAX, UINT64_MAX, UINT64_MAX,
                        UINT64_MAX, UINT64_MAX, UINT64_MAX, UINT64_MAX}};
        u512_t p = u512_sub(p512, u512_from_u64(31ULL));
        u512_t q = u512_sub(p512, u512_from_u64(37ULL));
        if (u512_cmp(u512_add_mod(p, q, p512), u512_sub(p512, u512_from_u64(68ULL))) != 0 ||
            u512_cmp(u512_mul_mod(p, q, p512), u512_from_u64(1147ULL)) != 0) {
            fprintf(stderr, "FAIL: u512 mod near 2^512-569\n");
            return 1;
        }
    }

    /* 3. Closed-form m-circuit numerator identity vs step-by-step C(v) on m = 1..6 */
    {
        const uint32_t k1[1] = {5}, l1[1] = {4};
        if (u1024_cmp(exact_mcircuit_numerator(1, k1, l1), step_by_step_numerator(1, k1, l1)) != 0) {
            fprintf(stderr, "FAIL: 1-circuit closed-form vs step-by-step\n");
            return 1;
        }
        const uint32_t k2[2] = {120, 120}, l2[2] = {72, 71};
        if (u1024_cmp(exact_mcircuit_numerator(2, k2, l2), step_by_step_numerator(2, k2, l2)) != 0) {
            fprintf(stderr, "FAIL: 2-circuit K=240 closed-form vs step-by-step\n");
            return 1;
        }
        const uint32_t k3[3] = {2, 5, 3}, l3[3] = {3, 2, 4};
        if (u1024_cmp(exact_mcircuit_numerator(3, k3, l3), step_by_step_numerator(3, k3, l3)) != 0) {
            fprintf(stderr, "FAIL: 3-circuit closed-form vs step-by-step\n");
            return 1;
        }
        const uint32_t k4[4] = {1, 3, 2, 4}, l4[4] = {2, 5, 2, 3};
        if (u1024_cmp(exact_mcircuit_numerator(4, k4, l4), step_by_step_numerator(4, k4, l4)) != 0) {
            fprintf(stderr, "FAIL: 4-circuit closed-form vs step-by-step\n");
            return 1;
        }
        const uint32_t k5[5] = {10, 22, 18, 25, 25}, l5[5] = {7, 15, 11, 16, 15};
        if (u1024_cmp(exact_mcircuit_numerator(5, k5, l5), step_by_step_numerator(5, k5, l5)) != 0) {
            fprintf(stderr, "FAIL: 5-circuit K=100 closed-form vs step-by-step\n");
            return 1;
        }
        const uint32_t k6[6] = {12, 20, 18, 22, 24, 24}, l6[6] = {9, 14, 10, 13, 15, 16};
        if (u1024_cmp(exact_mcircuit_numerator(6, k6, l6), step_by_step_numerator(6, k6, l6)) != 0) {
            fprintf(stderr, "FAIL: 6-circuit K=120 closed-form vs step-by-step\n");
            return 1;
        }
    }

    /* 4. Trivial (n=1 for m=1,6) and negative 3n+1 (n=-17 for m=2,6) cycle recovery */
    {
        const uint32_t kv1[1] = {1}, lv1[1] = {2};
        u1024_t c1 = exact_mcircuit_numerator(1U, kv1, lv1);
        u512_t d1 = u512_sub(g_pow2_512[2], g_pow3_512[1]);
        u1024_t q1;
        u512_t r1;
        u1024_divmod_u512(c1, d1, &q1, &r1);
        if (!u512_is_zero(r1) || q1.w[0] != 1ULL || q1.w[1] != 0ULL) {
            fprintf(stderr, "FAIL: trivial 1-circuit detection (expected n=1)\n");
            return 1;
        }

        const uint32_t kv6t[6] = {1, 1, 1, 1, 1, 1}, lv6t[6] = {2, 2, 2, 2, 2, 2};
        u1024_t c6t = exact_mcircuit_numerator(6U, kv6t, lv6t);
        u512_t d6t = u512_sub(g_pow2_512[12], g_pow3_512[6]);
        worker_ctx_t hit_ctx;
        memset(&hit_ctx, 0, sizeof(hit_ctx));
        record_hit(&hit_ctx, 6U, 6U, 12U, kv6t, lv6t, d6t);
        if (hit_ctx.hit_count != 1U || !hit_ctx.hits[0].is_trivial || hit_ctx.hits[0].n_cand.w[0] != 1ULL) {
            fprintf(stderr, "FAIL: trivial 6-circuit filtering (expected is_trivial=true, n=1)\n");
            return 1;
        }
        (void)c6t;

        const uint32_t kv2[2] = {4, 3}, lv2[2] = {2, 4};
        u1024_t c2 = exact_mcircuit_numerator(2U, kv2, lv2);
        u512_t d2 = u512_sub(g_pow3_512[7], g_pow2_512[11]); /* 2187 - 2048 = 139 */
        u1024_t q2;
        u512_t r2;
        u1024_divmod_u512(c2, d2, &q2, &r2);
        if (d2.w[0] != 139ULL || !u512_is_zero(r2) || q2.w[0] != 17ULL || q2.w[1] != 0ULL) {
            fprintf(stderr, "FAIL: negative 2-circuit -17 detection\n");
            return 1;
        }

        /* 3x concatenated -17 cycle gives an m=6 circuit (K=21, S=33) with C(v)/(3^21 - 2^33) == 17 */
        const uint32_t kv6n[6] = {4, 3, 4, 3, 4, 3}, lv6n[6] = {2, 4, 2, 4, 2, 4};
        u1024_t c6n = exact_mcircuit_numerator(6U, kv6n, lv6n);
        u512_t d6n = u512_sub(g_pow3_512[21], g_pow2_512[33]);
        u1024_t q6n;
        u512_t r6n;
        u1024_divmod_u512(c6n, d6n, &q6n, &r6n);
        if (!u512_is_zero(r6n) || q6n.w[0] != 17ULL || q6n.w[1] != 0ULL) {
            fprintf(stderr, "FAIL: negative 6-circuit -17 detection\n");
            return 1;
        }
    }

    /* 5. High-K checks: K=80/S=127 (u128), K=100/S=159 (u256), K=160/S=254 (u256), K=240/S=381 (u512) vs u1024 */
    {
        const uint32_t kv80[2] = {40, 40}, lv80[2] = {25, 24};
        u512_t d80_512 = u512_sub(g_pow2_512[127], g_pow3_512[80]);
        u1024_t c80 = exact_mcircuit_numerator(2U, kv80, lv80);
        u1024_t q80;
        u512_t rem80_exact;
        u1024_divmod_u512(c80, d80_512, &q80, &rem80_exact);

        u128 d80 = g_pow2_128[127] - g_pow3_128[80];
        u128 c0_80 = (g_pow3_128[40] - g_pow2_128[40]) % d80;
        u128 rem80_fast = add_mod128(mul_mod128(g_pow3_128[40] % d80, c0_80, d80),
                                     mul_mod128(g_pow2_128[64] % d80, c0_80, d80), d80);
        if (u512_cmp(rem80_exact, u512_from_u128(rem80_fast)) != 0) {
            fprintf(stderr, "FAIL: K=80, S=127 u128 vs exact u1024 mismatch\n");
            return 1;
        }

        const uint32_t kv100[3] = {30, 35, 35}, lv100[3] = {20, 21, 21};
        u256_t d100 = u256_sub(g_pow2_256[159], g_pow3_256[100]);
        u1024_t c100 = exact_mcircuit_numerator(3U, kv100, lv100);
        u1024_t q100;
        u512_t rem100_exact;
        u1024_divmod_u512(c100, u512_from_u256(d100), &q100, &rem100_exact);
        u256_t c100_0 = u256_mod(u256_sub(g_pow3_256[30], g_pow2_256[30]), d100);
        u256_t c100_1 = u256_mod(u256_sub(g_pow3_256[35], g_pow2_256[35]), d100);
        u256_t t0 = u256_mul_mod(u256_mod(g_pow3_256[70], d100), c100_0, d100);
        u256_t t1 = u256_mul_mod(u256_mod(g_pow2_256[49], d100),
                                 u256_mul_mod(u256_mod(g_pow3_256[35], d100), c100_1, d100), d100);
        u256_t t2 = u256_mul_mod(u256_mod(g_pow2_256[104], d100), c100_1, d100);
        u256_t rem100_fast = u256_add_mod(u256_add_mod(t0, t1, d100), t2, d100);
        if (u512_cmp(rem100_exact, u512_from_u256(rem100_fast)) != 0) {
            fprintf(stderr, "FAIL: K=100, S=159 u256 vs exact u1024 mismatch\n");
            return 1;
        }

        const uint32_t kv160[2] = {80, 80}, lv160[2] = {48, 48};
        u256_t d160 = u256_sub(g_pow2_256[254], g_pow3_256[160]);
        u1024_t c160 = exact_mcircuit_numerator(2U, kv160, lv160);
        u1024_t q160;
        u512_t rem160_exact;
        u1024_divmod_u512(c160, u512_from_u256(d160), &q160, &rem160_exact);
        u256_t c160_0 = u256_mod(u256_sub(g_pow3_256[80], g_pow2_256[80]), d160);
        u256_t u0 = u256_mul_mod(u256_mod(g_pow3_256[80], d160), c160_0, d160);
        u256_t u1 = u256_mul_mod(u256_mod(g_pow2_256[127], d160), c160_0, d160);
        u256_t rem160_fast = u256_add_mod(u0, u1, d160);
        if (u512_cmp(rem160_exact, u512_from_u256(rem160_fast)) != 0) {
            fprintf(stderr, "FAIL: K=160, S=254 u256 vs exact u1024 mismatch\n");
            return 1;
        }

        /* K=240, S=381, m=2: k=[120, 120], l=[72, 71] (S = 119+72 + 119+71 = 381) */
        const uint32_t kv240[2] = {120, 120}, lv240[2] = {72, 71};
        u512_t d240 = u512_sub(g_pow2_512[381], g_pow3_512[240]);
        u1024_t c240 = exact_mcircuit_numerator(2U, kv240, lv240);
        u1024_t q240;
        u512_t rem240_exact;
        u1024_divmod_u512(c240, d240, &q240, &rem240_exact);
        u512_t c240_0 = u512_mod(u512_sub(g_pow3_512[120], g_pow2_512[120]), d240);
        u512_t v0 = u512_mul_mod(u512_mod(g_pow3_512[120], d240), c240_0, d240);
        u512_t v1 = u512_mul_mod(u512_mod(g_pow2_512[191], d240), c240_0, d240);
        u512_t rem240_fast = u512_add_mod(v0, v1, d240);
        if (u512_cmp(rem240_exact, rem240_fast) != 0) {
            fprintf(stderr, "FAIL: K=240, S=381 u512 vs exact u1024 mismatch\n");
            return 1;
        }
    }

    /* 6. Direct u128 vs u256 vs u512 task-runner equivalence on m=5 (K=12,S=20) & m=6 (K=13,S=22) */
    {
        const work_task_t tasks[2] = {
            {5U, 12U, 20U, 1U, 2U},
            {6U, 13U, 22U, 1U, 2U},
        };
        for (size_t ti = 0; ti < 2; ti++) {
            uint32_t m = tasks[ti].m;
            worker_ctx_t ctx128, ctx256, ctx512;
            memset(&ctx128, 0, sizeof(ctx128));
            memset(&ctx256, 0, sizeof(ctx256));
            memset(&ctx512, 0, sizeof(ctx512));
            if (m == 5U) {
                run_task_m5_u128(&ctx128, &tasks[ti]);
                run_task_m5_u256(&ctx256, &tasks[ti]);
                run_task_m5_u512(&ctx512, &tasks[ti]);
            } else {
                run_task_m6_u128(&ctx128, &tasks[ti]);
                run_task_m6_u256(&ctx256, &tasks[ti]);
                run_task_m6_u512(&ctx512, &tasks[ti]);
            }
            if (ctx128.tested[m] == 0ULL || ctx128.tested[m] != ctx256.tested[m] ||
                ctx128.tested[m] != ctx512.tested[m] ||
                ctx128.near_count[m] != ctx256.near_count[m] ||
                ctx128.near_count[m] != ctx512.near_count[m]) {
                fprintf(stderr, "FAIL: m=%u u128 vs u256 vs u512 count mismatch\n", m);
                return 1;
            }
            for (size_t i = 0; i < ctx128.near_count[m]; i++) {
                if (u512_cmp(ctx128.near[m][i].dist_num, ctx256.near[m][i].dist_num) != 0 ||
                    u512_cmp(ctx128.near[m][i].dist_num, ctx512.near[m][i].dist_num) != 0) {
                    fprintf(stderr, "FAIL: m=%u u128 vs u256 vs u512 near-miss mismatch\n", m);
                    return 1;
                }
            }
        }
    }

    printf("[OK] mcircuit_hunter C11 self-test: mod128/256/512, closed-form m=1..6, n=1/-17, K=80/100/160/240 passed\n");
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

static bool push_task(work_task_t **tasks, size_t *count, size_t *cap, work_task_t item) {
    if (*count == *cap) {
        size_t new_cap = (*cap) * 2U;
        work_task_t *tmp = realloc(*tasks, new_cap * sizeof(work_task_t));
        if (!tmp) {
            return false;
        }
        *tasks = tmp;
        *cap = new_cap;
    }
    (*tasks)[(*count)++] = item;
    return true;
}

int main(int argc, char **argv) {
    init_tables();

    uint32_t k_max[MAX_M + 1] = {0, 0, 240, 120, 70, 44, 32};
    uint32_t threads = 4U;
    bound_mode_t bound_mode = BOUND_SIMONS;
    bool self_test = false;
    uint32_t min_tier = 0U;
    const char *json_out = NULL;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--self-test") == 0) {
            self_test = true;
        } else if (strcmp(argv[i], "--force-u256") == 0) {
            if (min_tier < 1U) {
                min_tier = 1U;
            }
        } else if (strcmp(argv[i], "--force-u512") == 0) {
            min_tier = 2U;
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
        } else if (strcmp(argv[i], "--k5-max") == 0 && i + 1 < argc) {
            if (!parse_u32(argv[++i], &k_max[5])) {
                fprintf(stderr, "Invalid --k5-max\n");
                return 2;
            }
        } else if (strcmp(argv[i], "--k6-max") == 0 && i + 1 < argc) {
            if (!parse_u32(argv[++i], &k_max[6])) {
                fprintf(stderr, "Invalid --k6-max\n");
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
                    "Usage: %s [--self-test] [--force-u256] [--force-u512] [--k2-max K] "
                    "[--k3-max K] [--k4-max K] [--k5-max K] [--k6-max K] "
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

    for (uint32_t m = 2U; m <= MAX_M; m++) {
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
                        if (!push_task(&tasks, &task_count, &task_cap,
                                       (work_task_t){m, k, s, k0, 0U})) {
                            free(tasks);
                            return 1;
                        }
                    }
                } else {
                    for (uint32_t k0 = 1U; k0 <= k / m; k0++) {
                        for (uint32_t k1 = k0; k1 <= k - (m - 1U) * k0; k1++) {
                            if (!push_task(&tasks, &task_count, &task_cap,
                                           (work_task_t){m, k, s, k0, k1})) {
                                free(tasks);
                                return 1;
                            }
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
        ctxs[t].min_tier = min_tier;
    }

    if (active_threads == 1U) {
        worker_entry(&ctxs[0]);
    } else {
        uint32_t spawned = 0U;
        bool thread_err = false;
        for (uint32_t t = 0; t < active_threads; t++) {
            int rc = pthread_create(&tids[t], NULL, worker_entry, &ctxs[t]);
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
            free(tasks);
            free(ctxs);
            free(tids);
            return 1;
        }
    }

    /* Deterministic merge across workers */
    uint64_t total_tested_m[MAX_M + 1] = {0};
    uint64_t total_tested_all = 0ULL;
    uint64_t total_skips_all = 0ULL;
    for (uint32_t m = 2U; m <= MAX_M; m++) {
        total_skips_all += guard_skips[m];
    }

    size_t all_hits_cap = 0U;
    for (uint32_t t = 0; t < active_threads; t++) {
        for (uint32_t m = 2U; m <= MAX_M; m++) {
            total_tested_m[m] += ctxs[t].tested[m];
        }
        all_hits_cap += ctxs[t].hit_count;
    }
    for (uint32_t m = 2U; m <= MAX_M; m++) {
        total_tested_all += total_tested_m[m];
    }

    hit_record_t *all_hits = all_hits_cap ? malloc(all_hits_cap * sizeof(hit_record_t)) : NULL;
    if (all_hits_cap && !all_hits) {
        free(tasks);
        free(ctxs);
        free(tids);
        return 1;
    }
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

    for (uint32_t m = 2U; m <= MAX_M; m++) {
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
    if (!isfinite(elapsed) || elapsed < 0.0) {
        elapsed = 0.0;
    }

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
    fprintf(fp, "    \"schema\": \"solve-collatz-mcircuit-hunter/v3\",\n");
    fprintf(fp, "    \"engine\": \"mcircuit_hunter.c\",\n");
    fprintf(fp, "    \"bound_mode\": \"%s\",\n", bound_name);
    fprintf(fp, "    \"k_limit_u128\": %u,\n", MAX_K_U128);
    fprintf(fp, "    \"s_limit_u128\": %u,\n", MAX_S_U128);
    fprintf(fp, "    \"k_limit_u256\": %u,\n", MAX_K_U256);
    fprintf(fp, "    \"s_limit_u256\": %u,\n", MAX_S_U256);
    fprintf(fp, "    \"k_limit_u512\": %u,\n", MAX_K_LIMIT);
    fprintf(fp, "    \"s_limit_u512\": %u,\n", MAX_S_LIMIT);
    fprintf(fp, "    \"overflow_guard_skips\": %" PRIu64 ",\n", total_skips_all);
    fprintf(fp, "    \"total_candidates_tested\": %" PRIu64 ",\n", total_tested_all);
    fprintf(fp, "    \"total_hits\": %zu,\n", nontrivial_hits);
    fprintf(fp, "    \"families\": [\n");
    for (uint32_t m = 2U; m <= MAX_M; m++) {
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
            fprintf(fp, "        \"s_rule\": \"S_min(K) <= S <= floor(K*log2(10/3)) via 3^K*2^S <= 10^K (S <= %u)\",\n",
                    MAX_S_LIMIT);
        } else {
            fprintf(fp, "        \"s_rule\": \"S_min(K) <= S < K*log2(3) + %u*log2(4/3) via 2^S*3^%u < 4^%u*3^K (S <= %u)\",\n",
                    m, m, m, MAX_S_LIMIT);
        }
        fprintf(fp, "        \"candidates_tested\": %" PRIu64 ",\n", total_tested_m[m]);
        fprintf(fp, "        \"overflow_guard_skips\": %" PRIu64 ",\n", guard_skips[m]);
        fprintf(fp, "        \"hits_found\": %zu,\n", fam_hits);
        fprintf(fp, "        \"near_misses\": [\n");
        for (size_t i = 0; i < merged_near_count[m]; i++) {
            const candidate_record_t *nr = &merged_near[m][i];
            char d_buf[192], r_buf[192], dn_buf[192];
            u512_to_str(nr->denom, d_buf, sizeof(d_buf));
            u512_to_str(nr->rem, r_buf, sizeof(r_buf));
            u512_to_str(nr->dist_num, dn_buf, sizeof(dn_buf));
            double da = isfinite((double)nr->dist_approx) ? (double)nr->dist_approx : 0.0;
            fprintf(fp, "          {\"m\": %u, \"k\": %u, \"s\": %u, \"k_vec\": ", nr->m, nr->k, nr->s);
            print_u32_vec(fp, nr->k_vec, nr->m);
            fprintf(fp, ", \"l_vec\": ");
            print_u32_vec(fp, nr->l_vec, nr->m);
            fprintf(fp, ", \"denom\": \"%s\", \"rem\": \"%s\", \"dist_num\": \"%s\", \"dist_approx\": %.12e}%s\n",
                    d_buf, r_buf, dn_buf, da, (i + 1U < merged_near_count[m]) ? "," : "");
        }
        fprintf(fp, "        ]\n");
        fprintf(fp, "      }%s\n", (m < MAX_M) ? "," : "");
    }
    fprintf(fp, "    ],\n");
    fprintf(fp, "    \"hits\": [\n");
    size_t printed_hits = 0U;
    for (size_t i = 0; i < all_hits_count; i++) {
        const hit_record_t *h = &all_hits[i];
        if (h->is_trivial) {
            continue;
        }
        char d_buf[192], n_buf[360];
        u512_to_str(h->denom, d_buf, sizeof(d_buf));
        u1024_to_str(h->n_cand, n_buf, sizeof(n_buf));
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
    fprintf(fp, "    \"force_u256\": %s,\n", (min_tier >= 1U) ? "true" : "false");
    fprintf(fp, "    \"force_u512\": %s,\n", (min_tier >= 2U) ? "true" : "false");
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
