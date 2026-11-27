/*
 * mcircuit_solver_impl.h — Type-parameterized canonical m-circuit solvers (m = 2, 3, 4, 5, 6).
 *
 * Included three times by `mcircuit_hunter.c`:
 *   1. With `MC_T = u128` (`MC_FN(x) = x##_u128`) for `K <= 80, S <= 127`.
 *   2. With `MC_T = u256_t` (`MC_FN(x) = x##_u256`) for `K <= 160, S <= 255` (and `--force-u256`).
 *   3. With `MC_T = u512_t` (`MC_FN(x) = x##_u512`) for `K <= 256, S <= 511` (and `--force-u512`).
 */

static void MC_FN(eval_candidate)(worker_ctx_t *ctx, uint32_t m, uint32_t k, uint32_t s,
                                    const uint32_t *kv, const uint32_t *lv,
                                    MC_T denom, long double denom_ld,
                                    MC_T base, MC_T term_last, MC_T *thresh) {
    MC_T rem = MC_ADD(base, term_last, denom);
    ctx->tested[m]++;
    if (MC_IS_ZERO(rem)) {
        MC_RECORD_HIT(ctx, m, k, s, kv, lv, denom);
        return;
    }
    if (MC_GT_ONE(denom)) {
        MC_T diff = MC_SUB(denom, rem);
        MC_T dist_num = (MC_CMP(rem, diff) <= 0) ? rem : diff;
        if (MC_CMP(dist_num, *thresh) <= 0) {
            MC_RECORD_NEAR(ctx, m, k, s, kv, lv, denom, rem);
            *thresh = MC_NEAR_THRESH(ctx, m, denom, denom_ld);
        }
    }
}

static void MC_FN(run_task_m2)(worker_ctx_t *ctx, const work_task_t *t) {
    uint32_t k = t->k;
    uint32_t s = t->s;
    uint32_t k0 = t->k0;
    uint32_t k1 = k - k0;
    uint32_t rem_l = s - k + 2U;
    if (rem_l < 4U) {
        return;
    }

    MC_T denom = MC_SUB(MC_POW2(s), MC_POW3(k));
    long double denom_ld = MC_TO_LD(denom);
    MC_T thresh = MC_NEAR_THRESH(ctx, 2U, denom, denom_ld);

    MC_T c0_mod = MC_MOD(MC_SUB(MC_POW3(k0), MC_POW2(k0)), denom);
    MC_T c1_mod = MC_MOD(MC_SUB(MC_POW3(k1), MC_POW2(k1)), denom);
    MC_T base0 = MC_MUL(MC_MOD(MC_POW3(k1), denom), c0_mod, denom);

    uint32_t l0_max = rem_l - 2U;
    if (k0 == k1 && rem_l / 2U < l0_max) {
        l0_max = rem_l / 2U;
    }
    if (l0_max < 2U) {
        return;
    }

    uint32_t s0_start = (k0 - 1U) + 2U;
    MC_T term1 = MC_MUL(MC_MOD(MC_POW2(s0_start), denom), c1_mod, denom);

    uint32_t kv[MAX_M] = {0};
    uint32_t lv[MAX_M] = {0};
    kv[0] = k0;
    kv[1] = k1;

    for (uint32_t l0 = 2U; l0 <= l0_max; l0++) {
        lv[0] = l0;
        lv[1] = rem_l - l0;
        MC_FN(eval_candidate)(ctx, 2U, k, s, kv, lv, denom, denom_ld, base0, term1, &thresh);
        term1 = MC_ADD(term1, term1, denom);
    }
}

static void MC_FN(run_task_m3)(worker_ctx_t *ctx, const work_task_t *t) {
    uint32_t k = t->k;
    uint32_t s = t->s;
    uint32_t k0 = t->k0;
    uint32_t rem_l = s - k + 3U;
    if (rem_l < 6U) {
        return;
    }

    MC_T denom = MC_SUB(MC_POW2(s), MC_POW3(k));
    long double denom_ld = MC_TO_LD(denom);
    MC_T thresh = MC_NEAR_THRESH(ctx, 3U, denom, denom_ld);
    MC_T c0_mod = MC_MOD(MC_SUB(MC_POW3(k0), MC_POW2(k0)), denom);

    uint32_t kv[MAX_M] = {0};
    uint32_t lv[MAX_M] = {0};
    kv[0] = k0;

    for (uint32_t k1 = k0; k1 <= k - 2U * k0; k1++) {
        uint32_t k2 = k - k0 - k1;
        if (k2 < k0) {
            continue;
        }
        kv[1] = k1;
        kv[2] = k2;

        uint32_t c_eq = 1U + (k1 == k0 ? 1U : 0U) + (k2 == k0 ? 1U : 0U);
        if (rem_l < 2U * 3U) {
            continue;
        }
        uint32_t l0_max = (rem_l - 2U * (3U - c_eq)) / c_eq;
        if (l0_max < 2U) {
            continue;
        }

        MC_T c1_mod = MC_MOD(MC_SUB(MC_POW3(k1), MC_POW2(k1)), denom);
        MC_T c2_mod = MC_MOD(MC_SUB(MC_POW3(k2), MC_POW2(k2)), denom);
        MC_T base0 = MC_MUL(MC_MOD(MC_POW3(k1 + k2), denom), c0_mod, denom);
        MC_T p3_k2_c1 = MC_MUL(MC_MOD(MC_POW3(k2), denom), c1_mod, denom);
        MC_T term1 = MC_MUL(MC_MOD(MC_POW2(k0 + 1U), denom), p3_k2_c1, denom);

        for (uint32_t l0 = 2U; l0 <= l0_max; l0++) {
            uint32_t s0 = (k0 - 1U) + l0;
            MC_T base1 = MC_ADD(base0, term1, denom);

            uint32_t l1_start = (k1 == k0) ? l0 : 2U;
            uint32_t min_l2 = (k2 == k0) ? l0 : 2U;
            uint32_t l1_max = rem_l - l0 - min_l2;
            if (l1_start <= l1_max) {
                uint32_t s01_start = s0 + (k1 - 1U) + l1_start;
                MC_T term2 = MC_MUL(MC_MOD(MC_POW2(s01_start), denom), c2_mod, denom);

                lv[0] = l0;
                for (uint32_t l1 = l1_start; l1 <= l1_max; l1++) {
                    lv[1] = l1;
                    lv[2] = rem_l - l0 - l1;
                    if (c_eq == 1U || is_canonical_m(3U, kv, lv)) {
                        MC_FN(eval_candidate)(ctx, 3U, k, s, kv, lv, denom, denom_ld,
                                              base1, term2, &thresh);
                    }
                    term2 = MC_ADD(term2, term2, denom);
                }
            }
            term1 = MC_ADD(term1, term1, denom);
        }
    }
}

static void MC_FN(run_task_m4)(worker_ctx_t *ctx, const work_task_t *t) {
    uint32_t k = t->k;
    uint32_t s = t->s;
    uint32_t k0 = t->k0;
    uint32_t k1 = t->k1;
    uint32_t rem_l = s - k + 4U;
    if (rem_l < 8U) {
        return;
    }

    MC_T denom = MC_SUB(MC_POW2(s), MC_POW3(k));
    long double denom_ld = MC_TO_LD(denom);
    MC_T thresh = MC_NEAR_THRESH(ctx, 4U, denom, denom_ld);
    MC_T c0_mod = MC_MOD(MC_SUB(MC_POW3(k0), MC_POW2(k0)), denom);
    MC_T c1_mod = MC_MOD(MC_SUB(MC_POW3(k1), MC_POW2(k1)), denom);

    uint32_t kv[MAX_M] = {0};
    uint32_t lv[MAX_M] = {0};
    kv[0] = k0;
    kv[1] = k1;

    for (uint32_t k2 = k0; k2 <= k - 2U * k0 - k1; k2++) {
        uint32_t k3 = k - k0 - k1 - k2;
        if (k3 < k0) {
            continue;
        }
        kv[2] = k2;
        kv[3] = k3;

        uint32_t c_eq = 1U + (k1 == k0 ? 1U : 0U) + (k2 == k0 ? 1U : 0U) + (k3 == k0 ? 1U : 0U);
        uint32_t l0_max = (rem_l - 2U * (4U - c_eq)) / c_eq;
        if (l0_max < 2U) {
            continue;
        }

        MC_T c2_mod = MC_MOD(MC_SUB(MC_POW3(k2), MC_POW2(k2)), denom);
        MC_T c3_mod = MC_MOD(MC_SUB(MC_POW3(k3), MC_POW2(k3)), denom);
        MC_T base0 = MC_MUL(MC_MOD(MC_POW3(k1 + k2 + k3), denom), c0_mod, denom);
        MC_T p3_23_c1 = MC_MUL(MC_MOD(MC_POW3(k2 + k3), denom), c1_mod, denom);
        MC_T p3_3_c2 = MC_MUL(MC_MOD(MC_POW3(k3), denom), c2_mod, denom);
        MC_T term1 = MC_MUL(MC_MOD(MC_POW2(k0 + 1U), denom), p3_23_c1, denom);

        for (uint32_t l0 = 2U; l0 <= l0_max; l0++) {
            uint32_t s0 = (k0 - 1U) + l0;
            MC_T base1 = MC_ADD(base0, term1, denom);

            uint32_t l1_start = (k1 == k0) ? l0 : 2U;
            uint32_t min_l2 = (k2 == k0) ? l0 : 2U;
            uint32_t min_l3 = (k3 == k0) ? l0 : 2U;
            uint32_t l1_max = rem_l - l0 - min_l2 - min_l3;
            if (l1_start <= l1_max) {
                uint32_t s01_start = s0 + (k1 - 1U) + l1_start;
                MC_T term2 = MC_MUL(MC_MOD(MC_POW2(s01_start), denom), p3_3_c2, denom);

                lv[0] = l0;
                for (uint32_t l1 = l1_start; l1 <= l1_max; l1++) {
                    MC_T base2 = MC_ADD(base1, term2, denom);
                    uint32_t s01 = s0 + (k1 - 1U) + l1;
                    uint32_t l2_max = rem_l - l0 - l1 - min_l3;
                    if (min_l2 <= l2_max) {
                        uint32_t s012_start = s01 + (k2 - 1U) + min_l2;
                        MC_T term3 = MC_MUL(MC_MOD(MC_POW2(s012_start), denom), c3_mod, denom);
                        lv[1] = l1;
                        for (uint32_t l2 = min_l2; l2 <= l2_max; l2++) {
                            lv[2] = l2;
                            lv[3] = rem_l - l0 - l1 - l2;
                            if (c_eq == 1U || is_canonical_m(4U, kv, lv)) {
                                MC_FN(eval_candidate)(ctx, 4U, k, s, kv, lv, denom, denom_ld,
                                                      base2, term3, &thresh);
                            }
                            term3 = MC_ADD(term3, term3, denom);
                        }
                    }
                    term2 = MC_ADD(term2, term2, denom);
                }
            }
            term1 = MC_ADD(term1, term1, denom);
        }
    }
}

static void MC_FN(run_task_m5)(worker_ctx_t *ctx, const work_task_t *t) {
    uint32_t k = t->k;
    uint32_t s = t->s;
    uint32_t k0 = t->k0;
    uint32_t k1 = t->k1;
    uint32_t rem_l = s - k + 5U;
    if (rem_l < 10U) {
        return;
    }

    MC_T denom = MC_SUB(MC_POW2(s), MC_POW3(k));
    long double denom_ld = MC_TO_LD(denom);
    MC_T thresh = MC_NEAR_THRESH(ctx, 5U, denom, denom_ld);
    MC_T c0_mod = MC_MOD(MC_SUB(MC_POW3(k0), MC_POW2(k0)), denom);
    MC_T c1_mod = MC_MOD(MC_SUB(MC_POW3(k1), MC_POW2(k1)), denom);

    uint32_t kv[MAX_M] = {0};
    uint32_t lv[MAX_M] = {0};
    kv[0] = k0;
    kv[1] = k1;

    for (uint32_t k2 = k0; k2 <= k - 3U * k0 - k1; k2++) {
        kv[2] = k2;
        MC_T c2_mod = MC_MOD(MC_SUB(MC_POW3(k2), MC_POW2(k2)), denom);

        for (uint32_t k3 = k0; k3 <= k - 2U * k0 - k1 - k2; k3++) {
            uint32_t k4 = k - k0 - k1 - k2 - k3;
            if (k4 < k0) {
                continue;
            }
            kv[3] = k3;
            kv[4] = k4;

            uint32_t c_eq = 1U + (k1 == k0 ? 1U : 0U) + (k2 == k0 ? 1U : 0U) +
                            (k3 == k0 ? 1U : 0U) + (k4 == k0 ? 1U : 0U);
            uint32_t l0_max = (rem_l - 2U * (5U - c_eq)) / c_eq;
            if (l0_max < 2U) {
                continue;
            }

            MC_T c3_mod = MC_MOD(MC_SUB(MC_POW3(k3), MC_POW2(k3)), denom);
            MC_T c4_mod = MC_MOD(MC_SUB(MC_POW3(k4), MC_POW2(k4)), denom);
            MC_T base0 = MC_MUL(MC_MOD(MC_POW3(k1 + k2 + k3 + k4), denom), c0_mod, denom);
            MC_T p3_234_c1 = MC_MUL(MC_MOD(MC_POW3(k2 + k3 + k4), denom), c1_mod, denom);
            MC_T p3_34_c2 = MC_MUL(MC_MOD(MC_POW3(k3 + k4), denom), c2_mod, denom);
            MC_T p3_4_c3 = MC_MUL(MC_MOD(MC_POW3(k4), denom), c3_mod, denom);
            MC_T term1 = MC_MUL(MC_MOD(MC_POW2(k0 + 1U), denom), p3_234_c1, denom);

            for (uint32_t l0 = 2U; l0 <= l0_max; l0++) {
                uint32_t s0 = (k0 - 1U) + l0;
                MC_T base1 = MC_ADD(base0, term1, denom);

                uint32_t min_l1 = (k1 == k0) ? l0 : 2U;
                uint32_t min_l2 = (k2 == k0) ? l0 : 2U;
                uint32_t min_l3 = (k3 == k0) ? l0 : 2U;
                uint32_t min_l4 = (k4 == k0) ? l0 : 2U;
                uint32_t l1_max = rem_l - l0 - min_l2 - min_l3 - min_l4;

                if (min_l1 <= l1_max) {
                    uint32_t s01_start = s0 + (k1 - 1U) + min_l1;
                    MC_T term2 = MC_MUL(MC_MOD(MC_POW2(s01_start), denom), p3_34_c2, denom);

                    lv[0] = l0;
                    for (uint32_t l1 = min_l1; l1 <= l1_max; l1++) {
                        MC_T base2 = MC_ADD(base1, term2, denom);
                        uint32_t s01 = s0 + (k1 - 1U) + l1;
                        uint32_t l2_max = rem_l - l0 - l1 - min_l3 - min_l4;
                        if (min_l2 <= l2_max) {
                            uint32_t s012_start = s01 + (k2 - 1U) + min_l2;
                            MC_T term3 = MC_MUL(MC_MOD(MC_POW2(s012_start), denom), p3_4_c3, denom);

                            lv[1] = l1;
                            for (uint32_t l2 = min_l2; l2 <= l2_max; l2++) {
                                MC_T base3 = MC_ADD(base2, term3, denom);
                                uint32_t s012 = s01 + (k2 - 1U) + l2;
                                uint32_t l3_max = rem_l - l0 - l1 - l2 - min_l4;
                                if (min_l3 <= l3_max) {
                                    uint32_t s0123_start = s012 + (k3 - 1U) + min_l3;
                                    MC_T term4 = MC_MUL(MC_MOD(MC_POW2(s0123_start), denom),
                                                        c4_mod, denom);
                                    lv[2] = l2;
                                    for (uint32_t l3 = min_l3; l3 <= l3_max; l3++) {
                                        lv[3] = l3;
                                        lv[4] = rem_l - l0 - l1 - l2 - l3;
                                        if (c_eq == 1U || is_canonical_m(5U, kv, lv)) {
                                            MC_FN(eval_candidate)(ctx, 5U, k, s, kv, lv, denom,
                                                                  denom_ld, base3, term4, &thresh);
                                        }
                                        term4 = MC_ADD(term4, term4, denom);
                                    }
                                }
                                term3 = MC_ADD(term3, term3, denom);
                            }
                        }
                        term2 = MC_ADD(term2, term2, denom);
                    }
                }
                term1 = MC_ADD(term1, term1, denom);
            }
        }
    }
}

static void MC_FN(run_task_m6)(worker_ctx_t *ctx, const work_task_t *t) {
    uint32_t k = t->k;
    uint32_t s = t->s;
    uint32_t k0 = t->k0;
    uint32_t k1 = t->k1;
    uint32_t rem_l = s - k + 6U;
    if (rem_l < 12U) {
        return;
    }

    MC_T denom = MC_SUB(MC_POW2(s), MC_POW3(k));
    long double denom_ld = MC_TO_LD(denom);
    MC_T thresh = MC_NEAR_THRESH(ctx, 6U, denom, denom_ld);
    MC_T c0_mod = MC_MOD(MC_SUB(MC_POW3(k0), MC_POW2(k0)), denom);
    MC_T c1_mod = MC_MOD(MC_SUB(MC_POW3(k1), MC_POW2(k1)), denom);

    uint32_t kv[MAX_M] = {0};
    uint32_t lv[MAX_M] = {0};
    kv[0] = k0;
    kv[1] = k1;

    for (uint32_t k2 = k0; k2 <= k - 4U * k0 - k1; k2++) {
        kv[2] = k2;
        MC_T c2_mod = MC_MOD(MC_SUB(MC_POW3(k2), MC_POW2(k2)), denom);

        for (uint32_t k3 = k0; k3 <= k - 3U * k0 - k1 - k2; k3++) {
            kv[3] = k3;
            MC_T c3_mod = MC_MOD(MC_SUB(MC_POW3(k3), MC_POW2(k3)), denom);

            for (uint32_t k4 = k0; k4 <= k - 2U * k0 - k1 - k2 - k3; k4++) {
                uint32_t k5 = k - k0 - k1 - k2 - k3 - k4;
                if (k5 < k0) {
                    continue;
                }
                kv[4] = k4;
                kv[5] = k5;

                uint32_t c_eq = 1U + (k1 == k0 ? 1U : 0U) + (k2 == k0 ? 1U : 0U) +
                                (k3 == k0 ? 1U : 0U) + (k4 == k0 ? 1U : 0U) +
                                (k5 == k0 ? 1U : 0U);
                uint32_t l0_max = (rem_l - 2U * (6U - c_eq)) / c_eq;
                if (l0_max < 2U) {
                    continue;
                }

                MC_T c4_mod = MC_MOD(MC_SUB(MC_POW3(k4), MC_POW2(k4)), denom);
                MC_T c5_mod = MC_MOD(MC_SUB(MC_POW3(k5), MC_POW2(k5)), denom);
                MC_T base0 = MC_MUL(MC_MOD(MC_POW3(k1 + k2 + k3 + k4 + k5), denom), c0_mod, denom);
                MC_T p3_2345_c1 = MC_MUL(MC_MOD(MC_POW3(k2 + k3 + k4 + k5), denom), c1_mod, denom);
                MC_T p3_345_c2 = MC_MUL(MC_MOD(MC_POW3(k3 + k4 + k5), denom), c2_mod, denom);
                MC_T p3_45_c3 = MC_MUL(MC_MOD(MC_POW3(k4 + k5), denom), c3_mod, denom);
                MC_T p3_5_c4 = MC_MUL(MC_MOD(MC_POW3(k5), denom), c4_mod, denom);
                MC_T term1 = MC_MUL(MC_MOD(MC_POW2(k0 + 1U), denom), p3_2345_c1, denom);

                for (uint32_t l0 = 2U; l0 <= l0_max; l0++) {
                    uint32_t s0 = (k0 - 1U) + l0;
                    MC_T base1 = MC_ADD(base0, term1, denom);

                    uint32_t min_l1 = (k1 == k0) ? l0 : 2U;
                    uint32_t min_l2 = (k2 == k0) ? l0 : 2U;
                    uint32_t min_l3 = (k3 == k0) ? l0 : 2U;
                    uint32_t min_l4 = (k4 == k0) ? l0 : 2U;
                    uint32_t min_l5 = (k5 == k0) ? l0 : 2U;
                    uint32_t l1_max = rem_l - l0 - min_l2 - min_l3 - min_l4 - min_l5;

                    if (min_l1 <= l1_max) {
                        uint32_t s01_start = s0 + (k1 - 1U) + min_l1;
                        MC_T term2 = MC_MUL(MC_MOD(MC_POW2(s01_start), denom), p3_345_c2, denom);

                        lv[0] = l0;
                        for (uint32_t l1 = min_l1; l1 <= l1_max; l1++) {
                            MC_T base2 = MC_ADD(base1, term2, denom);
                            uint32_t s01 = s0 + (k1 - 1U) + l1;
                            uint32_t l2_max = rem_l - l0 - l1 - min_l3 - min_l4 - min_l5;
                            if (min_l2 <= l2_max) {
                                uint32_t s012_start = s01 + (k2 - 1U) + min_l2;
                                MC_T term3 =
                                    MC_MUL(MC_MOD(MC_POW2(s012_start), denom), p3_45_c3, denom);

                                lv[1] = l1;
                                for (uint32_t l2 = min_l2; l2 <= l2_max; l2++) {
                                    MC_T base3 = MC_ADD(base2, term3, denom);
                                    uint32_t s012 = s01 + (k2 - 1U) + l2;
                                    uint32_t l3_max = rem_l - l0 - l1 - l2 - min_l4 - min_l5;
                                    if (min_l3 <= l3_max) {
                                        uint32_t s0123_start = s012 + (k3 - 1U) + min_l3;
                                        MC_T term4 = MC_MUL(MC_MOD(MC_POW2(s0123_start), denom),
                                                            p3_5_c4, denom);

                                        lv[2] = l2;
                                        for (uint32_t l3 = min_l3; l3 <= l3_max; l3++) {
                                            MC_T base4 = MC_ADD(base3, term4, denom);
                                            uint32_t s0123 = s012 + (k3 - 1U) + l3;
                                            uint32_t l4_max = rem_l - l0 - l1 - l2 - l3 - min_l5;
                                            if (min_l4 <= l4_max) {
                                                uint32_t s01234_start =
                                                    s0123 + (k4 - 1U) + min_l4;
                                                MC_T term5 = MC_MUL(
                                                    MC_MOD(MC_POW2(s01234_start), denom), c5_mod,
                                                    denom);

                                                lv[3] = l3;
                                                for (uint32_t l4 = min_l4; l4 <= l4_max; l4++) {
                                                    lv[4] = l4;
                                                    lv[5] = rem_l - l0 - l1 - l2 - l3 - l4;
                                                    if (c_eq == 1U || is_canonical_m(6U, kv, lv)) {
                                                        MC_FN(eval_candidate)(
                                                            ctx, 6U, k, s, kv, lv, denom, denom_ld,
                                                            base4, term5, &thresh);
                                                    }
                                                    term5 = MC_ADD(term5, term5, denom);
                                                }
                                            }
                                            term4 = MC_ADD(term4, term4, denom);
                                        }
                                    }
                                    term3 = MC_ADD(term3, term3, denom);
                                }
                            }
                            term2 = MC_ADD(term2, term2, denom);
                        }
                    }
                    term1 = MC_ADD(term1, term1, denom);
                }
            }
        }
    }
}
