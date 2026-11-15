/* Block-width planner for the kernel campaign (NOT rigorous; it only proposes).
 *
 * Derived from PsiCert-Claude-Handoff/reference/psisieve.c. It walks the same
 * segments as tools/psi_planner/GenCampaign.lean: odd numbers lo, lo+2, ...,
 * segments of 2^s bits from lo = A0 + 1 up to N (the last one shorter), and
 * for each segment picks the largest block exponent w <= WMAX such that every
 * block [A, A + 2^(w+1)] passes, with a safety margin, the two guards of
 * PsiFinite.blockStep for a floating-point model of the Lean enclosures:
 *
 *   U(A') = U(A) + c log A' + sum_pp log A' / j      (upper, at block ends)
 *   V(A') = V(A) + c log A  + sum_pp log A  / j      (lower)
 *   U(A') - A <= k sqrt A - margin,   A' - V(A) <= k sqrt A' - margin.
 *
 * It writes "lo w" lines to the plan file, and prints the psisieve.c
 * statistics (pi(N), psi(N) - N, extremal ratios) for comparison with
 * reference/results.txt, plus totals used for cost estimates.
 *
 * Block lengths are also capped, 2^(w+1) <= c sqrt(lo) + 16, with c = c1 below X1
 * and c2 above: the enclosure width grows like c sqrt(x) / log x, and must stay
 * well below the slack 0.0094 sqrt(x) at x = 110102617.
 *
 * Usage: psi_planner N A0 U0 V0 s plan.txt [k=0.8] [margin=1.0] [c1=0.03] [X1=1.3e8] [c2=0.15]
 *                    [sEarly=s] [Xs=0]
 *   segments have 2^sEarly bits while lo < Xs, 2^s bits afterwards.
 *   U0, V0: psi(A0) upper/lower (A0 must be even; the small walk gives psi(10^4)).
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define WMAX 16

typedef struct { uint64_t m; int j; double lp; } PP;
static int cmp_pp(const void *a, const void *b) {
    uint64_t x = ((const PP *)a)->m, y = ((const PP *)b)->m;
    return x < y ? -1 : x > y;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: %s N A0 U0 V0 s plan [k] [margin]\n", argv[0]); return 1; }
    uint64_t N = strtoull(argv[1], 0, 10), A0 = strtoull(argv[2], 0, 10);
    long double U = strtold(argv[3], 0), V = strtold(argv[4], 0);
    int sbits = atoi(argv[5]);
    FILE *plan = fopen(argv[6], "w");
    double kk = argc > 7 ? atof(argv[7]) : 0.8, margin = argc > 8 ? atof(argv[8]) : 1.0;
    double c1 = argc > 9 ? atof(argv[9]) : 0.03, X1 = argc > 10 ? atof(argv[10]) : 1.3e8;
    double c2 = argc > 11 ? atof(argv[11]) : 0.15;
    int sEarly = argc > 12 ? atoi(argv[12]) : sbits;
    double Xs = argc > 13 ? atof(argv[13]) : 0;
    if (A0 % 2 || N % 2 || !plan) { fprintf(stderr, "A0 and N must be even\n"); return 1; }

    uint64_t root = (uint64_t)sqrtl((long double)N) + 2;
    char *small = calloc(root + 1, 1);
    uint32_t *bp = malloc(sizeof(uint32_t) * (root / 2 + 16));
    size_t nbp = 0;
    for (uint64_t i = 2; i <= root; i++) {
        if (small[i]) continue;
        bp[nbp++] = (uint32_t)i;
        for (uint64_t j = i * i; j <= root; j += i) small[j] = 1;
    }
    size_t cap = 1 << 16, npp = 0;
    PP *pp = malloc(sizeof(PP) * cap);
    for (size_t i = 0; i < nbp; i++) {
        uint64_t p = bp[i];
        int j = 2;
        for (uint64_t q = p * p; q <= N; j++) {
            if (q > A0) { if (npp == cap) { cap *= 2; pp = realloc(pp, sizeof(PP) * cap); }
                          pp[npp].m = q; pp[npp].j = j; pp[npp].lp = log((double)p); npp++; }
            if (q > N / p) break;
            q *= p;
        }
    }
    qsort(pp, npp, sizeof(PP), cmp_pp);

    const uint64_t S = 1ULL << sbits;
    unsigned char *comp = malloc(S);
    uint32_t *cnt = malloc(sizeof(uint32_t) * (S + 1));   /* prefix prime counts */
    long double *slog = malloc(sizeof(long double) * (S + 1)); /* prefix sum of log p */
    size_t ip = 0;
    uint64_t lo = A0 + 1, nseg = 0, nblocks = 0, pcount = 0;
    long double psi = (U + V) / 2;  /* only for statistics */
    double wsum[WMAX + 1] = {0};
    double worst = 1e300, tight = 1e300; uint64_t worstA = 0, tightA = 0;
    while (lo - 1 < N) {
        uint64_t bits = (N - (lo - 1)) / 2;
        uint64_t Sx = (double)lo < Xs ? (1ULL << sEarly) : S;
        if (bits > Sx) bits = Sx;
        memset(comp, 0, bits);
        uint64_t hi = lo + 2 * (bits - 1);
        for (size_t i = 1; i < nbp; i++) {
            uint64_t d = bp[i];
            if (d * d > hi) break;
            uint64_t start = d * d >= lo ? (d * d - lo) / 2
                : ((d - lo % d) % d * ((d + 1) / 2)) % d;
            for (uint64_t j = start; j < bits; j += d) comp[j] = 1;
        }
        cnt[0] = 0; slog[0] = 0;
        for (uint64_t i = 0; i < bits; i++) {
            int pr = !comp[i];
            cnt[i + 1] = cnt[i] + pr;
            slog[i + 1] = slog[i] + (pr ? logl((long double)(lo + 2 * i)) : 0);
        }
        pcount += cnt[bits];
        /* prime powers of this segment: (lo-1, lo-1+2 bits] */
        size_t ip0 = ip;
        while (ip < npp && pp[ip].m <= lo - 1 + 2 * bits) ip++;
        int w = WMAX;
        double cap = ((double)lo < X1 ? c1 : c2) * sqrt((double)lo) + 16;
        while (w > 0 && (bits % (1ULL << w) || (double)(2ULL << w) > cap)) w--;
        long double U1 = 0, V1 = 0;
        double seg_worst = 0;
        for (; ; w--) {
            uint64_t W = 1ULL << w, B = bits / W;
            long double u = U, v = V;
            size_t q = ip0;
            int ok = 1;
            double sw = 1e300;
            for (uint64_t k = 0; k < B && ok; k++) {
                uint64_t A = lo - 1 + 2 * W * k, A1 = A + 2 * W;
                long double la = logl((long double)A), la1 = logl((long double)A1);
                long double c = cnt[W * (k + 1)] - cnt[W * k];
                long double ppu = 0, ppv = 0;
                while (q < ip && pp[q].m <= A1) { ppu += la1 / pp[q].j; ppv += la / pp[q].j; q++; }
                long double u1 = u + c * la1 + ppu;
                double m1 = kk * sqrt((double)A) - (double)(u1 - (long double)A);
                double m2 = kk * sqrt((double)A1) - (double)((long double)A1 - v);
                if (m1 < sw) sw = m1;
                if (m2 < sw) sw = m2;
                if (m1 < margin || m2 < margin) ok = 0;
                v = v + c * la + ppv;
                u = u1;
            }
            if (ok || w == 0) {
                if (!ok) { fprintf(stderr, "planner: segment lo=%llu fails at w=0\n",
                                   (unsigned long long)lo); return 2; }
                U1 = u; V1 = v; seg_worst = sw;
                nblocks += B;
                break;
            }
        }
        if (seg_worst < worst) { worst = seg_worst; worstA = lo; }
        if (lo > 100000000 && lo < 120000000 && seg_worst < tight) { tight = seg_worst; tightA = lo; }
        fprintf(plan, "%llu %d\n", (unsigned long long)lo, w);
        wsum[w] += 1;
        psi += slog[bits];
        for (size_t t = ip0; t < ip; t++) psi += pp[t].lp;
        U = U1; V = V1;
        lo += 2 * bits;
        nseg++;
    }
    fclose(plan);
    printf("N=%llu A0=%llu segment bits=2^%d k=%.4f margin=%.3f c1=%.4f X1=%.3g c2=%.4f\n",
           (unsigned long long)N, (unsigned long long)A0, sbits, kk, margin, c1, X1, c2);
    printf("odd primes in (A0, N]=%llu  proper prime powers in (A0, N]=%zu\n",
           (unsigned long long)pcount, npp);
    printf("psi(N) - N = %.4Lf   (model enclosure [%.4Lf, %.4Lf])\n", psi - (long double)N,
           V - (long double)N, U - (long double)N);
    printf("segments=%llu blocks=%llu  smallest guard slack %.3f in segment lo=%llu\n",
           (unsigned long long)nseg, (unsigned long long)nblocks, worst, (unsigned long long)worstA);
    printf("smallest slack in (1e8, 1.2e8): %.3f in segment lo=%llu\n", tight,
           (unsigned long long)tightA);
    printf("segments per w:");
    for (int w = 0; w <= WMAX; w++) if (wsum[w] > 0) printf(" w%d:%.0f", w, wsum[w]);
    printf("\n");
    return 0;
}
