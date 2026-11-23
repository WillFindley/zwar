#!/usr/bin/env python3
"""Regression-implied exponent alpha* for every curve benchmark, and the
target-scaling prediction for the forecast designs.

Lemma (target scaling): if a target scales in expectation as Y ~ r^a N^b with
r = W / N, then Y ~ W^a N^(b - a), so ranking by E[Y] is ranking by W / N^alpha*
with alpha* = 1 - b/a. Total WAR (b = a) gives alpha* = 0, the rate (b = 0)
gives 1, the z-statistic r sqrt(N) gives 1/2, and a convex season value s^gamma
gives 1 - 1/gamma.

(1) Regression-implied alpha*. For every benchmark of 16_alpha_convergence.py
    except the pennant rows (same samples: data sets built by the functions of
    scripts 15 and 16), regress the target on log W and log N among players
    with W > 0 (N > 0 always) and set alpha* = -c_N / c_W, because
    c_W log W + c_N log N = c_W (log W - alpha* log N):
      * continuous targets (future WAR, All-Star selections, award shares,
        future rate, expert list order): OLS of the rank-based inverse-normal
        transform of the target (Blom scores, average ranks for ties; robust
        to the many zeros); check: OLS of log Y among Y > 0 (not for the
        expert list order, whose target is a rank);
      * binary targets (Hall of Fame, list membership): logistic regression.
    For two-way expert careers W = total WAR and N = PA + BF (exact for
    single-role players). 95% CIs: 1,000-resample player bootstrap (stratified
    by outcome for binary targets), refitting within each resample. The argmax
    alpha and its bootstrap interval are recomputed with alpha_bench.analyse
    under the same seeds as scripts 15 / 16 (identical values).
(2) Forecast designs (script 10: checkpoint k = 3, 5, careers to 2023; script
    15: checkpoint k = 3, 5 and career midpoint, careers to 2016; hitters and
    pitchers). For a cumulative future target Y = r_f N_f with
    log E[r_f] = kappa log r + const and log E[N_f] = beta log N + const,
    log E[Y] = kappa log r + beta log N = kappa log W + (beta - kappa) log N,
    so c_W = kappa, c_N = beta - kappa and alpha* = 1 - beta/kappa (reported
    unclipped and clipped to [0, 1]). Estimates:
      * beta  = OLS slope of log N_future on log N_first (players with N_future > 0);
      * kappa = OLS slope of log future rate on log first rate (W > 0, W_future > 0);
      * rate persistence: Spearman of first vs future rate (players with at
        least the minimum exposure, 1,000 PA / 600 BF, in the future period).
    Because the simple slopes ignore that playing time also responds to the
    rate (and the rate to playing time), the script also reports the full
    two-channel decomposition on the positive sample: log r_f and log N_f
    are each regressed on (log r, log N); with coefficients (k_r, k_N) and
    (n_r, n_N), alpha*_full = 1 - (k_N + n_N)/(k_r + n_r), which equals the
    log-Y regression on that sample exactly (OLS is additive).
Outputs: outputs/implied_alpha.csv, outputs/implied_alpha_designs.csv,
         outputs/implied_alpha_summary.txt
"""
import importlib.util
import os
import sys

import numpy as np
from scipy.stats import norm, rankdata, spearmanr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import OUT, write_csv  # noqa: E402
import alpha_bench as ab  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
N_BOOT = 1000
LOG = []


def log(msg=""):
    print(msg)
    LOG.append(msg)


def load_script(fname, modname):
    spec = importlib.util.spec_from_file_location(modname, os.path.join(HERE, fname))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# ---------------------------------------------------------------------------
# Regressions
# ---------------------------------------------------------------------------
def inv_normal_rank(y):
    r = rankdata(y)
    return norm.ppf((r - 0.375) / (len(y) + 0.25))


def ols(X, y):
    return np.linalg.lstsq(X, y, rcond=None)[0]


def logit(X, y, iters=50):
    b = np.zeros(X.shape[1])
    y = y.astype(float)
    for _ in range(iters):
        p = 1 / (1 + np.exp(-np.clip(X @ b, -35, 35)))
        w = p * (1 - p) + 1e-12
        step = np.linalg.solve(X.T @ (X * w[:, None]) + 1e-8 * np.eye(X.shape[1]), X.T @ (y - p))
        b += step
        if np.max(np.abs(step)) < 1e-10:
            break
    return b


def design_matrix(*cols):
    return np.column_stack([np.ones(len(cols[0]))] + [c - c.mean() for c in cols])


def implied(W, N, y, kind, how="rank"):
    """(alpha*, c_W, c_N, n) from one fit; how in {"rank", "log"}."""
    m = (W > 0) & (N > 0)
    if how == "log":
        m &= y > 0
    if m.sum() < 10 or (kind == "auc" and (y[m].sum() < 2 or (~y[m]).sum() < 2)):
        return np.nan, np.nan, np.nan, int(m.sum())
    X = design_matrix(np.log(W[m]), np.log(N[m]))
    if kind == "auc":
        c = logit(X, y[m])
    else:
        c = ols(X, inv_normal_rank(y[m]) if how == "rank" else np.log(y[m]))
    return -c[2] / c[1], c[1], c[2], int(m.sum())


def boot_implied(W, N, y, kind, seed, do_log):
    rng = np.random.default_rng(seed)
    pos = np.flatnonzero(y) if kind == "auc" else None
    neg = np.flatnonzero(~y) if kind == "auc" else None
    a_rank, a_log = [], []
    for _ in range(N_BOOT):
        if kind == "auc":
            i = np.concatenate([rng.choice(pos, len(pos)), rng.choice(neg, len(neg))])
        else:
            i = rng.integers(0, len(y), len(y))
        a_rank.append(implied(W[i], N[i], y[i], kind, "rank")[0])
        if do_log:
            a_log.append(implied(W[i], N[i], y[i], kind, "log")[0])

    def ci(v):
        v = np.asarray(v, float)
        v = v[np.isfinite(v)]
        return tuple(np.percentile(v, [2.5, 97.5])) if len(v) else (np.nan, np.nan)
    return ci(a_rank), (ci(a_log) if do_log else (np.nan, np.nan))


# ---------------------------------------------------------------------------
# Forecast designs: beta, kappa, predicted alpha*
# ---------------------------------------------------------------------------
def slope(x, y):
    return float(np.polyfit(x, y, 1)[0])


def design_stats(W, N, fW, fN):
    a = fN > 0
    beta = slope(np.log(N[a]), np.log(fN[a]))
    b = (W > 0) & (fW > 0) & (fN > 0)
    lr, lrf, lN, lNf = np.log(W[b] / N[b]), np.log(fW[b] / fN[b]), np.log(N[b]), np.log(fN[b])
    kappa = slope(lr, lrf)
    X = design_matrix(lr, lN)
    k = ols(X, lrf)
    n = ols(X, lNf)
    full = 1 - (k[2] + n[2]) / (k[1] + n[1])
    return dict(beta=beta, kappa=kappa, pred=1 - beta / kappa, full=full, k_r=k[1], k_N=k[2], n_r=n[1],
                n_N=n[2], n_beta=int(a.sum()), n_pos=int(b.sum()))


def design_boot(W, N, fW, fN, seed):
    rng = np.random.default_rng(seed)
    keys = ("beta", "kappa", "pred", "full")
    acc = {k: [] for k in keys}
    for _ in range(N_BOOT):
        i = rng.integers(0, len(W), len(W))
        s = design_stats(W[i], N[i], fW[i], fN[i])
        for k in keys:
            acc[k].append(s[k])
    return {k: tuple(np.percentile(v, [2.5, 97.5])) for k, v in acc.items()}


def clip01(x):
    return float(min(1.0, max(0.0, x)))


# ---------------------------------------------------------------------------
def main():
    m15 = load_script("15_forecast_benchmarks.py", "fb15")
    m16 = load_script("16_alpha_convergence.py", "ac16")
    m10 = m15.ckpt10

    asg, shares, _ = m15.databank()
    samples15 = m15.design_samples(asg, shares)
    sets = m16.hof_sets() + m16.expert_sets() + m16.checkpoint_sets()
    for s in sets:
        s["duplicate"] = ""
    for b in m15.benchmark_sets(asg, shares, samples15):
        sets.append(dict(benchmark=m16.benchmark_name_15(b["role"], b["design"], b["outcome"]),
                         category=b["category"], kind=b["kind"], key=b["name"], W=b["W"], N=b["N"], y=b["y"],
                         duplicate=m16.duplicate_note_15(b["design"], b["outcome"])))

    rows, res = [], {}
    log("(1) Regression-implied alpha* = -c_N / c_W (target ~ log W + log N, players with W > 0)")
    log(f"{'benchmark':84s} {'n':>5s} {'argmax [95%]':>17s}  {'alpha* rank-normal/logit [95%]':>31s}  "
        f"{'alpha* log Y [95%]':>24s}")
    for s in sets:
        W, N, y, kind = s["W"], s["N"], s["y"], s["kind"]
        S = s["S"] if "S" in s else ab.z_matrix(W, N)
        r = ab.analyse(S, y, kind, s["key"])
        a_star, cW, cN, n_reg = implied(W, N, y, kind, "rank")
        do_log = kind != "auc" and not s["key"].startswith("expert")
        a_log, _, _, n_log = implied(W, N, y, kind, "log") if do_log else (np.nan, 0, 0, 0)
        ci_r, ci_l = boot_implied(W, N, y, kind, ab.seed_for(s["key"], base=18), do_log)
        inside = r["boot_lo"] - 1e-9 <= a_star <= r["boot_hi"] + 1e-9
        res[s["benchmark"]] = dict(argmax=r["argmax"], lo=r["boot_lo"], hi=r["boot_hi"], a_star=a_star, ci=ci_r)
        rows.append([s["benchmark"], s["category"], "logit" if kind == "auc" else "OLS rank-normal",
                     len(y), n_reg, r["argmax"], r["boot_lo"], r["boot_hi"],
                     round(a_star, 6), round(ci_r[0], 6), round(ci_r[1], 6), round(cW, 6), round(cN, 6),
                     int(inside), round(a_log, 6) if do_log else "", n_log if do_log else "",
                     round(ci_l[0], 6) if do_log else "", round(ci_l[1], 6) if do_log else "", s["duplicate"]])
        logc = f"{a_log:5.2f} [{ci_l[0]:5.2f},{ci_l[1]:5.2f}] n={n_log}" if do_log else ""
        log(f"{s['benchmark'][:84]:84s} {len(y):5d} {r['argmax']:5.2f} [{r['boot_lo']:.2f},{r['boot_hi']:.2f}]  "
            f"{a_star:6.2f} [{ci_r[0]:6.2f},{ci_r[1]:6.2f}] n={n_reg:<5d}  {logc}"
            f"{'' if not s['duplicate'] else '  (dup)'}")
    write_csv("implied_alpha.csv",
              ["benchmark", "category", "model", "n", "n_regression", "argmax_alpha", "argmax_boot_lo",
               "argmax_boot_hi", "alpha_star", "alpha_star_lo", "alpha_star_hi", "c_logW", "c_logN",
               "alpha_star_in_argmax_interval", "alpha_star_logY", "n_logY", "alpha_star_logY_lo",
               "alpha_star_logY_hi", "note"], rows)

    # Agreement summary over the career-value headline set
    head = [r for r in rows if r[1] in ("judgment", "forecast", "concurrent") and not r[-1]]
    a_arg = np.array([r[5] for r in head], float)
    a_st = np.array([r[8] for r in head], float)
    rho_imp = float(spearmanr(a_arg, a_st)[0])
    assert abs(round(rho_imp, 2) - 0.79) < 1e-9, f"Unexpected Spearman(argmax, alpha*): {rho_imp}"
    judg_rows = [r for r in head if r[1] == "judgment"]
    assert len(judg_rows) == 12 and sum(r[13] for r in judg_rows) == 12
    assert abs(round(float(np.nanmedian([r[8] for r in judg_rows])), 2) - 0.26) < 1e-9
    log()
    log(f"  career-value benchmarks (duplicates excluded): {len(head)}; alpha* inside the argmax 95% interval in "
        f"{sum(r[13] for r in head)}/{len(head)}; Spearman(argmax, alpha*) = {rho_imp:.2f}; "
        f"median alpha* {np.nanmedian(a_st):.2f} vs median argmax {np.median(a_arg):.2f}")
    for cat in ("judgment", "concurrent", "forecast"):
        H = [r for r in head if r[1] == cat]
        log(f"    {cat:10s} n={len(H):2d} median alpha* {np.nanmedian([r[8] for r in H]):.2f}; "
            f"median argmax {np.median([r[5] for r in H]):.2f}; alpha* inside argmax interval {sum(r[13] for r in H)}/{len(H)}")

    # (2) forecast designs
    log()
    log("(2) Target scaling in the forecast designs: beta = d log N_fut / d log N_first, kappa = d log r_fut / "
        "d log r_first; predicted alpha* = 1 - beta/kappa; full = two-channel decomposition (= log future WAR fit)")
    designs = []
    for role, label in (("H", "Hitters"), ("P", "Pitchers")):
        for k in (3, 5):
            P = m10.build(role, k)
            designs.append((label, f"checkpoint k={k}", "2023", P, m10.MIN_N[role],
                            f"{label}, checkpoint k={k} (careers to 2023): future WAR"))
    for rlabel, design, rws in samples15:
        designs.append((rlabel, design, "2016", rws, m15.MIN_N[rlabel[0]],
                        m16.benchmark_name_15(rlabel, design, "future WAR")))
    drows = []
    for label, design, cut, P, min_n, bname in designs:
        W = np.array([p["W"] for p in P], float)
        N = np.array([p["N"] for p in P], float)
        fW = np.array([p["fW"] for p in P], float)
        fN = np.array([p["fN"] for p in P], float)
        st = design_stats(W, N, fW, fN)
        ci = design_boot(W, N, fW, fN, ab.seed_for(f"{label}|{design}|{cut}", base=180))
        m = fN >= min_n
        rho = float(spearmanr(W[m] / N[m], fW[m] / fN[m])[0])
        obs = res.get(bname, {})
        drows.append([label, design, cut, len(P), st["n_beta"], round(st["beta"], 6), round(ci["beta"][0], 6),
                      round(ci["beta"][1], 6), st["n_pos"], round(st["kappa"], 6), round(ci["kappa"][0], 6),
                      round(ci["kappa"][1], 6), int(m.sum()), round(rho, 6), round(st["pred"], 6),
                      round(clip01(st["pred"]), 6), round(ci["pred"][0], 6), round(ci["pred"][1], 6),
                      round(st["full"], 6), round(ci["full"][0], 6), round(ci["full"][1], 6),
                      round(st["k_r"], 6), round(st["k_N"], 6), round(st["n_r"], 6), round(st["n_N"], 6),
                      obs.get("argmax", ""), obs.get("lo", ""), obs.get("hi", ""),
                      round(obs.get("a_star", np.nan), 6), bname])
        log(f"  {label:8s} {design:15s} (to {cut}) n={len(P):4d}  beta {st['beta']:.3f} [{ci['beta'][0]:.3f},"
            f"{ci['beta'][1]:.3f}]  kappa {st['kappa']:.3f} [{ci['kappa'][0]:.3f},{ci['kappa'][1]:.3f}]  "
            f"rate rho {rho:.3f}  -> predicted 1-beta/kappa {st['pred']:+.2f} [{ci['pred'][0]:+.2f},"
            f"{ci['pred'][1]:+.2f}] (clipped {clip01(st['pred']):.2f}); full decomposition {st['full']:+.2f} "
            f"[{ci['full'][0]:+.2f},{ci['full'][1]:+.2f}] (rate k_r {st['k_r']:.2f}, k_N {st['k_N']:+.2f}; "
            f"exposure n_r {st['n_r']:+.2f}, n_N {st['n_N']:.2f})  | observed future-WAR argmax "
            f"{obs.get('argmax', float('nan')):.2f} [{obs.get('lo', float('nan')):.2f},"
            f"{obs.get('hi', float('nan')):.2f}], alpha* {obs.get('a_star', float('nan')):.2f}")
    write_csv("implied_alpha_designs.csv",
              ["role", "design", "careers_to", "n", "n_beta", "beta", "beta_lo", "beta_hi", "n_positive", "kappa",
               "kappa_lo", "kappa_hi", "n_rate_rho", "rate_spearman", "pred_alpha_1_minus_beta_over_kappa",
               "pred_alpha_clipped", "pred_lo", "pred_hi", "alpha_full_decomposition", "full_lo", "full_hi",
               "rate_on_logr", "rate_on_logN", "exposure_on_logr", "exposure_on_logN",
               "observed_argmax_futureWAR", "argmax_lo", "argmax_hi", "implied_alpha_star_futureWAR",
               "benchmark"], drows)
    # Table 6 / Section 5.5 headline persistence and two-equation decomposition assertions
    t6 = [d for d in drows if (d[1].startswith("checkpoint") and d[2] == "2023") or (d[1] == "midpoint" and d[2] == "2016")]
    assert len(t6) == 6
    assert all(0.865 <= d[5] <= 1.635 for d in t6)
    h6 = [d for d in t6 if d[0] == "Hitters"]
    p6 = [d for d in t6 if d[0] == "Pitchers"]
    assert all(0.415 <= d[9] <= 0.495 and 0.525 <= d[13] <= 0.595 for d in h6)
    assert all(0.025 <= d[9] <= 0.195 and 0.225 <= d[13] <= 0.265 for d in p6)
    d_map = {(d[0], d[1], d[2]): d for d in drows}
    k3 = d_map[("Hitters", "checkpoint k=3", "2023")]
    k5 = d_map[("Hitters", "checkpoint k=5", "2023")]
    assert (f"{k3[18]:.2f}", f"{k3[19]:.2f}", f"{k3[20]:.2f}") == ("0.37", "-0.35", "0.99")
    assert (f"{k5[18]:.2f}", f"{k5[19]:.2f}", f"{k5[20]:.2f}") == ("-0.21", "-0.83", "0.24")
    with open(os.path.join(OUT, "implied_alpha_summary.txt"), "w") as fh:
        fh.write("\n".join(LOG) + "\n")


if __name__ == "__main__":
    main()
