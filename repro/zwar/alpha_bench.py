"""Shared machinery for the alpha-curve benchmarks (scripts 15 and 16).

Every benchmark is a score matrix S (players x alpha grid; column j holds the
scores of Z_alpha_j = W / N^alpha_j, or any other family indexed by alpha) and an
outcome y. The metric is Spearman's rho (average ranks for ties, identical to
scipy.stats.spearmanr) or the AUC (Mann-Whitney, ties = 1/2, identical to
common.auc). For each benchmark this module computes

  * the alpha curve, its argmax (first maximum on the grid, ties within 1e-12
    resolved toward the smaller alpha, as in 04_hof_validation.best_alpha),
  * the metric at alpha = 0, 0.2, 0.5, 1,
  * a player bootstrap (stratified by outcome for AUCs) of the argmax alpha
    (median and 95% percentile interval, read off the grid with the
    inverted-CDF rule so the endpoints are grid values) and of the metric
    differences m(0.2) - m(0.5) and m(0.2) - m(0),
  * optionally, K-fold x R-repeat cross-validation: alpha chosen on the
    training folds, held-out metric for the CV-chosen alpha and for fixed
    alpha = 0.2, 0.5 and 0 (folds stratified by outcome for AUCs).

Pure numpy / scipy; all randomness through numpy Generators with fixed seeds.
"""
import zlib

import numpy as np
from scipy.stats import rankdata

ALPHAS = np.round(np.arange(0, 1.0001, 0.05), 2)
A_REPORT = (0.0, 0.2, 0.5, 1.0)
N_BOOT = 1000
CV_FOLDS, CV_REPEATS = 5, 20


def seed_for(name, base=2026):
    """Deterministic per-benchmark seed (stable across runs and platforms)."""
    return base + zlib.crc32(name.encode("utf-8")) % 1_000_000


def z_matrix(W, N, alphas=ALPHAS):
    """Scores W / max(N, 1)^alpha for every alpha (players x alphas)."""
    W = np.asarray(W, float)
    N = np.maximum(np.asarray(N, float), 1.0)
    return W[:, None] / N[:, None] ** np.asarray(alphas)[None, :]


def col_spearman(S, y):
    """Spearman rho of each column of S with y (average ranks for ties)."""
    R = rankdata(S, axis=0)
    ry = rankdata(y)
    R = R - R.mean(axis=0)
    ry = ry - ry.mean()
    den = np.sqrt((R ** 2).sum(axis=0) * (ry ** 2).sum())
    with np.errstate(invalid="ignore", divide="ignore"):
        return (R * ry[:, None]).sum(axis=0) / den


def col_auc(S, y):
    """AUC of each column of S for binary y (Mann-Whitney, ties = 1/2)."""
    y = np.asarray(y, bool)
    n1, n0 = int(y.sum()), int((~y).sum())
    if n1 == 0 or n0 == 0:
        return np.full(S.shape[1], np.nan)
    R = rankdata(S, axis=0)
    return (R[y].sum(axis=0) - n1 * (n1 + 1) / 2) / (n1 * n0)


def curve(S, y, kind):
    return col_auc(S, y) if kind == "auc" else col_spearman(S, y)


def argmax_idx(c):
    best = 0
    for j in range(1, len(c)):
        if c[j] > c[best] + 1e-12:
            best = j
    return best


def _q(x, p):
    return float(np.quantile(np.asarray(x, float), p, method="inverted_cdf"))


def _resample(rng, n, pos, neg, kind):
    if kind == "auc":
        return np.concatenate([rng.choice(pos, len(pos)), rng.choice(neg, len(neg))])
    return rng.integers(0, n, n)


def analyse(S, y, kind, name, alphas=ALPHAS, n_boot=N_BOOT, cv=False):
    """Full summary of one benchmark. kind in {"spearman", "auc"}."""
    S = np.asarray(S, float)
    y = np.asarray(y, bool if kind == "auc" else float)
    alphas = np.asarray(alphas)
    jx = {a: int(np.flatnonzero(np.isclose(alphas, a))[0]) for a in A_REPORT}
    c = curve(S, y, kind)
    jb = argmax_idx(c)
    res = dict(name=name, kind=kind, n=len(y), n_pos=int(y.sum()) if kind == "auc" else "",
               curve=c, argmax=float(alphas[jb]), m_argmax=float(c[jb]))
    for a in A_REPORT:
        res[f"m{a:g}"] = float(c[jx[a]])
    res["d02_05"] = res["m0.2"] - res["m0.5"]
    res["d02_0"] = res["m0.2"] - res["m0"]

    rng = np.random.default_rng(seed_for(name))
    pos = np.flatnonzero(y) if kind == "auc" else None
    neg = np.flatnonzero(~y) if kind == "auc" else None
    am, d1, d2 = [], [], []
    for _ in range(n_boot):
        idx = _resample(rng, len(y), pos, neg, kind)
        cb = curve(S[idx], y[idx], kind)
        am.append(alphas[argmax_idx(cb)])
        d1.append(cb[jx[0.2]] - cb[jx[0.5]])
        d2.append(cb[jx[0.2]] - cb[jx[0.0]])
    res["boot_argmax"] = np.array(am)
    res["boot_median"] = _q(am, 0.5)
    res["boot_lo"], res["boot_hi"] = _q(am, 0.025), _q(am, 0.975)
    res["d02_05_lo"], res["d02_05_hi"] = (float(v) for v in np.percentile(d1, [2.5, 97.5]))
    res["d02_0_lo"], res["d02_0_hi"] = (float(v) for v in np.percentile(d2, [2.5, 97.5]))
    res["has02"] = bool(res["boot_lo"] - 1e-9 <= 0.2 <= res["boot_hi"] + 1e-9)
    res["has05"] = bool(res["boot_lo"] - 1e-9 <= 0.5 <= res["boot_hi"] + 1e-9)
    if cv:
        res.update(cross_validate(S, y, kind, name, alphas, jx))
    return res


def cross_validate(S, y, kind, name, alphas, jx):
    rng = np.random.default_rng(seed_for(name, base=7))
    n = len(y)
    chosen, cvm, f02, f05, f0 = [], [], [], [], []
    for _ in range(CV_REPEATS):
        if kind == "auc":
            fp = np.array_split(rng.permutation(np.flatnonzero(y)), CV_FOLDS)
            fn = np.array_split(rng.permutation(np.flatnonzero(~y)), CV_FOLDS)
            folds = [np.concatenate([fp[k], fn[k]]) for k in range(CV_FOLDS)]
        else:
            folds = np.array_split(rng.permutation(n), CV_FOLDS)
        for test in folds:
            train = np.setdiff1d(np.arange(n), test)
            ct = curve(S[train], y[train], kind)
            j = argmax_idx(ct)
            ch = curve(S[test], y[test], kind)
            chosen.append(float(alphas[j]))
            cvm.append(ch[j])
            f02.append(ch[jx[0.2]])
            f05.append(ch[jx[0.5]])
            f0.append(ch[jx[0.0]])
    return dict(cv_metric=float(np.nanmean(cvm)), cv_02=float(np.nanmean(f02)),
                cv_05=float(np.nanmean(f05)), cv_0=float(np.nanmean(f0)),
                cv_alpha_p10=_q(chosen, 0.10), cv_alpha_p50=_q(chosen, 0.50),
                cv_alpha_p90=_q(chosen, 0.90))


SUMMARY_FIELDS = ["n", "n_pos", "m0", "m0.2", "m0.5", "m1", "argmax", "m_argmax",
                  "boot_median", "boot_lo", "boot_hi", "has02", "has05",
                  "d02_05", "d02_05_lo", "d02_05_hi", "d02_0", "d02_0_lo", "d02_0_hi"]
CV_FIELDS = ["cv_metric", "cv_02", "cv_05", "cv_0", "cv_alpha_p10", "cv_alpha_p50", "cv_alpha_p90"]


def fmt_row(r, cv=True):
    def f(k):
        v = r.get(k, "")
        if isinstance(v, (bool, np.bool_)):
            return int(v)
        if isinstance(v, float):
            return round(v, 6)
        return v
    return [f(k) for k in SUMMARY_FIELDS + (CV_FIELDS if cv else [])]


def describe(r):
    """One human-readable line block for a benchmark."""
    s = (f"  n={r['n']}{' (' + str(r['n_pos']) + ' positives)' if r['kind'] == 'auc' else ''}  "
         f"m(0)={r['m0']:.3f} m(0.2)={r['m0.2']:.3f} m(0.5)={r['m0.5']:.3f} m(1)={r['m1']:.3f}  "
         f"argmax {r['argmax']:.2f} ({r['m_argmax']:.3f}); bootstrap argmax median {r['boot_median']:.2f} "
         f"[{r['boot_lo']:.2f}, {r['boot_hi']:.2f}]\n"
         f"  m(0.2)-m(0.5) {r['d02_05']:+.3f} [{r['d02_05_lo']:+.3f}, {r['d02_05_hi']:+.3f}]; "
         f"m(0.2)-m(0) {r['d02_0']:+.3f} [{r['d02_0_lo']:+.3f}, {r['d02_0_hi']:+.3f}]")
    if "cv_metric" in r:
        s += (f"\n  CV held-out: chosen-alpha {r['cv_metric']:.4f} | a=0.2 {r['cv_02']:.4f} | "
              f"a=0.5 {r['cv_05']:.4f} | a=0 {r['cv_0']:.4f}; chosen alpha median "
              f"{r['cv_alpha_p50']:.2f} (10-90%: {r['cv_alpha_p10']:.2f}-{r['cv_alpha_p90']:.2f})")
    return s
