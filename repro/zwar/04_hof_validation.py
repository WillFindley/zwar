#!/usr/bin/env python3
"""Hall of Fame classification analysis (paper Section 5.3, Table 4, Appendix J), extended with:

  * stratified bootstrap 95% CIs for AUC differences, including relief pitchers
  * bootstrap CIs for each relief-pitcher AUC (only ~8 Hall of Famers)
  * cross-validated choice of alpha (repeated stratified K-fold)
  * Gordon's Standardized Peak WAR (SPW) as an additional benchmark
  * the pitcher scale factor c in the pooled hitter + SP sample
  * the value point of the family, alpha = 0.2 (gamma = 1.25), with bootstrap
    CIs against career WAR and JAWS

Outputs: outputs/hof_auc.csv, outputs/hof_bootstrap.csv, outputs/hof_cv_alpha.csv,
         outputs/hof_c_grid.csv, outputs/hof_summary.txt
"""
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import auc, bootstrap_auc_diff, bootstrap_auc_ci, career, z_alpha, z2d, write_csv, OUT  # noqa: E402
from pools import hitters, pitchers, hof_eligible  # noqa: E402

ALPHAS = np.round(np.arange(0, 1.0001, 0.05), 2)
A_VALUE = 0.2   # value point of the family (gamma = 1.25; Proposition 4, Section 4)
N_BOOT = 2000
CV_FOLDS, CV_REPEATS = 5, 20
LOG = []


def log(msg=""):
    print(msg)
    LOG.append(msg)


def metric(players, name, alpha=0.5, c=1.0):
    vals = []
    for p in players:
        scale = c if p["role"] in ("SP", "RP") else 1.0
        if name == "Z":
            vals.append(scale * z_alpha(p["W"], p["N"], alpha))
        elif name == "WAR":
            vals.append(scale * p["W"])
        elif name == "S_JAWS":
            vals.append(p["S_JAWS"] if p.get("S_JAWS") is not None else p["JAWS"])
        elif name == "R_JAWS":
            vals.append(p["R_JAWS"] if p.get("R_JAWS") is not None else p["JAWS"])
        elif name == "SR_JAWS":
            # Role-appropriate published variant: S-JAWS for starters, R-JAWS for relievers
            v = p.get("S_JAWS") if p["role"] == "SP" else p.get("R_JAWS")
            vals.append(v if v is not None else p["JAWS"])
        else:
            vals.append(p[name])
    return np.array(vals, float)


def labels(players):
    return np.array([p["hof"] for p in players], bool)


def best_alpha(players, idx=None, c=1.0):
    y = labels(players)
    best = None
    for a in ALPHAS:
        s = metric(players, "Z", a, c)
        v = auc(s[idx], y[idx]) if idx is not None else auc(s, y)
        if best is None or v > best[1] + 1e-12:
            best = (a, v)
    return best


def cv_alpha(players, seed=2026):
    """Repeated stratified K-fold: choose alpha on the training folds, score the
    held-out fold. Returns mean held-out AUC for the CV-chosen alpha, for fixed
    alpha = 0.5 and 0, and the list of chosen alphas."""
    rng = np.random.default_rng(seed)
    y = labels(players)
    pos, neg = np.flatnonzero(y), np.flatnonzero(~y)
    scores = {a: metric(players, "Z", a) for a in ALPHAS}
    chosen, cv, fixed05, fixed0, fixed02 = [], [], [], [], []
    for _ in range(CV_REPEATS):
        fp = np.array_split(rng.permutation(pos), CV_FOLDS)
        fn = np.array_split(rng.permutation(neg), CV_FOLDS)
        for k in range(CV_FOLDS):
            test = np.concatenate([fp[k], fn[k]])
            train = np.setdiff1d(np.arange(len(y)), test)
            a_best = max(ALPHAS, key=lambda a: auc(scores[a][train], y[train]))
            chosen.append(float(a_best))
            cv.append(auc(scores[a_best][test], y[test]))
            fixed05.append(auc(scores[0.5][test], y[test]))
            fixed0.append(auc(scores[0.0][test], y[test]))
            fixed02.append(auc(scores[A_VALUE][test], y[test]))
    return (float(np.nanmean(cv)), float(np.nanmean(fixed05)), float(np.nanmean(fixed0)),
            chosen, float(np.nanmean(fixed02)))


def main():
    H = hof_eligible(hitters())
    SP = hof_eligible(pitchers("SP"))
    RP = hof_eligible(pitchers("RP"))
    HSP = H + SP

    def contested(ps):
        return [p for p in ps if p["W"] >= 40]

    pools = [
        ("Hitters (8 positions pooled)", H, "JAWS"),
        ("Starting pitchers", SP, "S_JAWS"),
        ("Relief pitchers", RP, "R_JAWS"),
        ("Hitters + SP pooled", HSP, "S_JAWS"),
        ("SP + RP pooled", SP + RP, "SR_JAWS"),
        ("Contested hitters", contested(H), "JAWS"),
        ("Contested SP", contested(SP), "S_JAWS"),
        ("Contested hitters + SP", contested(H) + contested(SP), "S_JAWS"),
    ]

    auc_rows, boot_rows, cv_rows = [], [], []
    log("Hall of Fame AUC (final season <= 2010; banned/PED excluded)")
    log(f"{'pool':32s} {'n':>5s} {'HOF':>4s} {'WAR':>6s} {'WAR7':>6s} {'JAWS':>6s} "
        f"{'alt':>6s} {'WAA':>6s} {'SPW':>6s} {'Z0.2':>6s} {'Z':>6s} {'bestA':>5s} {'AUC':>6s}")
    for name, ps, alt in pools:
        y = labels(ps)
        m = {k: auc(metric(ps, k), y) for k in ["WAR", "WAR7", "JAWS", "WAA", "SPW"]}
        m["Z"] = auc(metric(ps, "Z"), y)
        m["Z02"] = auc(metric(ps, "Z", A_VALUE), y)
        m["alt"] = auc(metric(ps, alt), y) if alt else float("nan")
        a_best, a_auc = best_alpha(ps)
        log(f"{name:32s} {len(ps):5d} {int(y.sum()):4d} {m['WAR']:6.3f} {m['WAR7']:6.3f} "
            f"{m['JAWS']:6.3f} {m['alt']:6.3f} {m['WAA']:6.3f} {m['SPW']:6.3f} {m['Z02']:6.3f} {m['Z']:6.3f} "
            f"{a_best:5.2f} {a_auc:6.3f}")
        auc_rows.append([name, len(ps), int(y.sum()), *(round(m[k], 4) for k in
                         ["WAR", "WAR7", "JAWS", "alt", "WAA", "SPW", "Z"]), a_best, round(a_auc, 4),
                         round(m["Z02"], 4)])

    # Mean over the eight hitter positions
    per_pos = {}
    for p in H:
        per_pos.setdefault(p["pos"], []).append(p)
    means = {k: [] for k in ["WAR", "WAR7", "JAWS", "WAA", "SPW", "Z"]}
    alpha_curve = {a: [] for a in ALPHAS}
    pos_detail = []
    for pos, ps in per_pos.items():
        y = labels(ps)
        for k in means:
            means[k].append(auc(metric(ps, k), y))
        for a in ALPHAS:
            alpha_curve[a].append(auc(metric(ps, "Z", a), y))
        pos_detail.append((pos, auc(metric(ps, "Z"), y), auc(metric(ps, "JAWS"), y)))
    log("Hitters (mean of 8 positions): " + ", ".join(
        f"{k}={np.mean(v):.3f}" for k, v in means.items()))
    a_curve = {a: float(np.mean(v)) for a, v in alpha_curve.items()}
    a_best = max(a_curve, key=a_curve.get)
    log(f"  mean-over-positions alpha curve: best alpha={a_best:.2f} ({a_curve[a_best]:.3f}); "
        + " ".join(f"{a:.2f}:{a_curve[a]:.3f}" for a in [0, .2, .25, .3, .4, .5, .7, 1.0]))
    log("  by position (Z vs JAWS): " + ", ".join(f"{p} {z:.3f}/{j:.3f}" for p, z, j in pos_detail))

    # Bootstrap CIs for AUC differences
    log("")
    log(f"Stratified bootstrap 95% CIs for AUC(Z) - AUC(other), {N_BOOT} resamples")
    for name, ps, alt in pools:
        y = labels(ps)
        z = metric(ps, "Z")
        others = ["JAWS", "WAR", "WAA", "SPW"] + ([alt] if alt and alt != "JAWS" else [])
        parts = []
        for o in others:
            lo, hi = bootstrap_auc_diff(z, metric(ps, o), y, N_BOOT)
            parts.append(f"{o} [{lo:+.3f}, {hi:+.3f}]")
            boot_rows.append([name, o, round(lo, 4), round(hi, 4)])
        log(f"  {name:30s} " + "; ".join(parts))
    log(f"Stratified bootstrap 95% CIs for AUC(Z_{A_VALUE}) - AUC(other), {N_BOOT} resamples")
    for name, ps, alt in pools:
        y = labels(ps)
        z02 = metric(ps, "Z", A_VALUE)
        parts = []
        for o in ["WAR", "JAWS"] + ([alt] if alt and alt != "JAWS" else []) + ["Z"]:
            other = metric(ps, o)
            lo, hi = bootstrap_auc_diff(z02, other, y, N_BOOT)
            parts.append(f"{o if o != 'Z' else 'Z_1/2'} [{lo:+.3f}, {hi:+.3f}]")
            boot_rows.append([name + f" (Z_{A_VALUE})", o, round(lo, 4), round(hi, 4)])
        log(f"  {name:30s} " + "; ".join(parts))

    # Relief pitchers: CI for each AUC
    yrp = labels(RP)
    log("")
    log(f"Relief pitchers: {len(RP)} players, {int(yrp.sum())} Hall of Famers: "
        + ", ".join(p["name"] for p in RP if p["hof"]))
    for k in ["WAR", "WAR7", "JAWS", "R_JAWS", "WAA", "SPW", "Z"]:
        s = metric(RP, k)
        lo, hi = bootstrap_auc_ci(s, yrp, N_BOOT)
        log(f"  AUC({k:6s}) = {auc(s, yrp):.3f}  95% CI [{lo:.3f}, {hi:.3f}]")
        boot_rows.append(["Relief pitchers (AUC CI)", k, round(lo, 4), round(hi, 4)])

    # Cross-validated alpha
    log("")
    log(f"Cross-validated alpha ({CV_REPEATS}x repeated stratified {CV_FOLDS}-fold)")
    for name, ps, _ in pools:
        cv, f05, f0, chosen, f02 = cv_alpha(ps)
        q = np.percentile(chosen, [10, 50, 90])
        log(f"  {name:30s} held-out AUC: CV-alpha {cv:.3f} | alpha=0.5 {f05:.3f} | alpha=0.2 {f02:.3f}"
            f" | alpha=0 {f0:.3f}"
            f" | chosen alpha median {q[1]:.2f} (10-90%: {q[0]:.2f}-{q[2]:.2f})")
        cv_rows.append([name, round(cv, 4), round(f05, 4), round(f0, 4),
                        q[0], q[1], q[2], round(f02, 4)])

    # Pitcher scale factor c
    log("")
    yh = labels(HSP)
    c_rows = []
    parts = []
    for c in [0.8, 0.9, 1.0, 1.1, 1.2, 1.3, 1.4, 59 / 41]:
        v = auc(metric(HSP, "Z", 0.5, c), yh)
        c_rows.append([round(c, 4), round(v, 4)])
        parts.append(f"c={c:.2f}:{v:.3f}")
    log("Hitters + SP pooled, pitcher scale factor: " + " ".join(parts)
        + "  (59/41 = bWAR equal-pool factor)")

    # Pooled SP + RP: where do the relief Hall of Famers rank?
    SPRP = SP + RP
    log("")
    log("SP + RP pooled: ranks of relief Hall of Famers in the combined pitcher list")
    for k in ["WAR", "JAWS", "Z"]:
        s = metric(SPRP, k)
        order = (-s).argsort(kind="mergesort").argsort(kind="mergesort")
        ranks = sorted(int(order[i]) + 1 for i, p in enumerate(SPRP) if p["hof"] and p["role"] == "RP")
        log(f"  {k:5s} {ranks}")

    # Sensitivity to the banned/PED exclusions
    Hi, SPi, RPi = (hof_eligible(hitters(), exclude=False), hof_eligible(pitchers("SP"), exclude=False),
                    hof_eligible(pitchers("RP"), exclude=False))
    max_change = 0.0
    for (a, b) in [(H, Hi), (SP, SPi), (RP, RPi), (HSP, Hi + SPi)]:
        for k in ["WAR", "WAR7", "JAWS", "WAA", "SPW", "Z"]:
            d = abs(auc(metric(a, k), labels(a)) - auc(metric(b, k), labels(b)))
            max_change = max(max_change, d)
    log(f"Including banned/PED players changes AUCs by at most {max_change:.4f} "
        f"(main pools; WAR, WAR7, JAWS, WAA, SPW, Z)")

    def sp_z2d(ps):
        out = []
        for p in ps:
            cb = career("bat", p["pid"])
            out.append(z2d(cb["WAR"] if cb else 0.0, cb["PA"] if cb else 0.0, p["W"], p["N"]))
        return np.array(out, float)
    log(f"Starting pitchers scored by two-coordinate Z_2D (incl. batting): "
        f"SP AUC = {auc(sp_z2d(SP), labels(SP)):.3f}, "
        f"Contested SP AUC = {auc(sp_z2d(contested(SP)), labels(contested(SP))):.3f}")

    write_csv("hof_auc.csv", ["pool", "n", "hof", "WAR", "WAR7", "JAWS", "S/R_JAWS", "WAA",
                              "SPW", "ZWAR", "best_alpha", "best_alpha_auc", "Z_alpha0.2"], auc_rows)
    write_csv("hof_bootstrap.csv", ["pool", "vs", "ci_lo", "ci_hi"], boot_rows)
    write_csv("hof_cv_alpha.csv", ["pool", "cv_alpha_auc", "alpha05_auc", "alpha0_auc",
                                   "alpha_p10", "alpha_p50", "alpha_p90", "alpha02_auc"], cv_rows)
    write_csv("hof_c_grid.csv", ["c", "auc"], c_rows)
    src = {}
    for p in SP + RP:
        src[p["season_src"]] = src.get(p["season_src"], 0) + 1
    log("")
    log(f"Pitcher season BF for SPW: {src} (scaled = season IPouts x career BF/out)")
    with open(os.path.join(OUT, "hof_summary.txt"), "w") as fh:
        fh.write("\n".join(LOG) + "\n")


if __name__ == "__main__":
    main()
