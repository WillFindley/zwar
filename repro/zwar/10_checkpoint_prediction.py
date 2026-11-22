#!/usr/bin/env python3
"""Predictive test of early-career checkpoint scores (paper Section 5.5 / Table 6,
"Forecasts and the scaling of targets").

For every player whose career began in 1901 or later, ended by 2023 and
includes no Negro Leagues season, take the end of his k-th season in a role
(k = 3 or 5; a season counts if it has PA > 0 for hitters or IPouts > 0 for
pitchers) as the checkpoint. Players need at least 1,000 PA (hitters) or
600 BF (pitchers) by the checkpoint. Hitters are players with fewer than 100
career innings pitched; pitchers are scored on pitching WAR alone.

Checkpoint predictors: Z_alpha = W / N^alpha over an alpha grid, and an
empirical Bayes rate (W + N0 r0) / (N + N0) with prior mean r0 and N0 = sigma^2 / tau^2 from
the method of moments (sigma = 0.065 WAR / sqrt(event), Section 3.3).
Pitcher exposure is IPouts x 1.4; because the factor is constant it does not
change any ranking within this test.

Outcomes:
  * rest-of-career WAR (Spearman, all eligible players)
  * rest-of-career rate WAR / N (Spearman, players with at least the same
    minimum exposure after the checkpoint)
  * Hall of Fame election (AUC; careers ending by 2010, bans / PED cases excluded)
Outputs: outputs/checkpoint_prediction.csv, outputs/checkpoint_summary.txt
"""
import os
import sys

import numpy as np
from scipy.stats import spearmanr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import (HITTER_POS, PITCHER_POS, HOF_EXCLUDE, auc, bootstrap_auc_diff,  # noqa: E402
                    load_jaws, load_war_daily, write_csv, OUT)

NGL = {"NN2", "NNL", "NAL", "ECL", "NSL", "EWL", "ANL"}
ALPHAS = np.round(np.arange(0, 1.0001, 0.05), 2)
FIRST, LAST_DONE, LAST_HOF = 1901, 2023, 2010
MIN_N = {"H": 1000.0, "P": 600.0}
BF_PER_OUT = 1.4
SIGMA = 0.065
N_BOOT = 2000
LOG = []


def spearman(a, b):
    """Spearman correlation with average ranks for ties (order-independent)."""
    return float(spearmanr(a, b)[0])


def log(msg=""):
    print(msg)
    LOG.append(msg)


def ngl_players():
    import csv
    from common import RAW
    out = set()
    for kind in ("bat", "pitch"):
        with open(os.path.join(RAW, f"war_daily_{kind}.txt"), encoding="utf-8") as fh:
            for r in csv.DictReader(fh):
                if r["lg_ID"] in NGL:
                    out.add(r["player_ID"])
    return out


def hof_flags():
    hof = set()
    for pos in HITTER_POS + PITCHER_POS:
        hof |= {d["pid"] for d in load_jaws(pos) if d["hof"]}
    return hof


def build(role, k):
    bat, pit = load_war_daily("bat"), load_war_daily("pitch")
    excl, hof = ngl_players(), hof_flags()
    out = []
    for pid in sorted(set(bat) | set(pit)):
        if pid in excl:
            continue
        years = set(bat.get(pid, {"seasons": {}})["seasons"]) | set(pit.get(pid, {"seasons": {}})["seasons"])
        if min(years) < FIRST or max(years) > LAST_DONE:
            continue
        outs_career = sum(s["IPouts"] for s in pit.get(pid, {"seasons": {}})["seasons"].values())
        if role == "H":
            if pid not in bat or outs_career >= 300:
                continue
            seas = sorted((y, s["WAR"], s["PA"]) for y, s in bat[pid]["seasons"].items() if s["PA"] > 0)
        else:
            if pid not in pit:
                continue
            seas = sorted((y, s["WAR"], s["IPouts"] * BF_PER_OUT)
                          for y, s in pit[pid]["seasons"].items() if s["IPouts"] > 0)
        if len(seas) < k:
            continue
        w0 = sum(w for _, w, _ in seas[:k])
        n0 = sum(n for _, _, n in seas[:k])
        if n0 < MIN_N[role]:
            continue
        w1 = sum(w for _, w, _ in seas[k:])
        n1 = sum(n for _, _, n in seas[k:])
        out.append(dict(pid=pid, W=w0, N=n0, fW=w1, fN=n1, last=max(years),
                        hof=pid in hof, excl=pid in HOF_EXCLUDE))
    return out


def eb_rate(players):
    r = np.array([p["W"] / p["N"] for p in players])
    n = np.array([p["N"] for p in players])
    tau2 = max(r.var() - np.mean(SIGMA ** 2 / n), 1e-12)
    n0 = SIGMA ** 2 / tau2
    rbar = float(np.sum(r * n) / np.sum(n))
    return (r * n + n0 * rbar) / (n + n0), n0


def boot_rho_diff(a, b, y, seed=11):
    rng = np.random.default_rng(seed)
    a, b, y = map(np.asarray, (a, b, y))
    d = []
    for _ in range(N_BOOT):
        i = rng.integers(0, len(y), len(y))
        d.append(spearman(a[i], y[i]) - spearman(b[i], y[i]))
    return tuple(np.percentile(d, [2.5, 97.5]))


def zs(players, a):
    return np.array([p["W"] / p["N"] ** a for p in players])


def main():
    rows = []
    for role, label in (("H", "Hitters"), ("P", "Pitchers")):
        for k in (3, 5):
            P = build(role, k)
            fut = np.array([p["fW"] for p in P])
            R = [p for p in P if p["fN"] >= MIN_N[role]]
            frate = np.array([p["fW"] / p["fN"] for p in R])
            H = [p for p in P if p["last"] <= LAST_HOF and not p["excl"]]
            yh = np.array([p["hof"] for p in H])
            eb_all, n0 = eb_rate(P)
            eb_r = eb_all[[i for i, p in enumerate(P) if p["fN"] >= MIN_N[role]]]
            eb_h = eb_all[[i for i, p in enumerate(P) if p["last"] <= LAST_HOF and not p["excl"]]]
            log(f"== {label}, first {k} seasons (>= {MIN_N[role]:.0f} {'PA' if role == 'H' else 'BF'}): "
                f"n = {len(P)}; future-rate subset {len(R)}; HOF subset {len(H)} ({int(yh.sum())} HOF); "
                f"EB N0 = {n0:.0f}")
            curve = {}
            for a in ALPHAS:
                s_all, s_r, s_h = zs(P, a), zs(R, a), zs(H, a)
                curve[a] = (spearman(s_all, fut), spearman(s_r, frate), auc(s_h, yh))
                rows.append([label, k, a, len(P), round(curve[a][0], 4), len(R), round(curve[a][1], 4),
                             len(H), int(yh.sum()), round(curve[a][2], 4)])
            eb = (spearman(eb_all, fut), spearman(eb_r, frate), auc(eb_h, yh))
            rows.append([label, k, "EB", len(P), round(eb[0], 4), len(R), round(eb[1], 4),
                         len(H), int(yh.sum()), round(eb[2], 4)])
            for j, name in enumerate(["future WAR (Spearman)", "future rate (Spearman)", "HOF (AUC)"]):
                best = max(ALPHAS, key=lambda a: curve[a][j])
                log(f"  {name:24s} a=0 {curve[0.0][j]:.3f}  a=0.25 {curve[0.25][j]:.3f}  "
                    f"a=0.5 {curve[0.5][j]:.3f}  a=1 {curve[1.0][j]:.3f}  best a={best:.2f} "
                    f"({curve[best][j]:.3f})  EB {eb[j]:.3f}")
            z5, z0, z1 = zs(P, 0.5), zs(P, 0.0), zs(P, 1.0)
            lo, hi = boot_rho_diff(z5, z0, fut)
            log(f"  future WAR: rho(a=0.5) - rho(a=0) 95% CI [{lo:+.3f}, {hi:+.3f}]")
            r5, r1 = zs(R, 0.5), zs(R, 1.0)
            lo, hi = boot_rho_diff(r5, r1, frate)
            lo2, hi2 = boot_rho_diff(r5, eb_r, frate)
            log(f"  future rate: rho(a=0.5) - rho(a=1) [{lo:+.3f}, {hi:+.3f}]; "
                f"rho(a=0.5) - rho(EB) [{lo2:+.3f}, {hi2:+.3f}]")
            lo, hi = bootstrap_auc_diff(zs(H, 0.5), zs(H, 0.0), yh, n_boot=N_BOOT)
            lo2, hi2 = bootstrap_auc_diff(zs(H, 0.5), zs(H, 1.0), yh, n_boot=N_BOOT)
            log(f"  HOF: AUC(a=0.5) - AUC(a=0) [{lo:+.3f}, {hi:+.3f}]; AUC(a=0.5) - AUC(a=1) "
                f"[{lo2:+.3f}, {hi2:+.3f}]")
            log("  curve (futWAR/futRate/HOF): " + "  ".join(
                f"{a:.2f}:{curve[a][0]:.3f}/{curve[a][1]:.3f}/{curve[a][2]:.3f}"
                for a in ALPHAS if round(a * 20) % 2 == 0))
            log()
    write_csv("checkpoint_prediction.csv",
              ["role", "k_seasons", "alpha", "n", "rho_future_WAR", "n_rate", "rho_future_rate",
               "n_hof_pool", "n_hof", "auc_hof"], rows)
    with open(os.path.join(OUT, "checkpoint_summary.txt"), "w") as fh:
        fh.write("\n".join(LOG) + "\n")


if __name__ == "__main__":
    main()
