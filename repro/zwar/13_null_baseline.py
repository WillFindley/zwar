#!/usr/bin/env python3
"""Evidence against a meaningful null (paper Proposition 6, Appendix C, Table 14).

Z_WAR tests H0: r = 0 (replacement level), a null no player in the paper is
ever close to. Here the null rate is raised to a level where the evidence
question is open, using Baseball-Reference's own era-, league- and
position-specific average baseline:

    D       = WAR - WAA          (replacement-to-average credit; a deterministic
                                  function of exposure, position and era)
    Z_{a,l} = (WAR - l * D) / N^a

l = 0 is the replacement-level family Z_a of the paper, l = 1 tests against
league average (Z_{1/2,1} = WAA / sqrt(N)), and l = 2 against a rate twice as
far above replacement as average (about 4 WAR per 650 PA, an All-Star pace).
By Proposition 6, Z_{a,l} rises with extra playing time iff the marginal rate
exceeds (1 - a) * r0 + a * rbar, where r0 = l * D / N.

Analyses:
  1. Share of Hall of Famers whose z = (W - l D) / (sigma sqrt N) exceeds 1.96
     (is the evidence question open?)
  2. Hall of Fame AUC over the (a, l) grid in the pools of Section 5.3; best a for
     each l; bootstrap CI for AUC(Z_{1/2,1}) - AUC(Z_{1/2,0}) and vs WAR
  3. Effective threshold a_eff = a + (1 - a) * l * D / W (Proposition 6 divided
     by rbar) for Hall of Famers at the best (a, l) per l
  4. Expert top-100 lists (Section 5.4) with the coordinate-wise null
Outputs: outputs/null_baseline.csv, outputs/null_baseline_summary.txt
"""
import importlib.util
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from alpha_bench import argmax_idx  # noqa: E402
from common import auc, bootstrap_auc_diff, load_war_daily, write_csv, OUT  # noqa: E402
from pools import hitters, pitchers, hof_eligible  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
SIGMA = 0.065
ALPHAS = np.round(np.arange(0, 1.0001, 0.05), 2)
LAMBDAS = [0.0, 0.25, 0.5, 0.75, 1.0, 1.5, 2.0]
N_BOOT = 2000
LOG = []


def log(msg=""):
    print(msg)
    LOG.append(msg)


def _load(name):
    spec = importlib.util.spec_from_file_location(name.replace(".py", ""), os.path.join(HERE, name))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def score(p, a, lam):
    d = p["W"] - p["WAA"]
    return (p["W"] - lam * d) / max(p["N"], 1.0) ** a


def scores(ps, a, lam):
    return np.array([score(p, a, lam) for p in ps], float)


def labels(ps):
    return np.array([p["hof"] for p in ps], bool)


def hof_part():
    H = hof_eligible(hitters())
    SP = hof_eligible(pitchers("SP"))
    RP = hof_eligible(pitchers("RP"))

    def contested(ps):
        return [p for p in ps if p["W"] >= 40]

    pools = [
        ("Hitters (8 positions pooled)", H),
        ("Starting pitchers", SP),
        ("Relief pitchers", RP),
        ("Hitters + SP pooled", H + SP),
        ("SP + RP pooled", SP + RP),
        ("Contested hitters", contested(H)),
        ("Contested SP", contested(SP)),
        ("Contested hitters + SP", contested(H) + contested(SP)),
    ]

    # 0. Replacement-to-average rate D/N, per 650 PA / 820 BF
    for name, ps, unit in [("hitters", H, 650), ("SP", SP, 820), ("RP", RP, 820)]:
        d = np.array([(p["W"] - p["WAA"]) / p["N"] * unit for p in ps if p["N"] >= 1000])
        log(f"replacement-to-average credit D/N ({name}, N >= 1000): median {np.median(d):.2f} "
            f"per {unit} (10-90%: {np.percentile(d, 10):.2f}-{np.percentile(d, 90):.2f})")

    # 1. Is the evidence question open?
    log("")
    log(f"Share of Hall of Famers with z = (W - l D)/(sigma sqrt N) > 1.96 (sigma = {SIGMA})")
    exp_shares = {
        "Hitters": {0.0: 0.96, 1.0: 0.85, 1.5: 0.60, 2.0: 0.27},
        "SP": {0.0: 1.00, 1.0: 0.88, 1.5: 0.61, 2.0: 0.22},
        "RP": {0.0: 1.00, 1.0: 0.88, 1.5: 0.25, 2.0: 0.00},
    }
    for name, ps in [("Hitters", H), ("SP", SP), ("RP", RP)]:
        hof = [p for p in ps if p["hof"]]
        parts = []
        for lam in (0.0, 1.0, 1.5, 2.0):
            z = scores(hof, 0.5, lam) / SIGMA
            sh = float(np.mean(z > 1.96))
            assert round(sh, 2) == exp_shares[name][lam], f"{name} l={lam}: share {sh}"
            parts.append(f"l={lam:g}: {sh:.0%} (median z {np.median(z):.1f})")
        log(f"  {name:8s} ({len(hof):3d} HOF)  " + "; ".join(parts))

    # 2. AUC over the (alpha, lambda) grid
    log("")
    log("Hall of Fame AUC: Z_{a,l} = (WAR - l (WAR - WAA)) / N^a")
    rows = []
    for name, ps in pools:
        y = labels(ps)
        grid = {(a, lam): auc(scores(ps, a, lam), y) for a in ALPHAS for lam in LAMBDAS}
        for (a, lam), v in grid.items():
            rows.append(["hof", name, a, lam, round(v, 4)])
        best = max(grid, key=grid.get)
        assert best[1] == 0.0, f"{name}: expected overall best at lambda=0, got {best}"
        auc_half = [grid[(0.5, lam)] for lam in LAMBDAS]
        assert all(auc_half[i] > auc_half[i + 1] for i in range(len(auc_half) - 1)), (
            f"{name}: AUC(0.5, lambda) not strictly decreasing: {auc_half}")
        per_l = []
        for lam in LAMBDAS:
            a_b = ALPHAS[argmax_idx([grid[(a, lam)] for a in ALPHAS])]
            if lam == 1.0:
                assert a_b == 0.0, f"{name}: expected best alpha=0 at lambda=1, got {a_b}"
            per_l.append(f"l={lam:g}: a*={a_b:.2f} ({grid[(a_b, lam)]:.3f}), a=.5 {grid[(0.5, lam)]:.3f}")
        log(f"  {name:30s} overall best a={best[0]:.2f}, l={best[1]:g} ({grid[best]:.3f})")
        log("      " + " | ".join(per_l))

    # Bootstrap: does a meaningful null help alpha = 1/2?
    log("")
    log(f"Stratified bootstrap 95% CIs ({N_BOOT} resamples)")
    for name, ps in pools[:5]:
        y = labels(ps)
        z0 = scores(ps, 0.5, 0.0)
        z1 = scores(ps, 0.5, 1.0)
        war = scores(ps, 0.0, 0.0)
        z25 = scores(ps, 0.25, 0.0)
        lo1, hi1 = bootstrap_auc_diff(z1, z0, y, N_BOOT)
        assert hi1 < 0.0, f"{name}: expected WAA/sqrtN - Z_1/2 CI < 0, got [{lo1}, {hi1}]"
        lo2, hi2 = bootstrap_auc_diff(z1, war, y, N_BOOT)
        lo3, hi3 = bootstrap_auc_diff(z1, z25, y, N_BOOT)
        log(f"  {name:30s} AUC(WAA/sqrtN)={auc(z1, y):.3f}: minus Z_1/2 [{lo1:+.3f}, {hi1:+.3f}]; "
            f"minus WAR [{lo2:+.3f}, {hi2:+.3f}]; minus Z_1/4 [{lo3:+.3f}, {hi3:+.3f}]")

    # 3. Effective threshold for Hall of Famers along the per-lambda optimum
    log("")
    log("Effective dilution threshold a_eff = a + (1 - a) l D / W for Hall of Famers "
        "(Proposition 6 / rbar), at the AUC-best a for each l")
    for name, ps in [("Hitters (8 positions pooled)", H), ("Starting pitchers", SP)]:
        y = labels(ps)
        hof = [p for p in ps if p["hof"] and p["W"] > 0]
        parts = []
        for lam in LAMBDAS:
            a_b = ALPHAS[argmax_idx([auc(scores(ps, a, lam), y) for a in ALPHAS])]
            eff = [a_b + (1 - a_b) * lam * (p["W"] - p["WAA"]) / p["W"] for p in hof]
            parts.append(f"l={lam:g}: a*={a_b:.2f} a_eff median {np.median(eff):.2f}")
        log(f"  {name:30s} " + " | ".join(parts))
        eff_half = [0.5 + 0.5 * 1.0 * (p["W"] - p["WAA"]) / p["W"] for p in hof]
        assert round(float(np.median(eff_half)), 2) == 0.74
        log(f"  {'':30s} WAA/sqrtN (a=.5, l=1): a_eff median {np.median(eff_half):.2f} "
            f"(10-90%: {np.percentile(eff_half, 10):.2f}-{np.percentile(eff_half, 90):.2f})")
    return rows


def expert_part():
    m11 = _load("11_expert_rankings.py")
    from scipy.stats import spearmanr
    lists = m11.load_lists()
    bat, pit = load_war_daily("bat"), load_war_daily("pitch")
    rows = []
    log("")
    log("Expert top-100 lists: coordinate-wise Z_{a,l}, signed quadrature (Spearman / AUC)")
    for lst, cutoff in m11.LISTS.items():
        car = m11.careers_through(cutoff)
        # add coordinate WAA through the cutoff
        for pid, p in car.items():
            bs = bat.get(pid, {"seasons": {}})["seasons"]
            ps = pit.get(pid, {"seasons": {}})["seasons"]
            p["a_pos"] = sum(s["WAA"] for y, s in bs.items() if y <= cutoff)
            p["a_pit"] = sum(s["WAA"] for y, s in ps.items() if y <= cutoff)
        entries = lists[lst]
        listed = {pid for _, pid, _ in entries}
        uni = [pid for pid, p in car.items() if p["war"] >= m11.MIN_WAR or pid in listed]
        y = np.array([pid in listed for pid in uni])
        ranks = np.array([r for r, _, _ in entries], float)
        lp = [pid for _, pid, _ in entries]

        def zz(p, a, lam):
            sp = (p["w_pos"] - lam * (p["w_pos"] - p["a_pos"])) / max(p["pa"], 1.0) ** a
            st = (p["w_pit"] - lam * (p["w_pit"] - p["a_pit"])) / max(p["bf"], 1.0) ** a
            i = sp * abs(sp) + st * abs(st)
            return math.copysign(math.sqrt(abs(i)), i)

        grid = {}
        for a in ALPHAS:
            for lam in LAMBDAS:
                su = np.array([zz(car[pid], a, lam) for pid in uni])
                sl = np.array([zz(car[pid], a, lam) for pid in lp])
                rho = float(spearmanr(-ranks, sl)[0])
                grid[(a, lam)] = (rho, auc(su, y))
                rows.append(["expert", lst, a, lam, round(rho, 4), round(grid[(a, lam)][1], 4)])
        log(f"  {lst}:")
        for lam in LAMBDAS:
            a_r = ALPHAS[argmax_idx([grid[(a, lam)][0] for a in ALPHAS])]
            a_u = ALPHAS[argmax_idx([grid[(a, lam)][1] for a in ALPHAS])]
            log(f"    l={lam:<4g} a=.5: {grid[(0.5, lam)][0]:.3f} / {grid[(0.5, lam)][1]:.3f}   "
                f"best a (rho) {a_r:.2f} ({grid[(a_r, lam)][0]:.3f})   best a (AUC) {a_u:.2f} "
                f"({grid[(a_u, lam)][1]:.3f})")
        best_r = max(grid, key=lambda k: grid[k][0])
        best_u = max(grid, key=lambda k: grid[k][1])
        log(f"    overall best: rho a={best_r[0]:.2f}, l={best_r[1]:g} ({grid[best_r][0]:.3f}); "
            f"AUC a={best_u[0]:.2f}, l={best_u[1]:g} ({grid[best_u][1]:.3f})")
    return rows


def main():
    rows = hof_part()
    erows = expert_part()
    write_csv("null_baseline.csv", ["analysis", "pool", "alpha", "lambda", "hof_auc_or_expert_spearman",
                                    "expert_auc"],
              [r + [""] if len(r) == 5 else r for r in rows] + erows)
    with open(os.path.join(OUT, "null_baseline_summary.txt"), "w") as fh:
        fh.write("\n".join(LOG) + "\n")


if __name__ == "__main__":
    main()
