#!/usr/bin/env python3
"""Compare the alpha family with two published expert rankings of the 100
greatest players (paper Section 5.4, Table 5, "Expert rankings").

Lists (data/expert/expert_lists.csv; names as published, mapped to B-Ref IDs):
  * tsn1998  - The Sporting News, "Baseball's 100 Greatest Players" (1998).
               Careers are truncated after the 1997 season.
  * espn2022 - ESPN, "Top 100 MLB players of all time" (1-3 February 2022).
               Careers are truncated after the 2021 season.

For each list, every player in B-Ref's season WAR files (MLB and Negro
Leagues) is scored on his career through the cutoff season:
  * WAR    = position WAR (all batting rows) + pitching WAR
  * JAWS   = (WAR + WAR7) / 2, WAR7 = best seven seasons of combined WAR
  * Z_alpha = the value-consistent l_gamma combination of the coordinate scores
             Z_k = W_k / N_k^alpha (common.z2d_lgamma, gamma = 1/(1 - alpha)):
             Z = sgn(I) |I|^(1/gamma), I = sum_k sgn(Z_k) |Z_k|^gamma; alpha = 1 is
             the gamma -> infinity limit (the coordinate with the larger |Z_k|).
             alpha = 1/2 (gamma = 2) is the paper's two-coordinate Z_WAR (signed
             quadrature, Equation 10) and is unchanged. N_pos = PA, N_pitch = BF.
             The previous default for alpha != 1/2 -- signed quadrature of the
             Z_k at every alpha -- is kept for reference in
             outputs/expert_rankings_quadrature.csv.
Pitcher BF per season is exact where a cached B-Ref pitching table exists and
otherwise IPouts x 1.4 (4.2 BF per inning).

Outcomes:
  * Spearman correlation between expert rank and metric among the 100 listed players
  * AUC for list membership within the universe (players with >= MIN_WAR career
    WAR through the cutoff, plus every listed player)
  * overlap between the metric's top 100 and the list; pitchers in each top 100
Outputs: outputs/expert_rankings.csv, outputs/expert_rankings_quadrature.csv,
         outputs/expert_summary.txt
"""
import csv
import math
import os
import sys
from collections import defaultdict

import numpy as np
from scipy.stats import spearmanr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import (ROOT, auc, bootstrap_auc_diff, has_season_bf, load_player_page,  # noqa: E402
                    load_war_daily, write_csv, z2d_lgamma, OUT)

LISTS = {"tsn1998": 1997, "espn2022": 2021}
ALPHAS = np.round(np.arange(0, 1.0001, 0.05), 2)
MIN_WAR = 15.0
BF_PER_OUT = 1.4
C_BWAR = 59 / 41
N_BOOT = 2000
LOG = []


def spearman(a, b):
    """Spearman correlation with average ranks for ties (order-independent)."""
    return float(spearmanr(a, b)[0])


def log(msg=""):
    print(msg)
    LOG.append(msg)


def load_lists():
    out = defaultdict(list)
    with open(os.path.join(ROOT, "data", "expert", "expert_lists.csv"), encoding="utf-8") as fh:
        for r in csv.DictReader(fh):
            out[r["list"]].append((int(r["rank"]), r["player_ID"], r["name_as_published"]))
    return out


_BF_CACHE = {}


def season_bf(pid, seasons):
    """{year: BF} for a pitcher: exact from a cached pitching table, else outs x 1.4."""
    if pid not in _BF_CACHE:
        exact = {}
        if has_season_bf(pid):
            exact = {y: s.get("BF", 0.0) for y, s in load_player_page(pid)["pitch"].items()}
        _BF_CACHE[pid] = {y: (exact[y] if exact.get(y) else s["IPouts"] * BF_PER_OUT)
                          for y, s in seasons.items()}
    return _BF_CACHE[pid]


def careers_through(year):
    bat, pit = load_war_daily("bat"), load_war_daily("pitch")
    res = {}
    for pid in sorted(set(bat) | set(pit)):
        bs = {y: s for y, s in bat.get(pid, {"seasons": {}})["seasons"].items() if y <= year}
        ps = {y: s for y, s in pit.get(pid, {"seasons": {}})["seasons"].items() if y <= year}
        if not bs and not ps:
            continue
        w_pos = sum(s["WAR"] for s in bs.values())
        pa = sum(s["PA"] for s in bs.values())
        w_pit = sum(s["WAR"] for s in ps.values())
        bf = 0.0
        if ps:
            bfs = season_bf(pid, pit[pid]["seasons"]) if has_season_bf(pid) else \
                {y: s["IPouts"] * BF_PER_OUT for y, s in ps.items()}
            bf = sum(v for y, v in bfs.items() if y <= year)
        by_year = defaultdict(float)
        for y, s in bs.items():
            by_year[y] += s["WAR"]
        for y, s in ps.items():
            by_year[y] += s["WAR"]
        war7 = sum(sorted(by_year.values(), reverse=True)[:7])
        res[pid] = dict(w_pos=w_pos, pa=pa, w_pit=w_pit, bf=bf, war=w_pos + w_pit,
                        jaws=(w_pos + w_pit + war7) / 2, pitcher=w_pit > w_pos)
    return res


def z_unified(p, alpha, c=1.0):
    """Signed quadrature of the coordinate scores at any alpha (previous default;
    identical to z_two_way at alpha = 1/2). Kept for reference and for script 14."""
    i = (p["w_pos"] * abs(p["w_pos"]) / max(p["pa"], 1.0) ** (2 * alpha)
         + c * c * p["w_pit"] * abs(p["w_pit"]) / max(p["bf"], 1.0) ** (2 * alpha))
    return math.copysign(math.sqrt(abs(i)), i)


def z_two_way(p, alpha, c=1.0):
    """Default two-coordinate score: the l_gamma rule (common.z2d_lgamma) with
    the pitcher coordinate scaled by c. alpha = 1 (gamma = infinity) is the limit
    of the rule: the coordinate score Z_k = W_k / N_k with the larger |Z_k|."""
    if alpha >= 1.0 - 1e-12:
        zs = (p["w_pos"] / max(p["pa"], 1.0), c * p["w_pit"] / max(p["bf"], 1.0))
        return max(zs, key=abs)
    return z2d_lgamma(p["w_pos"], p["pa"], c * p["w_pit"], p["bf"], alpha)


def z_radon(p, alpha, c=1.0):
    """l_gamma combination with gamma = 1/(1 - alpha) (Appendix A / Proposition 2)."""
    g = 1.0 / (1.0 - alpha)
    i = (math.copysign(abs(p["w_pos"]) ** g, p["w_pos"]) / max(p["pa"], 1.0) ** (g - 1.0)
         + (c ** g) * math.copysign(abs(p["w_pit"]) ** g, p["w_pit"]) / max(p["bf"], 1.0) ** (g - 1.0))
    return math.copysign(abs(i) ** (1.0 / g), i)


def boot_spearman_diff(rank, a, b, seed=7):
    rng = np.random.default_rng(seed)
    rank, a, b = map(np.asarray, (rank, a, b))
    d = []
    for _ in range(N_BOOT):
        idx = rng.integers(0, len(rank), len(rank))
        d.append(spearman(-rank[idx], a[idx]) - spearman(-rank[idx], b[idx]))
    return tuple(np.percentile(d, [2.5, 97.5]))


def main():
    lists = load_lists()
    rows, rows_q = [], []
    for lst, cutoff in LISTS.items():
        entries = lists[lst]
        listed = {pid for _, pid, _ in entries}
        car = careers_through(cutoff)
        uni = [pid for pid, p in car.items() if p["war"] >= MIN_WAR or pid in listed]
        below = sorted((car[pid]["war"], name) for _, pid, name in entries if car[pid]["war"] < MIN_WAR)
        y = np.array([pid in listed for pid in uni])
        ranks = np.array([r for r, _, _ in entries], float)
        lp = [pid for _, pid, _ in entries]

        metrics = {"WAR": lambda p: p["war"], "JAWS": lambda p: p["jaws"]}
        for a in ALPHAS:
            metrics[f"Z{a:.2f}"] = (lambda a: lambda p: z_two_way(p, a))(a)
        metrics["Z0.50_c59/41"] = lambda p: z_two_way(p, 0.5, C_BWAR)
        for c in (1.1, 1.2, 1.3):
            metrics[f"Z0.50_c{c:.1f}"] = (lambda c: lambda p: z_two_way(p, 0.5, c))(c)

        log(f"== {lst} (careers through {cutoff}); universe {len(uni)} players "
            f"(career WAR >= {MIN_WAR:g} or listed); listed below threshold: "
            + (", ".join(f"{n} {w:.1f}" for w, n in below) or "none"))
        n_pitch_list = sum(car[pid]["pitcher"] for pid in lp)
        res = {}
        for name, f in metrics.items():
            s_uni = np.array([f(car[pid]) for pid in uni])
            s_list = np.array([f(car[pid]) for pid in lp])
            rho = spearman(-ranks, s_list)
            a_ = auc(s_uni, y)
            top = [uni[i] for i in np.argsort(-s_uni, kind="mergesort")[:100]]
            overlap = len(set(top) & listed)
            n_pitch_top = sum(car[pid]["pitcher"] for pid in top)
            res[name] = (rho, a_, overlap, n_pitch_top, s_uni, s_list)
            rows.append([lst, name, round(rho, 4), round(a_, 4), overlap, n_pitch_top, n_pitch_list])
        for name in ["WAR", "JAWS", "Z0.00", "Z0.25", "Z0.50", "Z0.75", "Z1.00", "Z0.50_c1.1", "Z0.50_c1.2", "Z0.50_c1.3", "Z0.50_c59/41"]:
            rho, a_, ov, npt, _, _ = res[name]
            log(f"  {name:14s} Spearman(list order) {rho:.3f}   membership AUC {a_:.3f}   "
                f"top-100 overlap {ov:3d}   pitchers in top 100 {npt:2d} (list: {n_pitch_list})")
        zs = [k for k in res if k.startswith("Z") and "_" not in k]
        best_rho = max(zs, key=lambda k: res[k][0])
        best_auc = max(zs, key=lambda k: res[k][1])
        best_ov = max(zs, key=lambda k: (res[k][2], -abs(float(k[1:]) - 0.5)))
        log(f"  best alpha: Spearman {best_rho[1:]} ({res[best_rho][0]:.3f}); "
            f"AUC {best_auc[1:]} ({res[best_auc][1]:.3f}); overlap {best_ov[1:]} ({res[best_ov][2]})")
        log("  alpha curve (Spearman / AUC): " + "  ".join(
            f"{k[1:]}:{res[k][0]:.3f}/{res[k][1]:.3f}" for k in zs if float(k[1:]) * 20 % 2 == 0))
        radon_parts = []
        for a in (0.0, 0.15, 0.25, 0.50):
            su = np.array([z_radon(car[pid], a) for pid in uni])
            sl = np.array([z_radon(car[pid], a) for pid in lp])
            radon_parts.append(f"{a:.2f}:{spearman(-ranks, sl):.3f}/{auc(su, y):.3f}")
        log("  l_gamma (gamma=1/(1-a)) check (Spearman / AUC): " + "  ".join(radon_parts))
        quad_parts = []
        for a in ALPHAS:
            su = np.array([z_unified(car[pid], a) for pid in uni])
            sl = np.array([z_unified(car[pid], a) for pid in lp])
            rho_q, auc_q = spearman(-ranks, sl), auc(su, y)
            top = [uni[i] for i in np.argsort(-su, kind="mergesort")[:100]]
            rows_q.append([lst, f"Z{a:.2f}", round(rho_q, 4), round(auc_q, 4), len(set(top) & listed),
                           sum(car[pid]["pitcher"] for pid in top), n_pitch_list])
            if round(a * 20) % 2 == 0:
                quad_parts.append(f"{a:.2f}:{rho_q:.3f}/{auc_q:.3f}")
        log("  previous default (signed quadrature at every alpha), Spearman / AUC: " + "  ".join(quad_parts))
        for m1, m2 in [("Z0.50", "WAR"), ("Z0.50", "JAWS"), ("Z0.25", "WAR"), ("Z0.25", "Z0.50"),
                       ("Z0.50_c1.2", "JAWS"), ("Z0.50_c1.2", "Z0.50")]:
            lo, hi = boot_spearman_diff(ranks, res[m1][5], res[m2][5])
            alo, ahi = bootstrap_auc_diff(res[m1][4], res[m2][4], y, n_boot=N_BOOT)
            log(f"  {m1} - {m2}: Spearman diff 95% CI [{lo:+.3f}, {hi:+.3f}]; "
                f"AUC diff 95% CI [{alo:+.3f}, {ahi:+.3f}]")
        log()
    write_csv("expert_rankings.csv", ["list", "metric", "spearman_list_order", "membership_auc",
                                      "top100_overlap", "pitchers_in_top100", "pitchers_in_list"], rows)
    write_csv("expert_rankings_quadrature.csv", ["list", "metric", "spearman_list_order", "membership_auc",
                                                 "top100_overlap", "pitchers_in_top100", "pitchers_in_list"],
              rows_q)
    with open(os.path.join(OUT, "expert_summary.txt"), "w") as fh:
        fh.write("\n".join(LOG) + "\n")


if __name__ == "__main__":
    main()
