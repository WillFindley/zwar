#!/usr/bin/env python3
"""Reproduce the alpha-sensitivity ranks (paper Section 6.6, Table 12) and Spearman
correlations within the Baseball-Reference JAWS-page pools.

Hitters: all players on the eight hitter JAWS pages, position-player WAR / PA.
Pitchers: all players on the SP and RP JAWS pages, pitching WAR / BF.
Outputs: outputs/alpha_ranks.csv
"""
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import z_alpha, spearman, write_csv  # noqa: E402
from pools import hitters, pitchers  # noqa: E402

ALPHAS = [0.0, 0.2, 0.25, 0.3, 0.4, 0.5, 0.6, 0.7, 1.0]

PAPER = {  # name: ranks at ALPHAS as printed in the paper (Table 12)
    "Babe Ruth": [2, 1, 1, 1, 1, 1, 1, 1, 2], "Barry Bonds": [1, 2, 2, 2, 2, 2, 2, 2, 6],
    "Willie Mays": [3, 3, 3, 3, 3, 3, 3, 3, 10], "Ted Williams": [11, 10, 9, 9, 9, 7, 6, 6, 11],
    "Henry Aaron": [5, 5, 5, 5, 7, 9, 9, 10, 37], "Mike Trout": [30, 21, 21, 20, 18, 18, 15, 12, 18],
    "Jackie Robinson": [106, 70, 61, 52, 48, 40, 35, 33, 30], "Josh Gibson": [346, 197, 169, 142, 88, 50, 32, 17, 1],
    "Pete Rose": [41, 61, 71, 85, 115, 142, 192, 274, 885],
    "Walter Johnson": [2, 2, 2, 1, 1, 1, 1, 2, 36], "Roger Clemens": [3, 3, 3, 3, 3, 2, 2, 3, 32],
    "Cy Young": [1, 1, 1, 2, 2, 3, 3, 6, 81], "Pedro Martinez": [17, 11, 11, 11, 8, 7, 6, 5, 15],
    "Mariano Rivera": [80, 34, 30, 25, 13, 9, 4, 1, 1], "Clayton Kershaw": [28, 20, 17, 14, 12, 11, 10, 7, 30],
    "Greg Maddux": [8, 9, 9, 9, 10, 12, 13, 17, 129], "Nolan Ryan": [20, 28, 28, 30, 36, 46, 58, 95, 413],
    "Dennis Eckersley": [54, 53, 53, 51, 52, 52, 55, 69, 186], "Billy Wagner": [340, 245, 219, 197, 138, 100, 59, 30, 13],
}


def ranks(pool, alpha):
    s = np.array([z_alpha(p["W"], p["N"], alpha) for p in pool])
    order = np.argsort(-s, kind="mergesort")
    r = np.empty(len(s), int)
    r[order] = np.arange(1, len(s) + 1)
    return r, s


def main():
    pools = {"hitters": hitters(), "pitchers": pitchers("SP") + pitchers("RP")}
    print(f"pool sizes: hitters {len(pools['hitters'])} (paper 4,000), "
          f"pitchers {len(pools['pitchers'])} (paper 1,000)")
    out = []
    for kind, pool in pools.items():
        rk = {a: ranks(pool, a) for a in ALPHAS}
        by_name = {}
        for i, p in enumerate(pool):
            key = p["name"].replace("í", "i").replace("Pedro Martínez", "Pedro Martinez")
            by_name.setdefault(key, i)
        for name, paper in PAPER.items():
            if name not in by_name:
                continue
            i = by_name[name]
            ours = [int(rk[a][0][i]) for a in ALPHAS]
            diff = max(abs(x - y) for x, y in zip(ours, paper))
            flag = "" if diff <= 2 else f"   <-- max diff {diff}"
            print(f"{name:18s} ours {ours}\n{'':18s} paper{paper}{flag}")
            out.append([kind, name] + ours + paper + [diff])
        # Spearman correlations among the top 100 at alpha = 0.5
        r05, _ = rk[0.5]
        top = np.flatnonzero(r05 <= 100)
        for a in (0.4, 0.6):
            rho = spearman(rk[0.5][1][top], rk[a][1][top])
            print(f"{kind}: Spearman(top-100 at 0.5) alpha 0.5 vs {a}: {rho:.3f}")
    write_csv("alpha_ranks.csv", ["pool", "player"] + [f"ours_{a}" for a in ALPHAS]
              + [f"paper_{a}" for a in ALPHAS] + ["max_abs_diff"], out)


if __name__ == "__main__":
    main()
