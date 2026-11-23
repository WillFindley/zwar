#!/usr/bin/env python3
"""Seasons versus events as the exposure unit of the value reading
(paper Proposition 4, Appendix D, Table 15).

Under convex season value s^gamma with equal seasons, total value ranks careers
by W / S^alpha, where S is the number of seasons and alpha = 1 - 1/gamma. The
paper's family uses events, W / N^alpha with N = PA or BF; the two coincide
only when every career has the same exposure per season (W/N^alpha =
E^-alpha W/S^alpha). This script compares the two units on the paper's
external benchmarks:

  * Hall of Fame AUC in the pools of Table 4 (S = seasons with any exposure in
    the role, and S_100 = seasons with at least 100 PA / BF, minimum 1);
  * the two expert top-100 lists of Section 5.4 (two-way records combined by
    the signed quadrature of Equation (10) with S_k in place of N_k).

Outputs: outputs/season_unit.csv, outputs/season_unit_summary.txt
"""
import importlib.util
import math
import os
import sys

import numpy as np
from scipy.stats import spearmanr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import auc, bootstrap_auc_diff, load_war_daily, write_csv, OUT  # noqa: E402
from pools import hitters, pitchers, hof_eligible  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
ALPHAS = np.round(np.arange(0, 1.0001, 0.05), 2)
A_VALUE = 0.2
N_BOOT = 2000
MIN_EVENTS = 100
LOG = []


def log(msg=""):
    print(msg)
    LOG.append(msg)


def _load_module(fname, name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(HERE, fname))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def season_counts(kind, pid, last=None, min_events=0):
    p = load_war_daily(kind).get(pid)
    if not p:
        return 0
    key = "PA" if kind == "bat" else "IPouts"
    scale = 1.0 if kind == "bat" else 1.4   # outs -> BF for the 100-event cut
    n = 0
    for y, s in p["seasons"].items():
        if last is not None and y > last:
            continue
        e = s[key] * scale
        if e > 0 and e >= min_events:
            n += 1
    return n


def attach_seasons(players, kind):
    for p in players:
        p["S"] = max(season_counts(kind, p["pid"]), 1)
        p["S100"] = max(season_counts(kind, p["pid"], min_events=MIN_EVENTS), 1)
    return players


def score(ps, unit, alpha):
    if unit == "N":
        return np.array([p["W"] / max(p["N"], 1.0) ** alpha for p in ps])
    return np.array([p["W"] / p[unit] ** alpha for p in ps])


def best(ps, y, unit):
    vals = [(a, auc(score(ps, unit, a), y)) for a in ALPHAS]
    return max(vals, key=lambda t: (t[1], -t[0]))


def main():
    H = attach_seasons(hof_eligible(hitters()), "bat")
    SP = attach_seasons(hof_eligible(pitchers("SP")), "pitch")
    RP = attach_seasons(hof_eligible(pitchers("RP")), "pitch")

    def contested(ps):
        return [p for p in ps if p["W"] >= 40]

    pools = [("Hitters (8 positions pooled)", H), ("Starting pitchers", SP),
             ("Relief pitchers", RP), ("Hitters + SP pooled", H + SP), ("SP + RP pooled", SP + RP),
             ("Contested hitters", contested(H)), ("Contested SP", contested(SP)),
             ("Contested hitters + SP", contested(H) + contested(SP))]

    # Typical season exposure by role (median N/S among players with >= 1,000 events)
    for name, ps in [("hitters", H), ("SP", SP), ("RP", RP)]:
        e = [p["N"] / p["S"] for p in ps if p["N"] >= 1000]
        log(f"median events per season ({name}, >= 1,000 events): {np.median(e):.0f}")
    pre = [p["N"] / p["S"] for p in SP if p["N"] >= 1000 and p["year_min"] < 1920]
    post = [p["N"] / p["S"] for p in SP if p["N"] >= 1000 and p["year_min"] >= 1980]
    log(f"median BF per season, SP debuting before 1920: {np.median(pre):.0f}; 1980 or later: {np.median(post):.0f}")
    log("")

    rows = []
    log(f"Hall of Fame AUC: events (W/N^a) vs seasons (W/S^a, W/S100^a)")
    log(f"{'pool':32s} {'N a=.2':>7s} {'S a=.2':>7s} {'S100 .2':>7s}  "
        f"{'best N':>12s} {'best S':>12s} {'best S100':>12s}  S-N at a=.2 (95% CI)")
    for name, ps in pools:
        y = np.array([p["hof"] for p in ps], bool)
        r = {u: auc(score(ps, u, A_VALUE), y) for u in ("N", "S", "S100")}
        b = {u: best(ps, y, u) for u in ("N", "S", "S100")}
        lo, hi = bootstrap_auc_diff(score(ps, "S", A_VALUE), score(ps, "N", A_VALUE), y, N_BOOT)
        log(f"{name:32s} {r['N']:7.3f} {r['S']:7.3f} {r['S100']:7.3f}  "
            + " ".join(f"{b[u][0]:.2f} ({b[u][1]:.3f})" for u in ("N", "S", "S100"))
            + f"  [{lo:+.3f}, {hi:+.3f}]")
        rows.append([name, len(ps), int(y.sum()), round(r["N"], 4), round(r["S"], 4), round(r["S100"], 4),
                     b["N"][0], round(b["N"][1], 4), b["S"][0], round(b["S"][1], 4),
                     b["S100"][0], round(b["S100"][1], 4), round(lo, 4), round(hi, 4)])

    # Relief Hall of Famers within the combined SP + RP list
    SPRP = SP + RP
    log("")
    log(f"SP + RP pooled: ranks of relief Hall of Famers at alpha = {A_VALUE}")
    for u in ("N", "S"):
        s = score(SPRP, u, A_VALUE)
        order = (-s).argsort(kind="mergesort").argsort(kind="mergesort")
        ranks = sorted(int(order[i]) + 1 for i, p in enumerate(SPRP) if p["hof"] and p["role"] == "RP")
        log(f"  {'events' if u == 'N' else 'seasons':8s} {ranks}")

    # Expert lists
    ex = _load_module("11_expert_rankings.py", "expert11")
    lists = ex.load_lists()
    log("")
    log("Expert top-100 lists (Spearman with list order / membership AUC)")
    for lst, cutoff in ex.LISTS.items():
        entries = lists[lst]
        listed = {pid for _, pid, _ in entries}
        car = ex.careers_through(cutoff)
        uni = [pid for pid, p in car.items() if p["war"] >= ex.MIN_WAR or pid in listed]
        for pid in uni:
            car[pid]["s_pos"] = season_counts("bat", pid, last=cutoff)
            car[pid]["s_pit"] = season_counts("pitch", pid, last=cutoff)
        y = np.array([pid in listed for pid in uni])
        ranks = np.array([r for r, _, _ in entries], float)
        lp = [pid for _, pid, _ in entries]

        def z_season(p, a):
            i = (p["w_pos"] * abs(p["w_pos"]) / max(p["s_pos"], 1) ** (2 * a)
                 + p["w_pit"] * abs(p["w_pit"]) / max(p["s_pit"], 1) ** (2 * a))
            return math.copysign(math.sqrt(abs(i)), i)

        res = {}
        for unit, f in (("events", ex.z_unified), ("seasons", z_season)):
            curve = []
            for a in ALPHAS:
                su = np.array([f(car[pid], a) for pid in uni])
                sl = np.array([f(car[pid], a) for pid in lp])
                top = [uni[i] for i in np.argsort(-su, kind="mergesort")[:100]]
                npt = sum(car[pid]["pitcher"] for pid in top)
                curve.append((a, float(spearmanr(-ranks, sl)[0]), auc(su, y), npt))
            res[unit] = curve
        for unit, curve in res.items():
            at = next(c for c in curve if abs(c[0] - A_VALUE) < 1e-9)
            br = max(curve, key=lambda c: c[1])
            ba = max(curve, key=lambda c: c[2])
            log(f"  {lst} {unit:8s} a=0.2: {at[1]:.3f} / {at[2]:.3f} (pitchers in top 100: {at[3]}); "
                f"best a (rho) {br[0]:.2f} ({br[1]:.3f}); best a (AUC) {ba[0]:.2f} ({ba[2]:.3f})")
            rows.append([f"{lst} ({unit})", len(uni), len(listed), round(at[1], 4), round(at[2], 4), at[3],
                         br[0], round(br[1], 4), ba[0], round(ba[2], 4), "", "", "", ""])

    write_csv("season_unit.csv", ["pool", "n", "positives", "auc_or_rho_N_a0.2", "auc_S_a0.2_or_auc",
                                  "auc_S100_a0.2_or_pitchers", "bestA_N_or_rho", "auc_bestA_N_or_rho",
                                  "bestA_S_or_auc", "auc_bestA_S_or_auc", "bestA_S100", "auc_bestA_S100",
                                  "S_minus_N_ci_lo", "S_minus_N_ci_hi"], rows)
    with open(os.path.join(OUT, "season_unit_summary.txt"), "w") as fh:
        fh.write("\n".join(LOG) + "\n")


if __name__ == "__main__":
    main()
