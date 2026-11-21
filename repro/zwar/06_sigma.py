#!/usr/bin/env python3
"""Estimate the per-event standard deviation sigma_k of WAR for hitters and
pitchers from season-to-season dispersion, and the implied cross-role scale
factor c = sigma_pos / sigma_pitch (paper Table 1, "Variance" row).

Model (Proposition 3): season WAR W_s = r_i N_s + e_s with Var(e_s) = sigma^2 N_s.
Dividing by sqrt(N_s) gives a homoscedastic regression
    W_s / sqrt(N_s) = r_i sqrt(N_s) [+ b_i t_s sqrt(N_s)] + u_s,  Var(u_s) = sigma^2,
so the pooled residual sum of squares divided by its degrees of freedom is an
unbiased estimate of sigma^2. With a constant rate per player the estimate
also absorbs genuine changes in talent (aging), so it is an upper bound on
pure per-event noise; adding a per-player linear trend in the rate removes
the smooth part of that drift.

Pitcher season BF: exact from cached player pages where available, otherwise
season IPouts x (published career BF / career outs).
Outputs: outputs/sigma_estimates.csv
"""
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import auc, z_alpha, write_csv, load_war_daily  # noqa: E402
from pools import hitters, pitchers, hof_eligible, pitcher_season_bf  # noqa: E402


def season_table(players, kind):
    """{pid: [(year, W, N), ...]}"""
    out = {}
    for p in players:
        seasons = load_war_daily("bat" if kind == "H" else "pitch")[p["pid"]]["seasons"]
        if kind == "H":
            rows = [(y, s["WAR"], s["PA"]) for y, s in seasons.items()]
        else:
            wn, _ = pitcher_season_bf(p["pid"], p["BF"])
            rows = [(y, w, n) for y, (w, n) in wn.items()]
        out[p["pid"]] = rows
    return out


def sigma_hat(table, min_n=1, trend=False, deg=None, min_year=0):
    if deg is None:
        deg = 1 if trend else 0
    rss, dof = 0.0, 0
    for rows in table.values():
        rows = [(y, w, n) for y, w, n in rows if n >= min_n and y >= min_year]
        p = deg + 1
        if len(rows) <= p:
            continue
        y_ = np.array([w / np.sqrt(n) for _, w, n in rows])
        sq = np.array([np.sqrt(n) for _, _, n in rows])
        if deg >= 1:
            t = np.array([yr for yr, _, _ in rows], float)
            t -= t.mean()
            X = np.column_stack([sq * (t ** k) for k in range(p)])
        else:
            X = sq[:, None]
        beta, *_ = np.linalg.lstsq(X, y_, rcond=None)
        r = y_ - X @ beta
        rss += float(r @ r)
        dof += len(rows) - p
    return np.sqrt(rss / dof), dof


def main():
    H = [p for p in hitters() if p["N"] >= 3000]
    SP = [p for p in pitchers("SP") if p["N"] >= 2000]
    RP = [p for p in pitchers("RP") if p["N"] >= 2000]
    P = SP + RP
    th, tp = season_table(H, "H"), season_table(P, "P")
    tsp, trp = season_table(SP, "P"), season_table(RP, "P")
    print(f"players: {len(H)} hitters (>=3000 PA), {len(P)} pitchers (>=2000 BF: {len(SP)} SP, {len(RP)} RP)")

    rows = []
    specs = [
        ("constant rate, all seasons", dict()),
        ("constant rate, seasons >= 100 events", dict(min_n=100)),
        ("linear trend in rate, all seasons", dict(trend=True)),
        ("linear trend in rate, seasons >= 100 events", dict(trend=True, min_n=100)),
        ("linear trend in rate, 1950 on", dict(trend=True, min_year=1950)),
        ("quadratic trend in rate, all seasons", dict(deg=2)),
        ("quadratic trend in rate, seasons >= 100 events", dict(deg=2, min_n=100)),
    ]
    for label, kw in specs:
        sh, dh = sigma_hat(th, **kw)
        sp, dp = sigma_hat(tp, **kw)
        s_sp, _ = sigma_hat(tsp, **kw)
        s_rp, _ = sigma_hat(trp, **kw)
        c = sh / sp
        print(f"{label:45s} sigma_pos={sh:.4f}  sigma_pitch={sp:.4f} (SP {s_sp:.4f}, RP {s_rp:.4f})  "
              f"c=sigma_pos/sigma_pitch={c:.3f}   (single-season SE per 650 PA: {sh*np.sqrt(650):.2f} WAR)")
        rows.append([label, round(sh, 5), round(sp, 5), round(s_sp, 5), round(s_rp, 5), round(c, 4), dh, dp])

    # Hall of Fame AUC (hitters + SP pooled) at the implied c values
    HSP = hof_eligible(hitters()) + hof_eligible(pitchers("SP"))
    y = np.array([p["hof"] for p in HSP])
    for label, sh, sp, s_sp, s_rp, c, *_ in rows:
        s = np.array([(c if p["role"] == "SP" else 1.0) * z_alpha(p["W"], p["N"]) for p in HSP])
        print(f"HOF AUC (hitters+SP) at c={c:.3f} [{label}]: {auc(s, y):.3f}")
    write_csv("sigma_estimates.csv", ["specification", "sigma_pos", "sigma_pitch", "sigma_SP", "sigma_RP", "c",
                                      "dof_hitters", "dof_pitchers"], rows)

    # Relievers by career leverage (outs-weighted mean entering gmLI). The
    # leverage multiplier (1 + gmLI)/2 scales high-leverage relievers' value; if
    # it also scaled their noise, sigma would be larger for closers.
    gmli = career_gmli()
    hi = [p for p in RP if gmli.get(p["pid"], 0) >= 1.5]
    lo = [p for p in RP if gmli.get(p["pid"], 0) < 1.5]
    th_, tl_ = season_table(hi, "P"), season_table(lo, "P")
    print(f"Relievers by career gmLI: {len(hi)} with gmLI >= 1.5, {len(lo)} below")
    g_hi = float(np.mean([gmli[p["pid"]] for p in hi]))
    g_lo = float(np.mean([gmli.get(p["pid"], 1.0) for p in lo]))
    print(f"  mean career gmLI: {g_hi:.2f} (>= 1.5) vs {g_lo:.2f} (< 1.5); "
          f"ratio implied by full (1+gmLI)/2 noise scaling = {(1 + g_hi) / (1 + g_lo):.3f} (means {g_hi:.3f}, {g_lo:.3f})")
    for label, kw in specs[:3]:
        s_hi, _ = sigma_hat(th_, **kw)
        s_lo, _ = sigma_hat(tl_, **kw)
        print(f"  {label:45s} RP gmLI>=1.5 sigma={s_hi:.4f}   RP gmLI<1.5 sigma={s_lo:.4f}   "
              f"ratio={s_hi / s_lo:.3f}")
    # Relative to the common scale (hitters and starters), which is what a
    # role-specific variance would rescale high-leverage relievers against.
    print("  High-leverage RP sigma relative to the common (hitter / SP) scale:")
    for label, kw in specs[:3]:
        s_hi, _ = sigma_hat(th_, **kw)
        sh, _ = sigma_hat(th, **kw)
        s_sp, _ = sigma_hat(tsp, **kw)
        print(f"  {label:45s} sigma_HL/sigma_pos={s_hi / sh:.3f}  sigma_HL/sigma_SP={s_hi / s_sp:.3f}  "
              f"-> score shrink {100 * (1 - sh / s_hi):.1f}% / {100 * (1 - s_sp / s_hi):.1f}%")


def career_gmli():
    """Outs-weighted career mean of B-Ref's GR_leverage_index_avg per pitcher."""
    import csv
    from common import RAW, num
    acc = {}
    with open(os.path.join(RAW, "war_daily_pitch.txt"), encoding="utf-8") as fh:
        for r in csv.DictReader(fh):
            li, outs = num(r.get("GR_leverage_index_avg"), None), num(r.get("IPouts_relief"))
            if li is None or outs <= 0:
                continue
            a = acc.setdefault(r["player_ID"], [0.0, 0.0])
            a[0] += li * outs
            a[1] += outs
    return {pid: s / w for pid, (s, w) in acc.items() if w > 0}


if __name__ == "__main__":
    main()
