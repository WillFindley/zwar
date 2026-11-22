#!/usr/bin/env python3
"""Verify the FanGraphs fWAR robustness analysis in Appendix G (\\ref{app:fwar}).

Reads cached FanGraphs career leaderboards from data/raw/fangraphs_bat.json and
data/raw/fangraphs_pit.json, matches players to the Baseball-Reference JAWS pools
by normalized name and debut year, and verifies:
  * Hitters (n = 953 with >= 3,000 PA): Spearman correlation 0.936 between
    bWAR- and fWAR-based Z_pos, all 10 of the top 10 in common, Ruth (1.621) #1,
    Bonds (1.465) #2.
  * Pitchers (n = 560 matched in the JAWS pitcher pool with >= 2,500 BF):
    Spearman correlation 0.743, top-6 fWAR Z_pitch (Clemens 0.940, Randy Johnson
    0.845, Maddux 0.816, Martinez 0.791, Cy Young 0.765, Walter Johnson 0.761),
    Kershaw #7 (0.744), Nolan Ryan #9 (0.710), Mariano Rivera #35 (39.1 fWAR,
    Z_pitch = 0.547, #1 reliever), and Dennis Eckersley (0.531, #2 reliever).
Outputs: outputs/fwar_check.csv
"""
import json
import math
import os
import re
import sys
import unicodedata

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import RAW, spearman, write_csv  # noqa: E402
from pools import hitters, pitchers  # noqa: E402

ALIASES = {
    "pete alexander": "grover alexander",
    "john ward": "john montgomery ward",
    "goose gossage": "rich gossage",
    "hank aaron": "henry aaron",
}


def norm(s):
    s = re.sub(r"<[^>]+>", "", s)
    s = unicodedata.normalize("NFKD", s)
    s = "".join(c for c in s if not unicodedata.combining(c)).lower()
    s = re.sub(r"[^a-z0-9 ]", "", s).strip()
    return ALIASES.get(s, s)


def main():
    bat_path = os.path.join(RAW, "fangraphs_bat.json")
    pit_path = os.path.join(RAW, "fangraphs_pit.json")
    with open(bat_path, encoding="utf-8") as fh:
        fg_bat = json.load(fh)["data"]
    with open(pit_path, encoding="utf-8") as fh:
        fg_pit = json.load(fh)["data"]

    fails = []
    rows = []

    def chk(label, got, exp, tol=0.0):
        bad = abs(got - exp) > tol + 1e-9
        if bad:
            fails.append(label)
        status = "MISMATCH" if bad else "OK"
        rows.append([label, round(got, 4) if isinstance(got, float) else got, exp, status])
        flag = "   <-- MISMATCH" if bad else ""
        print(f"{label:48s} computed={got} paper={exp}{flag}")

    # 1. Hitters (matched against JAWS hitter pool, PA >= 3,000)
    H = hitters()
    h_idx = {(norm(p["name"]), p["year_min"]): p for p in H}
    h_by_name = {}
    for p in H:
        h_by_name.setdefault(norm(p["name"]), []).append(p)

    matched_h = []
    for r in fg_bat:
        nm = norm(r.get("Name", "") or r.get("PlayerName", ""))
        y0 = int(r["SeasonMin"])
        p = h_idx.get((nm, y0))
        if not p:
            cands = [x for x in h_by_name.get(nm, []) if abs(x["year_min"] - y0) <= 1]
            if len(cands) == 1:
                p = cands[0]
        if p and r["PA"] >= 3000:
            matched_h.append((p, r))

    zb_h = [p["W"] / math.sqrt(p["N"]) for p, _ in matched_h]
    zf_h = [r["WAR"] / math.sqrt(r["PA"]) for _, r in matched_h]
    rho_h = spearman(zb_h, zf_h)

    top10_b = {p["pid"] for _, (p, _) in sorted(zip(zb_h, matched_h), key=lambda x: -x[0])[:10]}
    ord_f_h = sorted(zip(zf_h, matched_h), key=lambda x: -x[0])
    top10_f = {p["pid"] for _, (p, _) in ord_f_h[:10]}

    chk("Hitters matched (PA >= 3,000)", len(matched_h), 953, 0)
    chk("Hitters Spearman(Z_bWAR, Z_fWAR)", round(rho_h, 3), 0.936, 0.001)
    chk("Hitters top-10 overlap", len(top10_b & top10_f), 10, 0)
    chk("Hitters #1 Babe Ruth fWAR Z_pos", round(ord_f_h[0][0], 3), 1.621, 0.001)
    chk("Hitters #2 Barry Bonds fWAR Z_pos", round(ord_f_h[1][0], 3), 1.465, 0.001)

    # 2. Pitchers (Baseball-Reference BF as denominator, BF >= 2,500)
    P = pitchers("SP") + pitchers("RP")
    p_idx = {(norm(p["name"]), p["year_min"]): p for p in P}
    matched_p_jaws = []
    for r in fg_pit:
        nm = norm(r.get("Name", "") or r.get("PlayerName", ""))
        y0 = int(r["SeasonMin"])
        p = p_idx.get((nm, y0))
        if p and p["N"] >= 2500:
            matched_p_jaws.append((p, r))

    zb_p = [p["W"] / math.sqrt(p["N"]) for p, _ in matched_p_jaws]
    zf_p = [r["WAR"] / math.sqrt(p["N"]) for p, r in matched_p_jaws]
    rho_p = spearman(zb_p, zf_p)

    chk("Pitchers matched (BF >= 2,500)", len(matched_p_jaws), 560, 0)
    chk("Pitchers Spearman(Z_bWAR, Z_fWAR)", round(rho_p, 3), 0.743, 0.001)

    ord_f_p = sorted(zip(zf_p, matched_p_jaws), key=lambda x: -x[0])
    rk_by_pid = {p["pid"]: (i + 1, z, r["WAR"]) for i, (z, (p, r)) in enumerate(ord_f_p)}

    expected_pitchers = [
        ("clemero02", "Roger Clemens", 1, 0.940),
        ("johnsra05", "Randy Johnson", 2, 0.845),
        ("maddugr01", "Greg Maddux", 3, 0.816),
        ("martipe02", "Pedro Martinez", 4, 0.791),
        ("youngcy01", "Cy Young", 5, 0.765),
        ("johnswa01", "Walter Johnson", 6, 0.761),
        ("kershcl01", "Clayton Kershaw", 7, 0.744),
        ("ryanno01", "Nolan Ryan", 9, 0.710),
        ("riverma01", "Mariano Rivera", 35, 0.547),
    ]
    for pid, name, exp_rk, exp_z in expected_pitchers:
        rk, z, _ = rk_by_pid[pid]
        chk(f"Pitchers {name} fWAR rank", rk, exp_rk, 0)
        chk(f"Pitchers {name} fWAR Z_pitch", round(z, 3), exp_z, 0.001)

    chk("Pitchers Mariano Rivera fWAR", round(rk_by_pid["riverma01"][2], 1), 39.1, 0.05)
    chk("Pitchers Dennis Eckersley fWAR Z_pitch", round(rk_by_pid["eckerde01"][1], 3), 0.531, 0.001)

    write_csv("fwar_check.csv", ["check", "computed", "paper", "status"], rows)
    if fails:
        print(f"\n{len(fails)} MISMATCHES: {fails}")
        sys.exit(1)
    print("\nALL FWAR CHECKS PASSED")


if __name__ == "__main__":
    main()
