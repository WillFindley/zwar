#!/usr/bin/env python3
"""Verify the FanGraphs fWAR robustness analysis in Appendix G (\\ref{app:fwar}).

Reads cached FanGraphs career leaderboards from data/raw/fangraphs_bat.json and
data/raw/fangraphs_pit.json, matches players to the Baseball-Reference JAWS pools
by xMLBAMID (via mlb_ID -> player_ID from war_daily_bat.txt / war_daily_pitch.txt),
falling back to normalized name and debut year when xMLBAMID is absent (and
deduplicating by player_ID), and verifies:
  * Hitters (n = 979 with >= 3,000 PA): Spearman correlation 0.934 between
    bWAR- and fWAR-based Z_pos, all 10 of the top 10 in common, Ruth (1.621) #1,
    Bonds (1.465) #2.
  * Pitchers (n = 580 matched in the JAWS pitcher pool with >= 2,500 BF):
    Spearman correlation 0.740, top-9 fWAR Z_pitch (Clemens 0.940, Randy Johnson
    0.845, Maddux 0.816, Martinez 0.791, Cy Young 0.765, Walter Johnson 0.761,
    Kershaw 0.744, Blyleven 0.719, Nolan Ryan 0.710), Mariano Rivera #35
    (39.1 fWAR, Z_pitch = 0.547, #1 reliever), and Dennis Eckersley #42
    (0.531, #2 reliever).
Outputs: outputs/fwar_check.csv
"""
import csv
import json
import math
import os
import re
import sys
import unicodedata

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


def build_mlb_to_bref():
    """Map Baseball-Reference integer mlb_ID strings to player_ID across bat and pitch files."""
    mlb_to_bref = {}
    for kind in ("bat", "pitch"):
        path = os.path.join(RAW, f"war_daily_{kind}.txt")
        with open(path, encoding="utf-8") as fh:
            for r in csv.DictReader(fh):
                mid = r["mlb_ID"].strip()
                if not mid or mid in ("NULL", "None", "0"):
                    continue
                try:
                    key = str(int(float(mid)))
                except ValueError:
                    key = mid
                pid = r["player_ID"].strip()
                if key in mlb_to_bref and mlb_to_bref[key] != pid:
                    raise ValueError(f"mlb_ID {key} maps to {mlb_to_bref[key]} and {pid}")
                mlb_to_bref[key] = pid
    return mlb_to_bref


def match_pool(fg_rows, pool, mlb_to_bref):
    """Match FanGraphs rows to a JAWS pool by xMLBAMID, falling back to
    normalized name + debut year when xMLBAMID has no B-Ref mapping."""
    by_pid = {p["pid"]: p for p in pool}
    idx = {(norm(p["name"]), p["year_min"]): p for p in pool}
    by_name = {}
    for p in pool:
        by_name.setdefault(norm(p["name"]), []).append(p)

    matched = []
    seen = set()
    for r in fg_rows:
        xid = r.get("xMLBAMID")
        pid = mlb_to_bref.get(str(int(xid))) if xid not in (None, "", 0) else None
        p = by_pid.get(pid) if pid else None
        if not p and not pid:
            nm = norm(r.get("Name", "") or r.get("PlayerName", ""))
            y0 = int(r["SeasonMin"])
            p = idx.get((nm, y0))
            if not p:
                cands = [x for x in by_name.get(nm, []) if abs(x["year_min"] - y0) <= 1]
                if len(cands) == 1:
                    p = cands[0]
        if p and p["pid"] not in seen:
            seen.add(p["pid"])
            matched.append((p, r))
    return matched


def main():
    bat_path = os.path.join(RAW, "fangraphs_bat.json")
    pit_path = os.path.join(RAW, "fangraphs_pit.json")
    with open(bat_path, encoding="utf-8") as fh:
        fg_bat = json.load(fh)["data"]
    with open(pit_path, encoding="utf-8") as fh:
        fg_pit = json.load(fh)["data"]

    mlb_to_bref = build_mlb_to_bref()
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
    matched_h = [(p, r) for p, r in match_pool(fg_bat, H, mlb_to_bref) if r["PA"] >= 3000]

    zb_h = [p["W"] / math.sqrt(p["N"]) for p, _ in matched_h]
    zf_h = [r["WAR"] / math.sqrt(r["PA"]) for _, r in matched_h]
    rho_h = spearman(zb_h, zf_h)

    top10_b = {p["pid"] for _, (p, _) in sorted(zip(zb_h, matched_h), key=lambda x: -x[0])[:10]}
    ord_f_h = sorted(zip(zf_h, matched_h), key=lambda x: -x[0])
    top10_f = {p["pid"] for _, (p, _) in ord_f_h[:10]}
    rk_h_by_pid = {p["pid"]: (i + 1, z) for i, (z, (p, _)) in enumerate(ord_f_h)}

    chk("Hitters matched (PA >= 3,000)", len(matched_h), 979, 0)
    chk("Hitters Spearman(Z_bWAR, Z_fWAR)", round(rho_h, 3), 0.934, 0.001)
    chk("Hitters top-10 overlap", len(top10_b & top10_f), 10, 0)
    chk("Hitters Babe Ruth fWAR rank", rk_h_by_pid["ruthba01"][0], 1, 0)
    chk("Hitters Babe Ruth fWAR Z_pos", round(rk_h_by_pid["ruthba01"][1], 3), 1.621, 0.001)
    chk("Hitters Barry Bonds fWAR rank", rk_h_by_pid["bondsba01"][0], 2, 0)
    chk("Hitters Barry Bonds fWAR Z_pos", round(rk_h_by_pid["bondsba01"][1], 3), 1.465, 0.001)

    # 2. Pitchers (Baseball-Reference BF as denominator, BF >= 2,500)
    P = pitchers("SP") + pitchers("RP")
    matched_p_jaws = [(p, r) for p, r in match_pool(fg_pit, P, mlb_to_bref) if p["N"] >= 2500]

    zb_p = [p["W"] / math.sqrt(p["N"]) for p, _ in matched_p_jaws]
    zf_p = [r["WAR"] / math.sqrt(p["N"]) for p, r in matched_p_jaws]
    rho_p = spearman(zb_p, zf_p)

    chk("Pitchers matched (BF >= 2,500)", len(matched_p_jaws), 580, 0)
    chk("Pitchers Spearman(Z_bWAR, Z_fWAR)", round(rho_p, 3), 0.740, 0.001)

    ord_f_p = sorted(zip(zf_p, matched_p_jaws), key=lambda x: -x[0])
    rk_by_pid = {p["pid"]: (i + 1, z, r["WAR"]) for i, (z, (p, r)) in enumerate(ord_f_p)}
    rp_ord = [p["pid"] for _, (p, _) in ord_f_p if p["role"] == "RP"]

    expected_pitchers = [
        ("clemero02", "Roger Clemens", 1, 0.940),
        ("johnsra05", "Randy Johnson", 2, 0.845),
        ("maddugr01", "Greg Maddux", 3, 0.816),
        ("martipe02", "Pedro Martinez", 4, 0.791),
        ("youngcy01", "Cy Young", 5, 0.765),
        ("johnswa01", "Walter Johnson", 6, 0.761),
        ("kershcl01", "Clayton Kershaw", 7, 0.744),
        ("blylebe01", "Bert Blyleven", 8, 0.719),
        ("ryanno01", "Nolan Ryan", 9, 0.710),
        ("riverma01", "Mariano Rivera", 35, 0.547),
        ("eckerde01", "Dennis Eckersley", 42, 0.531),
    ]
    for pid, name, exp_rk, exp_z in expected_pitchers:
        rk, z, _ = rk_by_pid[pid]
        chk(f"Pitchers {name} fWAR rank", rk, exp_rk, 0)
        chk(f"Pitchers {name} fWAR Z_pitch", round(z, 3), exp_z, 0.001)

    chk("Pitchers Mariano Rivera fWAR", round(rk_by_pid["riverma01"][2], 1), 39.1, 0.05)
    chk("Pitchers Mariano Rivera reliever rank", rp_ord.index("riverma01") + 1, 1, 0)
    chk("Pitchers Dennis Eckersley reliever rank", rp_ord.index("eckerde01") + 1, 2, 0)

    write_csv("fwar_check.csv", ["check", "computed", "paper", "status"], rows)
    if fails:
        print(f"\n{len(fails)} MISMATCHES: {fails}")
        sys.exit(1)
    print("\nALL FWAR CHECKS PASSED")


if __name__ == "__main__":
    main()
