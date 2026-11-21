#!/usr/bin/env python3
"""Validate the Standardized Peak WAR (SPW) implementation.

1. Against values published by Gordon (BRJ 52(1), 2023; WAR as of Dec. 2022):
   Pedro Martinez 53.6 (best SP), Eddie Plank 32.3, Babe Ruth 61.4 (best hitter),
   and the statements that Cy Young and Walter Johnson added 124.7 and 102.6
   pitching WAR beyond their SPW.
2. Exact season BF (player pages) versus the scaled approximation
   (season IPouts x career BF/out) used for pitchers without a cached page.
Outputs: outputs/spw_check.csv
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np  # noqa: E402
from common import load_war_daily, load_player_page, has_season_bf, spw, write_csv, RAW  # noqa: E402
from pools import SPW_BF, SPW_BF_UNIT, SPW_PA, SPW_PA_UNIT, pitchers  # noqa: E402

JAWS_BF = {p["pid"]: p["BF"] for p in pitchers("SP") + pitchers("RP")}


def pitcher_spw(pid, mode):
    seasons = load_war_daily("pitch")[pid]["seasons"]
    if mode == "exact":
        pg = load_player_page(pid)["pitch"]
        wn = [(s["WAR"], pg.get(y, {}).get("BF", 0.0)) for y, s in seasons.items()]
    else:
        outs = sum(s["IPouts"] for s in seasons.values())
        ratio = JAWS_BF[pid] / outs
        wn = [(s["WAR"], s["IPouts"] * ratio) for s in seasons.values()]
    return spw(wn, SPW_BF, SPW_BF_UNIT), sum(w for w, _ in wn)


def main():
    rows = []
    print("1) Comparison with Gordon (2023)")
    targets = [("martipe02", "Pedro Martinez", 53.6, None), ("planked01", "Eddie Plank", 32.3, None),
               ("youngcy01", "Cy Young", None, 124.7), ("johnswa01", "Walter Johnson", None, 102.6),
               ("riverma01", "Mariano Rivera", None, 0.0)]
    for pid, name, g_spw, g_beyond in targets:
        mode = "exact" if has_season_bf(pid) else "scaled"
        s, w = pitcher_spw(pid, mode)
        if g_spw is not None:
            print(f"  {name:16s} SPW ours {s:5.1f} ({mode})   Gordon {g_spw:5.1f}")
            rows.append([name, "SPW", round(s, 2), g_spw, mode])
        else:
            print(f"  {name:16s} WAR beyond SPW ours {w - s:5.1f} ({mode})   Gordon {g_beyond:5.1f}")
            rows.append([name, "WAR beyond SPW", round(w - s, 2), g_beyond, mode])
    ruth = load_war_daily("bat")["ruthba01"]["seasons"]
    s = spw([(x["WAR"], x["PA"]) for x in ruth.values()], SPW_PA, SPW_PA_UNIT)
    print(f"  {'Babe Ruth':16s} SPW ours {s:5.1f} (hitting)  Gordon  61.4")
    rows.append(["Babe Ruth", "SPW (hitting)", round(s, 2), 61.4, "exact PA"])

    print("2) Exact vs scaled season BF (all pitchers with exact season BF)")
    diffs = []
    for pid in JAWS_BF:
        if not has_season_bf(pid) or pid not in load_war_daily("pitch"):
            continue
        e, _ = pitcher_spw(pid, "exact")
        a, _ = pitcher_spw(pid, "scaled")
        diffs.append(a - e)
        rows.append([pid, "SPW exact vs scaled", round(a, 2), round(e, 2), "scaled vs exact"])
    d = np.array(diffs)
    print(f"  {len(d)} pitchers: scaled - exact SPW mean {d.mean():+.2f}, median {np.median(d):+.2f}, "
          f"5-95% [{np.percentile(d, 5):+.2f}, {np.percentile(d, 95):+.2f}]")
    write_csv("spw_check.csv", ["player", "quantity", "ours", "reference", "note"], rows)


if __name__ == "__main__":
    main()
