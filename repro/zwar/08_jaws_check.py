#!/usr/bin/env python3
"""Check JAWS, S-JAWS and R-JAWS values and ranks quoted in Tables 7-9
against Baseball-Reference's JAWS position pages.

JAWS ranks in Table 7 are across all eight hitter positions combined (by
JAWS); pitcher JAWS ranks are within the SP page (Table 8) and R-JAWS ranks
within the RP page (Table 9).
Outputs: outputs/jaws_check.csv
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import HITTER_POS, load_jaws, write_csv  # noqa: E402

# Table 7: pid, JAWS, rank across 8 positions
HIT = [("ruthba01", 123.5, 1), ("bondsba01", 117.8, 2), ("mayswi01", 114.9, 3),
       ("cobbty01", 108.9, 4), ("hornsro01", 100.7, 6), ("speaktr01", 99.7, 7),
       ("willite01", 94.8, 10), ("wagneho01", 99.3, 8), ("aaronha01", 101.8, 5),
       ("gehrilo01", 90.6, 13), ("musiast01", 96.6, 9), ("collied01", 93.7, 11),
       ("mantlmi01", 87.5, 14), ("troutmi01", 78.3, 22), ("dimagjo01", 65.4, 39),
       ("steartu99", 45.1, 182), ("robinja02", 57.8, 65), ("gibsojo99", 35.2, 371),
       ("rosepe01", 62.3, 45)]
# Table 8: pid, JAWS, JAWS rank (SP), S-JAWS, S-JAWS rank
SP = [("johnswa01", 130.2, 1, 117.6, 1), ("clemero02", 102.6, 3, 101.6, 3),
      ("youngcy01", 120.8, 2, 107.2, 2), ("grovele01", 86.2, 7, 83.2, 5),
      ("nichoki01", 96.7, 4, 83.1, 6), ("alexape01", 95.1, 5, 85.1, 4),
      ("martipe02", 71.1, 22, 71.1, 12), ("johnsra05", 81.3, 10, 80.8, 9),
      ("seaveto01", 84.6, 8, 81.9, 7), ("kershcl01", 65.3, 28, 65.3, 20),
      ("maddugr01", 81.4, 9, 81.1, 8), ("mathech01", 88.8, 6, 80.3, 10),
      ("fostebi99", 41.4, 138, 41.4, 122), ("paigesa01", 38.2, 173, 38.2, 160),
      ("ryanno01", 62.2, 34, 59.7, 30), ("blylebe01", 72.4, 17, 69.7, 15),
      ("niekrph01", 75.1, 15, 70.1, 14), ("perryga01", 71.2, 21, 65.7, 19),
      ("spahnwa01", 75.8, 13, 72.6, 11)]
# Table 9: pid, JAWS, R-JAWS, R-JAWS rank (RP page)
RP = [("riverma01", 42.5, 48.9, 1), ("eckerde01", 49.9, 39.6, 2), ("wilheho01", 36.7, 34.4, 3),
      ("gossari01", 36.4, 29.5, 4), ("wagnebi02", 23.7, 24.9, 6), ("chapmar01", 21.9, 23.3, 11),
      ("nathajo01", 24.2, 24.3, 8), ("papeljo01", 21.4, 21.7, 12), ("hillejo01", 28.4, 18.1, 25),
      ("hoffmtr01", 23.7, 27.2, 5), ("henketo01", 20.2, 19.4, 19), ("smithle02", 24.8, 21.0, 15),
      ("janseke01", 20.8, 24.9, 7), ("kimbrcr01", 21.0, 19.7, 18), ("suttebr01", 24.1, 18.1, 26),
      ("gordoto01", 29.1, 23.6, 10), ("kindeel01", 26.7, 21.5, 13), ("shantbo01", 29.7, 18.4, 24)]


def rank_by(players, key):
    """Rank range for each player: (best, worst) positions within its tie block,
    since published values are rounded to 0.1."""
    vals = [p[key] if p[key] is not None else -1e9 for p in players]
    out = {}
    for p in players:
        v = p[key] if p[key] is not None else -1e9
        better = sum(x > v + 1e-9 for x in vals)
        tied = sum(abs(x - v) <= 1e-9 for x in vals)
        out[p["pid"]] = (better + 1, better + tied)
    return out


def main():
    hit = [d for pos in HITTER_POS for d in load_jaws(pos)]
    sp, rp = load_jaws("SP"), load_jaws("RP")
    idx = {d["pid"]: d for d in hit + sp + rp}
    r_hit, r_sp, r_spj, r_rpj = (rank_by(hit, "JAWS"), rank_by(sp, "JAWS"),
                                 rank_by(sp, "S_JAWS"), rank_by(rp, "R_JAWS"))
    rows, bad = [], 0

    def check(pid, field, paper, ours, tol=0):
        nonlocal bad
        if isinstance(ours, tuple):  # rank range from a tie block
            ok = ours[0] <= paper <= ours[1]
            ours = ours[0] if ours[0] == ours[1] else f"{ours[0]}-{ours[1]}"
        else:
            ok = ours is not None and abs(paper - ours) <= tol + 1e-9
        bad += not ok
        rows.append([pid, field, paper, ours, "OK" if ok else "MISMATCH"])
        if not ok:
            print(f"MISMATCH {pid:10s} {field:12s} paper={paper} ours={ours}")

    for pid, j, r in HIT:
        check(pid, "JAWS", j, idx[pid]["JAWS"], 0.05)
        check(pid, "JAWS rank", r, r_hit[pid])
    for pid, j, r, s, sr in SP:
        check(pid, "JAWS", j, idx[pid]["JAWS"], 0.05)
        check(pid, "JAWS rank", r, r_sp[pid])
        check(pid, "S-JAWS", s, idx[pid]["S_JAWS"], 0.05)
        check(pid, "S-JAWS rank", sr, r_spj[pid])
    for pid, j, rj, rr in RP:
        check(pid, "JAWS", j, idx[pid]["JAWS"], 0.05)
        check(pid, "R-JAWS", rj, idx[pid]["R_JAWS"], 0.05)
        check(pid, "R-JAWS rank", rr, r_rpj[pid])
    print(f"{len(rows)} JAWS checks, {bad} mismatches")
    write_csv("jaws_check.csv", ["pid", "field", "paper", "bref", "status"], rows)
    if bad:
        sys.exit(1)


if __name__ == "__main__":
    main()
