#!/usr/bin/env python3
"""Check every raw input reported in the paper against Baseball-Reference.

Reference values, in priority order (all cached by fetch_data.py):
  * Published career rows: JAWS position pages, the 'N Yrs' footer of
    player pages (PA, IP, BF, WAR), war_daily season sums, and finally
    the career-WAR leaderboard fallback.

Status codes:
  OK        exact (counts) or within 0.05 (WAR)
  ROUNDING  WAR differs by <= 0.10 (published career vs. summed seasons)
  MISMATCH  anything else

Writes outputs/input_check.csv.
"""
import csv
import os
import sys
import unicodedata

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import (PITCHER_POS, HITTER_POS, load_war_daily, career, load_jaws,  # noqa: E402
                    load_player_page, load_player_career, load_war_leaderboard,
                    ip_to_outs, write_csv, RAW)
import paper_values as PV  # noqa: E402

ALIASES = {
    "Pete Alexander": ["Grover Alexander"],
    "John Ward": ["John Montgomery Ward", "Monte Ward"],
    "Goose Gossage": ["Rich Gossage"],
    "Hank Aaron": ["Henry Aaron"],
}

# Pre-BF pitchers in Table 10 whose BF is estimated as round(4.2 * IP)
ESTIMATED_BF = {"Elmer Smith", "Cy Seymour"}


def norm(s):
    s = unicodedata.normalize("NFKD", s)
    return "".join(ch for ch in s if not unicodedata.combining(ch)).lower().strip()


def resolve(name, kind):
    """Map a display name to the B-Ref player_ID with the largest |WAR| of `kind`."""
    names = {norm(n) for n in [name] + ALIASES.get(name, [])}
    best = None
    for k in ("bat", "pitch"):
        for pid, p in load_war_daily(k).items():
            if norm(p["name"]) in names:
                c = career(kind, pid)
                w = abs(c["WAR"]) if c else 0.0
                if best is None or w > best[1]:
                    best = (pid, w)
    return best[0] if best else None


_JAWS = None
_LB = None


def jaws_index():
    global _JAWS
    if _JAWS is None:
        _JAWS = {}
        for pos in HITTER_POS + PITCHER_POS:
            for d in load_jaws(pos):
                _JAWS.setdefault(d["pid"], {}).update(
                    {k: v for k, v in d.items() if k in ("BF", "PA_page", "IPouts")})
    return _JAWS


def leaderboard():
    global _LB
    if _LB is None:
        _LB = load_war_leaderboard()
    return _LB


def published(pid, kind, field):
    """Published career value and its source, or (None, 'missing')."""
    pc = load_player_career(pid)
    if pc and pc[kind].get(field) not in (None, 0):
        return pc[kind][field], "player page"
    j = jaws_index().get(pid, {})
    jf = {"BF": "BF", "PA": "PA_page", "IPouts": "IPouts"}.get(field)
    if jf and j.get(jf):
        return j[jf], "jaws page"
    c = career(kind, pid)
    if c and field in c:
        return c[field], "war_daily (season sum)"
    lb = leaderboard().get(pid)
    if lb and field in ("PA", "IPouts") and lb.get(field):
        if (kind == "bat" and field == "PA") or (kind == "pitch" and field == "IPouts"):
            return lb[field], "WAR leaderboard"
    return None, "missing"


def published_war(pid, kind):
    pc = load_player_career(pid)
    if pc and pc[kind].get("WAR") is not None and "WAR" in pc[kind]:
        return pc[kind]["WAR"], "player page"
    c = career(kind, pid)
    return (c["WAR"], "war_daily (season sum)") if c else (0.0, "none")


rows, problems = [], []


def check(player, field, paper, bref, source, is_war):
    if bref is None:
        status = "MISSING"
    else:
        d = abs(paper - bref)
        if is_war:
            status = "OK" if d <= 0.05 + 1e-9 else ("ROUNDING" if d <= 0.10 + 1e-9 else "MISMATCH")
        else:
            status = "OK" if d == 0 else "MISMATCH"
    rows.append([player, field, paper, "" if bref is None else round(bref, 3), source, status])
    if status not in ("OK",):
        problems.append(f"{status:9s} {player:28s} {field:9s} paper={paper} bref={bref} ({source})")


def main():
    for name, w, pa in PV.HITTERS:
        pid = resolve(name, "bat")
        check(name, "posWAR", w, *published_war(pid, "bat"), True)
        check(name, "PA", pa, *published(pid, "bat", "PA"), False)
    check("Herb Washington", "G", 105, career("bat", "washihe01")["G"], "war_daily (season sum)", False)

    for name, w, bf, ip in PV.PITCHERS:
        pid = resolve(name, "pitch")
        check(name, "pitchWAR", w, *published_war(pid, "pitch"), True)
        check(name, "IP(outs)", ip_to_outs(ip), *published(pid, "pitch", "IPouts"), False)
        check(name, "BF", bf, *published(pid, "pitch", "BF"), False)

    for name, wpos, pa, wp, bf, ip in PV.TWO_WAY:
        pid = resolve(name, "pitch") if wp > wpos else resolve(name, "bat")
        check(name, "posWAR", wpos, *published_war(pid, "bat"), True)
        check(name, "pitchWAR", wp, *published_war(pid, "pitch"), True)
        check(name, "IP(outs)", ip_to_outs(ip), *published(pid, "pitch", "IPouts"), False)
        check(name, "PA", pa, *published(pid, "bat", "PA"), False)
        bref_bf, bf_src = published(pid, "pitch", "BF")
        if bref_bf is None and name in ESTIMATED_BF:
            outs, outs_src = published(pid, "pitch", "IPouts")
            if outs is not None:
                bref_bf = round(outs * 4.2 / 3)
                bf_src = f"{outs_src} (4.2 * IP)"
        check(name, "BF", bf, bref_bf, bf_src, False)

    for name, w, pa in PV.PITCHER_BATTING:
        pid = resolve(name, "pitch")
        check(name, "batWAR", w, *published_war(pid, "bat"), True)
        check(name, "batPA", pa, *published(pid, "bat", "PA"), False)

    for name, wpos, pa, wp, bf, ip in PV.HITTER_PITCHING:
        pid = resolve(name, "bat")
        check(name, "posWAR", wpos, *published_war(pid, "bat"), True)
        check(name, "PA", pa, *published(pid, "bat", "PA"), False)
        check(name, "pitchWAR", wp, *published_war(pid, "pitch"), True)
        if bf is not None:
            check(name, "BF", bf, *published(pid, "pitch", "BF"), False)
        if ip is not None:
            check(name, "IP(outs)", ip_to_outs(ip), *published(pid, "pitch", "IPouts"), False)

    # Season checkpoints: compare with (a) the sum of displayed (rounded) season
    # WAR on the player page and (b) the unrounded war_daily sum.
    for name, label, (y0, y1), w, n, kind in PV.CHECKPOINTS:
        pid = resolve(name, "pitch" if kind == "pitch" else "bat")
        key = "BF" if kind == "pitch" else "PA"
        if os.path.exists(os.path.join(RAW, f"player_{pid}.html")):
            pg = load_player_page(pid)[kind]
            w_page = sum(s["WAR"] for y, s in pg.items() if y0 <= y <= y1)
            check(f"{name} {label}", "WAR", w, w_page, "player page (sum of displayed seasons)", True)
            check(f"{name} {label}", key, n, sum(s[key] for y, s in pg.items() if y0 <= y <= y1),
                  "player page (seasons)", False)
        seasons = load_war_daily(kind)[pid]["seasons"]
        w_daily = sum(s["WAR"] for y, s in seasons.items() if y0 <= y <= y1)
        rows.append([f"{name} {label}", "WAR(unrounded)", w, round(w_daily, 3),
                     "war_daily (season sum)", "INFO"])

    for name, label, (y0, y1), ip, neg_exp in PV.CHECKPOINT_EXTRA:
        pid = resolve(name, "pitch")
        pg = load_player_page(pid)["pitch"]
        if ip is not None:
            check(f"{name} {label}", "IP(outs)", ip_to_outs(ip),
                  sum(s["IPouts"] for y, s in pg.items() if y0 <= y <= y1),
                  "player page (seasons)", False)
        if neg_exp is not None:
            neg_cnt = sum(1 for y, s in pg.items() if y0 <= y <= y1 and s["WAR"] < 0)
            check(f"{name} {label}", "neg_yrs", neg_exp, neg_cnt, "player page (seasons)", False)

    # Remark 4: 59.0/41.0 position-player vs pitcher bWAR share in every season since 1980
    yr_np_bat, yr_all_bat, yr_pit = {}, {}, {}
    with open(os.path.join(RAW, "war_daily_bat.txt"), encoding="utf-8") as fh:
        for r in csv.DictReader(fh):
            y = int(r["year_ID"])
            if y < 1980 or r["WAR"] in ("", "NULL", "NA"):
                continue
            wv = float(r["WAR"])
            yr_all_bat[y] = yr_all_bat.get(y, 0.0) + wv
            if r.get("pitcher") != "Y":
                yr_np_bat[y] = yr_np_bat.get(y, 0.0) + wv
    with open(os.path.join(RAW, "war_daily_pitch.txt"), encoding="utf-8") as fh:
        for r in csv.DictReader(fh):
            y = int(r["year_ID"])
            if y < 1980 or r["WAR"] in ("", "NULL", "NA"):
                continue
            yr_pit[y] = yr_pit.get(y, 0.0) + float(r["WAR"])
    sh_np = {y: 100.0 * yr_np_bat[y] / (yr_np_bat[y] + yr_pit[y]) for y in sorted(yr_pit)}
    sh_all = {y: 100.0 * yr_all_bat[y] / (yr_all_bat[y] + yr_pit[y]) for y in sorted(yr_pit)}
    bad_np = [y for y, s_val in sh_np.items() if round(s_val, 1) != 59.0]
    bad_all = [y for y, s_val in sh_all.items() if not (58.8 <= s_val <= 59.1)]
    if bad_np or bad_all:
        problems.append(f"MISMATCH Remark 4 league WAR split bad_np={bad_np}, bad_all={bad_all}")
    print(f"Remark 4 (1980-{max(sh_np)}): non-pitcher bat WAR share {min(sh_np.values()):.2f}%-"
          f"{max(sh_np.values()):.2f}% (59.0/41.0); w/ pitcher batting {min(sh_all.values()):.2f}%-"
          f"{max(sh_all.values()):.2f}%")

    path = write_csv("input_check.csv", ["player", "field", "paper", "bref", "source", "status"], rows)
    counts = {}
    for r in rows:
        counts[r[-1]] = counts.get(r[-1], 0) + 1
    print(f"{len(rows)} rows: {counts} -> {path}")
    for p in problems:
        print("  " + p)
    if problems:
        sys.exit(1)


if __name__ == "__main__":
    main()
