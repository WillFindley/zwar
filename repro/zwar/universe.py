"""All-time rank universe shared by 07_rank_checks.py and 17_leaderboards.py.

Universe: every player in B-Ref's season WAR files.
  * Position play: position-player WAR (published career row from a cached
    player page, else the season sum rounded to 0.1 as published on B-Ref);
    PA from the player page, else the JAWS pages, else summed season PA.
  * Pitching: pitching WAR (same rounding convention); career BF from the JAWS
    pages (1,000 pitchers), a cached player page, a short list of hitters'
    secondary BF quoted in Table 7, otherwise IPouts x 4.2/3 (an approximation
    that only affects low-ranked pitchers).
Exposure floor max(N, 1) is applied by the scoring functions, and ties are
broken deterministically by player ID. The unified (two-coordinate) score is
the value-consistent l_gamma rule, common.z2d_lgamma (gamma = 1/(1 - alpha)):
total WAR at alpha = 0, signed quadrature at alpha = 1/2.
"""
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import (HITTER_POS, PITCHER_POS, load_jaws, load_war_daily, career,  # noqa: E402
                    load_player_career, z2d_lgamma)

# Secondary pitching BF from Table 7 / top-50 hitters without a cached player page
TAB6_BF = {"cobbty01": 20.0, "speaktr01": 4.0, "willite01": 9.0, "wagneho01": 37.0,
           "musiast01": 1.0, "broutda01": 127.0, "ansonca01": 21.0, "pujolal01": 7.0,
           "davisge01": 23.0, "steartu99": 37.0, "gibsojo99": 10.0}


def bref_round1(x):
    """Round half away from zero to 0.1, as B-Ref displays WAR."""
    return float(np.copysign(int(abs(x) * 10 + 0.5 + 1e-9) / 10.0, x))


def build():
    """Return a dict with the universe:
    pids, bat, pitch (war_daily dicts), jaws ({pid: merged JAWS row}),
    pos_w, pos_n, pit_w, pit_n, ipouts ({pid: published or summed outs}),
    approx (pids whose BF is IPouts x 4.2/3)."""
    jaws = {}
    for pos in HITTER_POS + PITCHER_POS:
        for d in load_jaws(pos):
            jaws.setdefault(d["pid"], {}).update(d)
    bat, pitch = load_war_daily("bat"), load_war_daily("pitch")
    pids = set(bat) | set(pitch)

    pos_w, pos_n, pit_w, pit_n, ipouts, approx = {}, {}, {}, {}, {}, set()
    for pid in pids:
        cb, cp = career("bat", pid), career("pitch", pid)
        pc = load_player_career(pid)
        w_b = pc["bat"].get("WAR") if (pc and "WAR" in pc["bat"]) else (bref_round1(cb["WAR"]) if cb else 0.0)
        pos_w[pid] = w_b
        pa = (pc["bat"].get("PA") if pc else None) or jaws.get(pid, {}).get("PA_page") or (cb["PA"] if cb else 0.0)
        pos_n[pid] = pa
        w_p = pc["pitch"].get("WAR") if (pc and "WAR" in pc["pitch"]) else (bref_round1(cp["WAR"]) if cp else 0.0)
        pit_w[pid] = w_p
        bf = jaws.get(pid, {}).get("BF")
        if not bf and pc:
            bf = pc["pitch"].get("BF")
        if not bf and pid in TAB6_BF:
            bf = TAB6_BF[pid]
        if not bf and cp:
            bf = cp["IPouts"] * 4.2 / 3
            approx.add(pid)
        pit_n[pid] = bf or 0.0
        outs = jaws.get(pid, {}).get("IPouts") or (pc["pitch"].get("IPouts") if pc else None)
        ipouts[pid] = outs or (cp["IPouts"] if cp else 0.0)
    return {"pids": pids, "bat": bat, "pitch": pitch, "jaws": jaws, "pos_w": pos_w,
            "pos_n": pos_n, "pit_w": pit_w, "pit_n": pit_n, "ipouts": ipouts, "approx": approx}


def unified_scores(u, alpha):
    """{pid: two-coordinate l_gamma score} for every player in the universe."""
    pw, pn, tw, tn = u["pos_w"], u["pos_n"], u["pit_w"], u["pit_n"]
    return {p: z2d_lgamma(pw[p], pn[p], tw[p], tn[p], alpha) for p in u["pids"]}


def ranking(score):
    """Ranks 1..n, ties broken by player ID so the output does not depend on
    set iteration order (which varies with PYTHONHASHSEED)."""
    order = sorted(score, key=lambda p: (-score[p], p))
    return {p: i + 1 for i, p in enumerate(order)}, order


def tie_range(score, pid, eps=1e-9):
    """(best, worst) rank of pid's tie block."""
    v = score[pid]
    better = sum(1 for x in score.values() if x > v + eps)
    same = sum(1 for x in score.values() if abs(x - v) <= eps)
    return better + 1, better + same


def min_ranks(score, eps=1e-9):
    """Standard competition ranks ('1224'): the best rank of each tie block."""
    vals = np.sort(np.fromiter(score.values(), float))[::-1]
    neg = -vals  # ascending
    return {p: int(np.searchsorted(neg, -v - eps, side="left")) + 1 for p, v in score.items()}
