"""Build the player pools used by the Hall of Fame, alpha-sensitivity and
variance analyses from the B-Ref JAWS pages and season WAR files."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import (HITTER_POS, PITCHER_POS, HOF_EXCLUDE, load_jaws,  # noqa: E402
                    load_war_daily, load_player_page, has_season_bf, spw)

SPW_PA, SPW_PA_UNIT = 3250, 650
SPW_BF, SPW_BF_UNIT = 5000, 1000


def _seasons(kind, pid):
    p = load_war_daily(kind).get(pid)
    return p["seasons"] if p else {}


def pitcher_season_bf(pid, career_bf):
    """Season BF: exact from a cached player page when available, otherwise
    IPouts scaled by the player's career BF per out (published career BF from
    the JAWS page). Returns ({year: (WAR, BF)}, source)."""
    seasons = _seasons("pitch", pid)
    if has_season_bf(pid):
        pg = load_player_page(pid)["pitch"]
        if pg:
            return ({y: (s["WAR"], pg.get(y, {}).get("BF", 0.0)) for y, s in seasons.items()},
                    "exact")
    outs = sum(s["IPouts"] for s in seasons.values())
    ratio = career_bf / outs if outs > 0 else 0.0
    return {y: (s["WAR"], s["IPouts"] * ratio) for y, s in seasons.items()}, "scaled"


def hitters():
    """All players on the eight hitter JAWS pages, with position-player WAR,
    WAA and season data from war_daily_bat."""
    out, seen = [], set()
    for pos in HITTER_POS:
        for d in load_jaws(pos):
            if d["pid"] in seen:
                continue
            seen.add(d["pid"])
            s = _seasons("bat", d["pid"])
            d["W"] = sum(x["WAR"] for x in s.values())
            d["WAA"] = sum(x["WAA"] for x in s.values())
            d["N"] = d["PA_page"] if d["PA_page"] else sum(x["PA"] for x in s.values())
            d["season_WN"] = [(x["WAR"], x["PA"]) for x in s.values()]
            d["SPW"] = spw(d["season_WN"], SPW_PA, SPW_PA_UNIT)
            d["role"] = "H"
            out.append(d)
    return out


def pitchers(pos):
    out = []
    for d in load_jaws(pos):
        s = _seasons("pitch", d["pid"])
        d["W"] = sum(x["WAR"] for x in s.values())
        d["WAA"] = sum(x["WAA"] for x in s.values())
        d["N"] = d["BF"]
        wn, src = pitcher_season_bf(d["pid"], d["BF"])
        d["season_WN"] = list(wn.values())
        d["season_src"] = src
        d["SPW"] = spw(d["season_WN"], SPW_BF, SPW_BF_UNIT)
        d["role"] = pos
        out.append(d)
    return out


def hof_eligible(players, last_year=2010, exclude=True):
    return [p for p in players
            if p["year_max"] <= last_year and not (exclude and p["pid"] in HOF_EXCLUDE)]
