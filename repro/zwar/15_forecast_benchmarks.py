#!/usr/bin/env python3
"""Forecast and concurrent-judgment benchmarks for the exponent alpha in
Z_alpha = W / N^alpha (new analysis for the alpha-convergence section).

Population and roles (exactly as in 10_checkpoint_prediction.py): careers
beginning in 1901 or later with no Negro Leagues season; hitters have fewer
than 100 career innings pitched (< 300 outs) and are scored on position-player
WAR with N = PA; pitchers are scored on pitching WAR with N = IPouts x 1.4 (a
constant factor, so rankings are unaffected). A season counts in a role if it
has PA > 0 (hitters) or IPouts > 0 (pitchers). ONE COMMON CUTOFF: careers must
end by 2016 (the last season of the Lahman Databank award-voting files) for
every outcome in this script, including future WAR; this is why the checkpoint
future-WAR numbers differ slightly from script 10 (careers ending by 2023).

Forecast designs (predictor = Z_alpha on the first-period W, N):
  * checkpoint k = 3 and k = 5: the first k role seasons (>= 1,000 PA /
    600 BF by the checkpoint); the future period is every later role season.
  * career midpoint: careers with S >= 6 role seasons; predictors from the
    first floor(S/2) seasons (>= 1,000 PA / 600 BF in that half), outcomes
    from the remaining seasons ("second-half career"). This design conditions
    on career length, so it is a split-career association, not a real-time
    forecast.

Outcomes, all from the future / second-half role seasons:
  * future WAR (Spearman; everyone in the design)
  * future All-Star selections (Spearman; a player-year counts once, so the
    two-game years 1959-62 count once; only years with a future role season
    count; restricted to players whose last predictor season is >= 1932, so
    the whole future period lies in 1933+)
  * future award vote shares (Spearman; sum over future role seasons of
    pointsWon / pointsMax). Hitters: MVP shares, restricted to future periods
    in 1931+ (continuous BBWAA MVP voting in both leagues; the Databank has no
    MVP vote for 1915-21, AL 1929-30, NL 1922-23 and 1930). Pitchers: MVP +
    Cy Young shares, restricted to future periods in 1956+.
  * Hall of Fame election (AUC; careers ending by 2010, HOF_EXCLUDE removed,
    HOF flag from the JAWS pages as in script 10)
  * future rate W / N (Spearman; players with >= 1,000 PA / 600 BF in the
    future period) -- a TALENT contrast, not a career-value target; it is
    expected to prefer alpha near 1.

Concurrent judgment benchmarks (NOT forecasts): the Hall-of-Fame-style pools
of 04_hof_validation.py (hitters from the eight JAWS hitter pages pooled, SP,
RP; W = role WAR, N = PA / BF as in pools.py), careers ending by 2016 and with
no Negro Leagues season (NgL seasons have no MLB All-Star or award coverage).
Spearman of career Z_alpha with career All-Star selections (careers wholly in
1933-2016) and with career award shares (hitters: MVP, careers wholly in
1931-2016; SP / RP: MVP + Cy Young, careers wholly in 1956-2016).

For every benchmark (alpha grid 0..1 step 0.05; see alpha_bench.py): the curve,
argmax alpha, metric at alpha = 0, 0.2, 0.5, 1 and at the argmax; 1,000-resample
player bootstrap (stratified by outcome for AUCs) of the argmax alpha (median,
95% interval) and of m(0.2) - m(0.5) and m(0.2) - m(0); 5-fold x 20-repeat
cross-validation of the choice of alpha.

Award / All-Star IDs: Databank playerID -> bbrefID via People.csv (they differ
for ~230 players); B-Ref season files use bbrefID.

Outputs: outputs/forecast_benchmarks.csv (long: benchmark, design, role,
         outcome, n, alpha, metric), outputs/forecast_benchmarks_summary.csv,
         outputs/forecast_benchmarks_summary.txt
"""
import csv
import importlib.util
import os
import sys
from collections import defaultdict

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import HOF_EXCLUDE, RAW, OUT, load_war_daily, write_csv  # noqa: E402
from pools import hitters, pitchers  # noqa: E402
import alpha_bench as ab  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("ckpt10", os.path.join(HERE, "10_checkpoint_prediction.py"))
ckpt10 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ckpt10)

FIRST, LAST_DONE, LAST_HOF = 1901, 2016, 2010
MIN_N = ckpt10.MIN_N                  # {"H": 1000 PA, "P": 600 BF}
BF_PER_OUT = ckpt10.BF_PER_OUT        # 1.4
ASG_FIRST = 1933
AWARD_FIRST = {"H": 1931, "P": 1956}
DB = os.path.join(RAW, "databank")
LOG = []


def log(msg=""):
    print(msg)
    LOG.append(msg)


# ---------------------------------------------------------------------------
# Lahman Databank: All-Star selections and award vote shares (bbref IDs)
# ---------------------------------------------------------------------------
def databank():
    with open(os.path.join(DB, "People.csv"), encoding="latin-1") as fh:
        people = {r["playerID"]: (r["bbrefID"] or r["playerID"]) for r in csv.DictReader(fh)}
    stats = dict(people_remapped=sum(k != v for k, v in people.items()))
    asg, blank = set(), []
    with open(os.path.join(DB, "AllstarFull.csv"), encoding="latin-1") as fh:
        for r in csv.DictReader(fh):
            if not r["yearID"].strip():
                blank.append(r["playerID"])
                continue
            asg.add((people.get(r["playerID"], r["playerID"]), int(r["yearID"])))
    shares = defaultdict(lambda: defaultdict(float))
    with open(os.path.join(DB, "AwardsSharePlayers.csv"), encoding="latin-1") as fh:
        for r in csv.DictReader(fh):
            key = {"MVP": "MVP", "Cy Young": "CY"}.get(r["awardID"])
            if key is None or float(r["pointsMax"]) <= 0:
                continue
            pid = people.get(r["playerID"], r["playerID"])
            shares[(pid, int(r["yearID"]))][key] += float(r["pointsWon"]) / float(r["pointsMax"])
    stats["asg_blank_year"] = blank
    stats["asg_ids"] = {p for p, _ in asg}
    stats["award_ids"] = {p for p, _ in shares}
    return asg, shares, stats


def award_share(shares, pid, year, role):
    s = shares.get((pid, year))
    if not s:
        return 0.0
    return s.get("MVP", 0.0) + (s.get("CY", 0.0) if role != "H" else 0.0)


# ---------------------------------------------------------------------------
# Careers by role (population of script 10, 2016 cutoff)
# ---------------------------------------------------------------------------
def role_careers(role):
    bat, pit = load_war_daily("bat"), load_war_daily("pitch")
    excl, hof = ckpt10.ngl_players(), ckpt10.hof_flags()
    out = []
    for pid in sorted(set(bat) | set(pit)):
        if pid in excl:
            continue
        years = set(bat.get(pid, {"seasons": {}})["seasons"]) | set(pit.get(pid, {"seasons": {}})["seasons"])
        if min(years) < FIRST or max(years) > LAST_DONE:
            continue
        outs_career = sum(s["IPouts"] for s in pit.get(pid, {"seasons": {}})["seasons"].values())
        if role == "H":
            if pid not in bat or outs_career >= 300:
                continue
            seas = sorted((y, s["WAR"], s["PA"]) for y, s in bat[pid]["seasons"].items() if s["PA"] > 0)
        else:
            if pid not in pit:
                continue
            seas = sorted((y, s["WAR"], s["IPouts"] * BF_PER_OUT)
                          for y, s in pit[pid]["seasons"].items() if s["IPouts"] > 0)
        if not seas:
            continue
        out.append(dict(pid=pid, seas=seas, last=max(years), hof=pid in hof, excl=pid in HOF_EXCLUDE))
    return out


def design_sample(careers, role, design, asg, shares):
    """Rows with first-period (W, N) and future-period outcomes."""
    rows = []
    for c in careers:
        seas = c["seas"]
        if design == "midpoint":
            if len(seas) < 6:
                continue
            k = len(seas) // 2
        else:
            k = int(design.split("=")[1])
            if len(seas) < k:
                continue
        w0 = sum(w for _, w, _ in seas[:k])
        n0 = sum(n for _, _, n in seas[:k])
        if n0 < MIN_N[role]:
            continue
        fut = seas[k:]
        fyears = [y for y, _, _ in fut]
        rows.append(dict(
            pid=c["pid"], W=w0, N=n0, t=seas[k - 1][0],
            fW=sum(w for _, w, _ in fut), fN=sum(n for _, _, n in fut),
            fASG=sum((c["pid"], y) in asg for y in fyears),
            fAW=sum(award_share(shares, c["pid"], y, role) for y in fyears),
            last=c["last"], hof=c["hof"], excl=c["excl"]))
    return rows


def outcome_sets(rows, role):
    """(outcome, metric kind, subset rows, y, category)."""
    sets = []
    sets.append(("future WAR", "spearman", rows, [r["fW"] for r in rows], "forecast"))
    a = [r for r in rows if r["t"] >= ASG_FIRST - 1]
    sets.append(("future All-Star selections", "spearman", a, [r["fASG"] for r in a], "forecast"))
    w = [r for r in rows if r["t"] >= AWARD_FIRST[role] - 1]
    sets.append(("future award shares" + (" (MVP)" if role == "H" else " (MVP+CY)"), "spearman", w,
                 [r["fAW"] for r in w], "forecast"))
    h = [r for r in rows if r["last"] <= LAST_HOF and not r["excl"]]
    sets.append(("Hall of Fame", "auc", h, [r["hof"] for r in h], "forecast"))
    f = [r for r in rows if r["fN"] >= MIN_N[role]]
    sets.append(("future rate", "spearman", f, [r["fW"] / r["fN"] for r in f], "talent-contrast"))
    return sets


def ngl_free(players, ngl):
    return [p for p in players if p["pid"] not in ngl]


DESIGNS = ("checkpoint k=3", "checkpoint k=5", "midpoint")


def design_samples(asg, shares):
    """[(role label, design, rows)] for every forecast design (2016 cutoff)."""
    out = []
    for role, rlabel in (("H", "Hitters"), ("P", "Pitchers")):
        careers = role_careers(role)
        for design in DESIGNS:
            out.append((rlabel, design, design_sample(careers, role, design, asg, shares)))
    return out


def concurrent_sets(asg, shares):
    """Concurrent benchmarks: dicts with name, role, outcome, first year, W, N, y."""
    ngl = ckpt10.ngl_players()
    pools = [("Hitters (8 positions pooled)", "H", ngl_free(hitters(), ngl)),
             ("Starting pitchers", "P", ngl_free(pitchers("SP"), ngl)),
             ("Relief pitchers", "P", ngl_free(pitchers("RP"), ngl))]
    out = []
    for pname, role, ps in pools:
        ps = [p for p in ps if p["year_max"] <= LAST_DONE]
        for outcome, first in (("career All-Star selections", ASG_FIRST),
                               ("career award shares" + (" (MVP)" if role == "H" else " (MVP+CY)"),
                                AWARD_FIRST[role])):
            sub = [p for p in ps if p["year_min"] >= first]
            if outcome.startswith("career All-Star"):
                y = [sum((p["pid"], yr) in asg for yr in range(p["year_min"], p["year_max"] + 1)) for p in sub]
            else:
                y = [sum(award_share(shares, p["pid"], yr, role) for yr in range(p["year_min"], p["year_max"] + 1))
                     for p in sub]
            out.append(dict(name=f"{pname} | concurrent | {outcome}", design="concurrent", role=pname,
                            outcome=outcome, first=first, kind="spearman", category="concurrent",
                            W=np.array([p["W"] for p in sub], float), N=np.array([p["N"] for p in sub], float),
                            y=np.array(y, float)))
    return out


def benchmark_sets(asg, shares, samples=None):
    """Every script-15 benchmark as a dict (name, design, role, outcome, kind, category, W, N, y)."""
    out = []
    for rlabel, design, rows in (samples if samples is not None else design_samples(asg, shares)):
        role = rlabel[0]
        for outcome, kind, sub, y, cat in outcome_sets(rows, role):
            out.append(dict(name=f"{rlabel} | {design} | {outcome}", design=design, role=rlabel,
                            outcome=outcome, kind=kind, category=cat,
                            W=np.array([r["W"] for r in sub], float), N=np.array([r["N"] for r in sub], float),
                            y=np.array(y, bool if kind == "auc" else float), n_design=len(rows)))
    return out + concurrent_sets(asg, shares)


def main():
    asg, shares, st = databank()
    bat, pit = load_war_daily("bat"), load_war_daily("pitch")
    known = set(bat) | set(pit)
    log("Databank: People.csv remaps %d playerIDs to a different bbrefID; All-Star player-years %d; "
        "award (MVP/CY) player-years %d" % (st["people_remapped"], len(asg), len(shares)))
    log("  All-Star rows with blank yearID (dropped): %s" % (st["asg_blank_year"] or "none"))
    log("  mapped IDs absent from the B-Ref season files: All-Star %d, awards %d"
        % (len(st["asg_ids"] - known), len(st["award_ids"] - known)))
    log(f"Population: careers {FIRST}-{LAST_DONE} (common cutoff), no Negro Leagues season; "
        f"HOF subset ends by {LAST_HOF}; All-Star future periods {ASG_FIRST}+; award future periods "
        f"{AWARD_FIRST['H']}+ (hitters, MVP), {AWARD_FIRST['P']}+ (pitchers, MVP+CY)")
    log()

    long_rows, summ_rows, results = [], [], []
    last_design = None
    for b in benchmark_sets(asg, shares):
        if b["design"] != "concurrent" and (b["role"], b["design"]) != last_design:
            last_design = (b["role"], b["design"])
            log(f"== {b['role']}, {b['design']}: {b['n_design']} players")
        elif b["design"] == "concurrent" and last_design != "concurrent":
            last_design = "concurrent"
            log("== Concurrent (career Z_alpha vs career All-Star selections / award shares; not forecasts)")
        S = ab.z_matrix(b["W"], b["N"])
        r = ab.analyse(S, b["y"], b["kind"], b["name"], cv=True)
        r.update(design=b["design"], role=b["role"], outcome=b["outcome"], category=b["category"])
        results.append(r)
        if b["design"] == "concurrent":
            log(f" {b['role']}: {b['outcome']} (Spearman; careers {b['first']}-{LAST_DONE}; "
                f"{int(np.sum(b['y'] > 0))} players with > 0)")
        else:
            log(f" {b['outcome']} ({'AUC' if b['kind'] == 'auc' else 'Spearman'}; {b['category']})")
        log(ab.describe(r))
    log()

    for r in results:
        for a, m in zip(ab.ALPHAS, r["curve"]):
            long_rows.append([r["name"], r["design"], r["role"], r["outcome"], r["n"], a, round(float(m), 5)])
        summ_rows.append([r["name"], r["design"], r["role"], r["outcome"], r["category"],
                          "AUC" if r["kind"] == "auc" else "Spearman"] + ab.fmt_row(r))

    # Compact overview
    cv_ = [r for r in results if r["category"] != "talent-contrast"]
    log("Overview (career-value benchmarks, excluding the future-rate talent contrast):")
    log(f"  {'benchmark':72s} {'argmax':>6s} {'95% boot':>12s} {'m.2-m.5':>8s} {'m.2-m0':>8s}")
    for r in cv_:
        log(f"  {r['name']:72s} {r['argmax']:6.2f} [{r['boot_lo']:.2f},{r['boot_hi']:.2f}] "
            f"{r['d02_05']:+8.3f} {r['d02_0']:+8.3f}")
    log(f"  median argmax {np.median([r['argmax'] for r in cv_]):.2f}; intervals containing 0.2: "
        f"{sum(r['has02'] for r in cv_)}/{len(cv_)}, containing 0.5: {sum(r['has05'] for r in cv_)}/{len(cv_)}")

    write_csv("forecast_benchmarks.csv", ["benchmark", "design", "role", "outcome", "n", "alpha", "metric"],
              long_rows)
    write_csv("forecast_benchmarks_summary.csv",
              ["benchmark", "design", "role", "outcome", "category", "metric_name"]
              + ab.SUMMARY_FIELDS + ab.CV_FIELDS, summ_rows)
    with open(os.path.join(OUT, "forecast_benchmarks_summary.txt"), "w") as fh:
        fh.write("\n".join(LOG) + "\n")


if __name__ == "__main__":
    main()
