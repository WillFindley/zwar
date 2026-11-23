#!/usr/bin/env python3
"""Estimate the convexity gamma of season value from pennant races (paper
Proposition 4, Section 4, Table 2).

Proposition 4: if a season worth s WAR is worth s^gamma, a constant-rate career
ranks as W / N^alpha with alpha = 1 - 1/gamma. Here gamma is estimated without
reference to Hall of Fame voting or expert lists, from how much a season of s
wins raises a team's chance of reaching the postseason, winning the pennant or
winning the World Series.

Data: Baseball-Reference franchise histories (data/raw/teams/*.html; W, L,
finish and postseason result for every AL/NL team-season since 1901) and the
season WAR files (player seasons and their teams).

Method:
  1. Win totals are scaled to 162 games. For each postseason format (era) and
     outcome, P(outcome | wins) is a logistic regression on team-seasons.
  2. Context-neutral season value: v(s) = mean over all team-seasons of
     P_era(w + s) - P_era(w), i.e. the gain from adding s wins to a randomly
     drawn team of its era.
  3. Actual-context season value: for every player season (combined batting and
     pitching WAR on one team, scaled to 162 games), P(w_team) - P(w_team - s),
     averaged within 1-WAR bins.
  4. gamma is the log-log slope of v(s) over s in [2, 10] WAR (the range of
     All-Star to MVP seasons) and, equivalently for the paper's example, the
     ratio log2(v(10) / v(5)). alpha = 1 - 1/gamma.
  5. 95% intervals: bootstrap over team-seasons within era (players' seasons
     resampled with their teams), refitting the logistic curves.
Outputs: outputs/season_value.csv, outputs/season_value_summary.txt
"""
import csv
import html as htmllib
import os
import re
import sys
from collections import defaultdict

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import RAW, OUT, write_csv  # noqa: E402

FIRST, LAST = 1901, 2025          # 2026 postseason incomplete at the snapshot
SKIP = {1981, 1994, 2020}          # split season / no postseason / 60-game season
NO_WS = {1901, 1902, 1904}         # pennant decided, no World Series
ERAS = [("1901-1968 (1 berth per league)", 1901, 1968),
        ("1969-1993 (4 berths)", 1969, 1993),
        ("1995-2011 (8 berths)", 1995, 2011),
        ("2012-2021 (10 berths)", 2012, 2021),
        ("2022-2025 (12 berths)", 2022, 2025)]
OUTCOMES = ["berth", "pennant", "ws"]
S_GRID = np.round(np.arange(2.0, 10.0001, 0.5), 2)
N_BOOT = 1000
LOG = []


def log(msg=""):
    print(msg)
    LOG.append(msg)


def era_of(y):
    for i, (_, a, b) in enumerate(ERAS):
        if a <= y <= b:
            return i
    return None


def load_team_seasons():
    rows = []
    tdir = os.path.join(RAW, "teams")
    for fn in sorted(os.listdir(tdir)):
        if not fn.endswith(".html"):
            continue
        h = open(os.path.join(tdir, fn), encoding="utf-8").read().replace("<!--", "").replace("-->", "")
        i = h.find('id="franchise_years"')
        if i < 0:
            continue
        seg = h[i:h.find("</table>", i)]
        for r in re.findall(r"<tr[^>]*>(.*?)</tr>", seg, re.S):
            cells = {k: v for k, v in re.findall(r'data-stat="([^"]+)"[^>]*>(.*?)</t[hd]>', r, re.S)}
            if "year_ID" not in cells or not re.fullmatch(r"\d{4}", re.sub("<[^>]+>", "", cells["year_ID"]).strip()):
                continue
            txt = {k: htmllib.unescape(re.sub("<[^>]+>", "", v)).replace("\xa0", " ").strip()
                   for k, v in cells.items()}
            m = re.search(r"/teams/([A-Z0-9]{3})/(\d{4})\.shtml", cells.get("team_name", ""))
            y = int(txt["year_ID"])
            lg = txt.get("lg_ID", "").split(" ")[0]
            if not m or lg not in ("AL", "NL") or not (FIRST <= y <= LAST) or y in SKIP:
                continue
            w, l_ = float(txt["W"]), float(txt["L"])
            po, fin = txt.get("playoffs", ""), txt.get("finish", "")
            first = fin.startswith("1st")
            pennant = ("WS" in po) or (y in NO_WS and first)
            rows.append(dict(team=m.group(1), year=y, lg=lg, W=w, L=l_, w162=w / (w + l_) * 162,
                             g=w + l_, era=era_of(y), berth=bool(po) or (y in NO_WS and first),
                             pennant=pennant, ws=po.startswith("Won WS"), no_ws=y in NO_WS))
    uniq = {}
    for r in rows:  # deduplicate (year, team) across franchise pages (OAK covers 1901-2026 Athletics AL; ATH is 1876 NL)
        uniq.setdefault((r["year"], r["team"]), r)
    return [uniq[k] for k in sorted(uniq)]


def player_seasons():
    """{(year, team): [season WAR of each player stint]} from both WAR files."""
    acc = defaultdict(float)
    for kind in ("bat", "pitch"):
        with open(os.path.join(RAW, f"war_daily_{kind}.txt"), encoding="utf-8") as fh:
            for r in csv.DictReader(fh):
                if r["lg_ID"] not in ("AL", "NL"):
                    continue
                try:
                    w = float(r["WAR"])
                except ValueError:
                    continue
                acc[(int(r["year_ID"]), r["team_ID"], r["player_ID"])] += w
    out = defaultdict(list)
    for (y, t, _), w in acc.items():
        out[(y, t)].append(w)
    return out


def logit_fit(x, y, wt, quad=False, iters=60):
    """Weighted logistic regression by Newton-Raphson; x centered at 81 wins, scaled by 10."""
    z = (np.asarray(x, float) - 81.0) / 10.0
    X = np.column_stack([np.ones_like(z), z] + ([z * z] if quad else []))
    y, wt = np.asarray(y, float), np.asarray(wt, float)
    b = np.zeros(X.shape[1])
    for _ in range(iters):
        p = 1 / (1 + np.exp(-np.clip(X @ b, -35, 35)))
        W = wt * p * (1 - p) + 1e-12
        step = np.linalg.solve(X.T @ (X * W[:, None]) + 1e-9 * np.eye(len(b)), X.T @ (wt * (y - p)))
        b += step
        if np.max(np.abs(step)) < 1e-10:
            break
    return b


def logit_p(b, x):
    z = (np.asarray(x, float) - 81.0) / 10.0
    eta = b[0] + b[1] * z + (b[2] * z * z if len(b) == 3 else 0.0)
    return 1 / (1 + np.exp(-np.clip(eta, -35, 35)))


class Data:
    """Array form of team-seasons and player seasons for fast (weighted) refits."""

    def __init__(self, teams, ps):
        self.w = np.array([t["w162"] for t in teams])
        self.era = np.array([t["era"] for t in teams])
        self.no_ws = np.array([t["no_ws"] for t in teams])
        self.y = {o: np.array([t[o] for t in teams], float) for o in OUTCOMES}
        ti, s = [], []
        for k, t in enumerate(teams):
            for x in ps.get((t["year"], t["team"]), []):
                s162 = x * 162 / t["g"]
                if 1.5 <= s162 < 10.5:
                    ti.append(k)
                    s.append(s162)
        self.ti, self.s = np.array(ti), np.array(s)
        self.bin = np.rint(self.s).astype(int)

    def usable(self, outcome):
        return ~self.no_ws if outcome == "ws" else np.ones(len(self.w), bool)

    def curves(self, outcome, wt, quad=False):
        u = self.usable(outcome)
        return {e: logit_fit(self.w[u & (self.era == e)], self.y[outcome][u & (self.era == e)],
                             wt[u & (self.era == e)], quad) for e in range(len(ERAS))}

    def p(self, cur, w, era):
        out = np.empty(len(w))
        for e, b in cur.items():
            m = era == e
            out[m] = logit_p(b, w[m])
        return out

    def v_neutral(self, cur, outcome, wt, eras=None):
        u = self.usable(outcome)
        if eras is not None:
            u = u & np.isin(self.era, eras)
        w, e, ww = self.w[u], self.era[u], wt[u]
        base = self.p(cur, w, e)
        return np.array([np.sum(ww * (self.p(cur, w + s, e) - base)) / ww.sum() for s in S_GRID])

    def v_actual(self, cur, outcome, wt):
        keep = self.usable(outcome)[self.ti]
        ti, s, bn = self.ti[keep], self.s[keep], self.bin[keep]
        w, e = self.w[ti], self.era[ti]
        d = self.p(cur, w, e) - self.p(cur, w - s, e)
        ww = wt[ti]
        bins = np.arange(2, 11)
        vals = np.array([np.sum(ww[bn == b] * d[bn == b]) / np.sum(ww[bn == b]) for b in bins])
        cnts = np.array([int(np.sum(bn == b)) for b in bins])
        return bins, vals, cnts


def gamma_grid(v):
    """(log-log slope over S_GRID, log2 v(10)/v(5))."""
    slope = np.polyfit(np.log(S_GRID), np.log(v), 1)[0]
    ratio = np.log2(v[S_GRID == 10.0][0] / v[S_GRID == 5.0][0])
    return slope, ratio


def gamma_bins(bins, vals):
    slope = np.polyfit(np.log(bins), np.log(vals), 1)[0]
    ratio = np.log2(vals[bins == 10][0] / vals[bins == 5][0])
    return slope, ratio


def main():
    teams = load_team_seasons()
    ps = player_seasons()
    # Coverage: every AL/NL team-season in the WAR files must have a franchise row.
    have = {(t["year"], t["team"]) for t in teams}
    want = {k for k in ps if FIRST <= k[0] <= LAST and k[0] not in SKIP}
    missing = sorted(want - have)
    assert len(teams) == 2622 and len(missing) == 0, f"Unexpected team-seasons: {len(teams)}, missing={missing}"
    log(f"team-seasons: {len(teams)} ({FIRST}-{LAST}, excluding {sorted(SKIP)}); "
        f"AL/NL team-seasons in WAR files without a franchise row: {len(missing)} {missing[:10]}")
    for e, (name, _, _) in enumerate(ERAS):
        T = [t for t in teams if t["era"] == e]
        log(f"  {name:32s} {len(T):5d} team-seasons; berth {np.mean([t['berth'] for t in T]):.3f}, "
            f"pennant {np.mean([t['pennant'] for t in T]):.3f}, WS {np.mean([t['ws'] for t in T if not t['no_ws']]):.3f}")
    D = Data(teams, ps)
    assert len(D.s) == 24400, f"Expected 24,400 usable player-seasons, got {len(D.s)}"
    log(f"player seasons with 1.5 <= WAR (162-game scale) < 10.5: {len(D.s)}")
    log()

    rng = np.random.default_rng(2026)
    ones = np.ones(len(teams))
    era_idx = [np.flatnonzero(D.era == e) for e in range(len(ERAS))]
    boot_w = []
    for _ in range(N_BOOT):
        wt = np.zeros(len(teams))
        for ix in era_idx:
            np.add.at(wt, rng.choice(ix, len(ix)), 1.0)
        boot_w.append(wt)
    rows, ws_checks = [], None
    for outcome in OUTCOMES:
        for quad in (False, True):
            label = f"{outcome}{' (quadratic logit)' if quad else ''}"
            cur = D.curves(outcome, ones, quad)
            vn = D.v_neutral(cur, outcome, ones)
            gn = gamma_grid(vn)
            bins, va, cnt = D.v_actual(cur, outcome, ones)
            ga = gamma_bins(bins, va)
            ci = {}
            if not quad:
                B = []
                for wt in boot_w:
                    cb = D.curves(outcome, wt)
                    B.append(gamma_grid(D.v_neutral(cb, outcome, wt))
                             + gamma_bins(*D.v_actual(cb, outcome, wt)[:2]))
                B = np.array(B)
                ci = {j: np.percentile(B[:, j], [2.5, 97.5]) for j in range(4)}
                if outcome == "ws":
                    ws_checks = (sum(cnt), vn, gn, ga, ci)

            def fmt(val, j):
                a = f"{val:.3f}"
                if j in ci:
                    a += f" [{ci[j][0]:.2f}, {ci[j][1]:.2f}]"
                return a + f" (alpha {1 - 1 / val:.3f})"
            log(f"== {label}")
            log("  context-neutral v(s) at s = 2, 5, 10: " + ", ".join(
                f"{vn[S_GRID == s][0]:.4f}" for s in (2.0, 5.0, 10.0)))
            log(f"  context-neutral gamma: slope {fmt(gn[0], 0)}; log2 v(10)/v(5) {fmt(gn[1], 1)}")
            log(f"  actual-context gamma:  slope {fmt(ga[0], 2)}; log2 v(10)/v(5) {fmt(ga[1], 3)}")
            log("  actual-context seasons per bin (2..10 WAR): " + " ".join(str(c) for c in cnt))
            rows.append([outcome, "quadratic" if quad else "linear", round(gn[0], 4), round(gn[1], 4),
                         round(ga[0], 4), round(ga[1], 4)]
                        + ([round(x, 4) for j in range(4) for x in ci[j]] if ci else [""] * 8))
        cur = D.curves(outcome, ones)
        era_cn = [gamma_grid(D.v_neutral(cur, outcome, ones, eras=[e]))[0] for e in range(len(ERAS))]
        if outcome == "ws":
            assert all(1.215 <= g <= 1.305 for g in era_cn), f"Unexpected WS per-era CN slopes: {era_cn}"
        log("  by era (context-neutral slope): " + "; ".join(
            f"{ERAS[e][0].split(' ')[0]}: {g:.2f}" for e, g in enumerate(era_cn)))
        log()
    rmap = {(r[0], r[1]): r for r in rows}
    ws_cnt, ws_vn, ws_gn, ws_ga, ws_ci = ws_checks
    assert ws_cnt == 23997, f"Expected 23,997 WS player-seasons, got {ws_cnt}"
    assert f"{100 * ws_vn[S_GRID == 5.0][0]:.2f}" == "4.13" and f"{100 * ws_vn[S_GRID == 10.0][0]:.2f}" == "10.47"
    assert (f"{rmap[('berth', 'linear')][2]:.2f}", f"{rmap[('berth', 'linear')][4]:.2f}") == ("1.07", "1.10")
    assert (f"{rmap[('pennant', 'linear')][2]:.2f}", f"{rmap[('pennant', 'linear')][4]:.2f}") == ("1.17", "1.29")
    assert (f"{ws_gn[0]:.2f}", f"{ws_ci[0][0]:.2f}", f"{ws_ci[0][1]:.2f}") == ("1.25", "1.23", "1.28")
    assert (f"{ws_ga[0]:.2f}", f"{ws_ci[2][0]:.2f}", f"{ws_ci[2][1]:.2f}") == ("1.30", "1.18", "1.40")
    write_csv("season_value.csv", ["outcome", "logit", "gamma_neutral_slope", "gamma_neutral_ratio",
                                   "gamma_actual_slope", "gamma_actual_ratio",
                                   "ns_lo", "ns_hi", "nr_lo", "nr_hi", "as_lo", "as_hi", "ar_lo", "ar_hi"], rows)
    with open(os.path.join(OUT, "season_value_summary.txt"), "w") as fh:
        fh.write("\n".join(LOG) + "\n")


if __name__ == "__main__":
    main()
