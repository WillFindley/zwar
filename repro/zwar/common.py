"""Shared loaders and statistics for the ZWAR reproduction pipeline.

Pure standard library + numpy. All inputs are read from data/raw/, which is
populated by fetch_data.py (the only networked step).
"""
import csv
import html as htmllib
import math
import os
import re
from collections import defaultdict

import numpy as np
from scipy.stats import rankdata

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RAW = os.path.join(ROOT, "data", "raw")
OUT = os.path.join(ROOT, "outputs")
os.makedirs(OUT, exist_ok=True)

HITTER_POS = ["C", "1B", "2B", "3B", "SS", "LF", "CF", "RF"]
PITCHER_POS = ["SP", "RP"]

# Players excluded from the main Hall of Fame specification (bans / PEDs).
HOF_EXCLUDE = {
    "rosepe01",   # Pete Rose
    "jacksjo01",  # Joe Jackson
    "bondsba01",  # Barry Bonds
    "clemero02",  # Roger Clemens
    "mcgwima01",  # Mark McGwire
    "sosasa01",   # Sammy Sosa
    "palmera01",  # Rafael Palmeiro
    "sheffga01",  # Gary Sheffield
}


def num(x, default=0.0):
    if x is None:
        return default
    x = str(x).strip().replace(",", "")
    if x in ("", "NULL", "None"):
        return default
    try:
        return float(x)
    except ValueError:
        return default


def ip_to_outs(ip):
    """Baseball innings notation (e.g. 2855.1) to outs."""
    ip = num(ip)
    whole = int(ip)
    frac = round((ip - whole) * 10)
    return whole * 3 + frac


# ---------------------------------------------------------------------------
# Baseball-Reference season WAR files
# ---------------------------------------------------------------------------
_WAR_CACHE = {}


def load_war_daily(kind):
    """Return {player_ID: {"name":..., "seasons": {year: {...}}}} for kind in
    {"bat", "pitch"}. Multiple stints in a season are summed."""
    if kind in _WAR_CACHE:
        return _WAR_CACHE[kind]
    path = os.path.join(RAW, f"war_daily_{kind}.txt")
    players = {}
    with open(path, encoding="utf-8") as fh:
        for r in csv.DictReader(fh):
            pid = r["player_ID"]
            p = players.setdefault(pid, {"name": r["name_common"], "seasons": {}})
            y = int(r["year_ID"])
            s = p["seasons"].setdefault(y, defaultdict(float))
            s["WAR"] += num(r["WAR"])
            s["WAA"] += num(r["WAA"])
            if kind == "bat":
                s["PA"] += num(r["PA"])
                s["G"] += num(r["G"])
            else:
                s["IPouts"] += num(r["IPouts"])
                s["G"] += num(r["G"])
                s["GS"] += num(r["GS"])
    _WAR_CACHE[kind] = players
    return players


def career(kind, pid):
    p = load_war_daily(kind).get(pid)
    if not p:
        return None
    tot = defaultdict(float)
    for s in p["seasons"].values():
        for k, v in s.items():
            tot[k] += v
    tot["first"] = min(p["seasons"])
    tot["last"] = max(p["seasons"])
    return tot


# ---------------------------------------------------------------------------
# HTML table parsing (Baseball-Reference)
# ---------------------------------------------------------------------------
_TAG = re.compile(r"<[^>]+>")
_ROW = re.compile(r"<tr\b([^>]*)>(.*?)</tr>", re.S)
_CELL = re.compile(r"<(t[hd])\b([^>]*)>(.*?)</t[hd]>", re.S)
_ATTR = re.compile(r'([a-zA-Z_:-]+)="([^"]*)"')


def _read_html(name):
    with open(os.path.join(RAW, name), encoding="utf-8") as fh:
        # B-Ref hides many tables inside HTML comments.
        return fh.read().replace("<!--", "").replace("-->", "")


def table_rows(html, table_id):
    """Yield (row_attrs, {data-stat: text}, {data-stat: attrs}) for a table."""
    start = re.search(r'<table\b[^>]*\bid="%s"' % re.escape(table_id), html)
    if not start:
        return
    end = html.find("</table>", start.end())
    body = html[start.end():end]
    for rm in _ROW.finditer(body):
        rattrs = dict(_ATTR.findall(rm.group(1)))
        cells, cattrs = {}, {}
        for cm in _CELL.finditer(rm.group(2)):
            a = dict(_ATTR.findall(cm.group(2)))
            stat = a.get("data-stat")
            if not stat:
                continue
            cells[stat] = htmllib.unescape(_TAG.sub("", cm.group(3))).strip()
            cattrs[stat] = a
            cattrs[stat]["_raw"] = cm.group(3)
        if cells:
            yield rattrs, cells, cattrs


def load_jaws(pos):
    """Parse a JAWS position leaderboard into a list of player dicts."""
    html = _read_html(f"jaws_{pos}.html")
    out = []
    for _, c, a in table_rows(html, "jaws"):
        pid = a.get("player", {}).get("data-append-csv")
        if not pid:
            continue
        raw = a["player"]["_raw"]
        d = {
            "pid": pid,
            "name": _TAG.sub("", raw).replace("HOF", "").strip(),
            "hof": 'class="hof_note"' in raw,
            "pos": pos,
            "WAR": num(c.get("WAR_career")),
            "WAR7": num(c.get("WAR_peak7")),
            "JAWS": num(c.get("JAWS")),
            "S_JAWS": num(c.get("S_JAWS"), None) if "S_JAWS" in c else None,
            "R_JAWS": num(c.get("R_JAWS"), None) if "R_JAWS" in c else None,
            "WAA_page": num(c.get("WAA")),
            "year_min": int(num(c.get("year_min"))),
            "year_max": int(num(c.get("year_max"))),
        }
        if pos in PITCHER_POS:
            d["BF"] = num(c.get("batters_faced"))
            d["IP"] = c.get("IP", "")
            d["IPouts"] = ip_to_outs(c.get("IP", "0"))
            d["G"] = num(c.get("G"))
            d["GS"] = num(c.get("GS"))
        else:
            d["PA_page"] = num(c.get("PA"))
        out.append(d)
    return out


def has_season_bf(pid):
    return (os.path.exists(os.path.join(RAW, f"player_{pid}.html"))
            or os.path.exists(os.path.join(RAW, "pitching_tables", f"{pid}.html")))


def load_player_page(pid):
    """Season rows (regular season) from a player page.

    Returns {"pitch": {year: {"IPouts", "BF", "WAR"}}, "bat": {year: {"PA", "WAR"}}}
    Multi-team seasons use the combined (e.g. '2TM') row when present. Falls
    back to data/raw/pitching_tables/<pid>.html (pitching only) if the full
    page is not cached.
    """
    if os.path.exists(os.path.join(RAW, f"player_{pid}.html")):
        html = _read_html(f"player_{pid}.html")
    else:
        html = _read_html(os.path.join("pitching_tables", f"{pid}.html"))
    res = {"pitch": {}, "bat": {}}
    specs = [
        ("pitch", "players_standard_pitching", {"p_ip": "IP", "p_bfp": "BF", "p_war": "WAR"}),
        ("bat", "players_standard_batting", {"b_pa": "PA", "b_war": "WAR"}),
    ]
    for kind, tid, fields in specs:
        per_year = defaultdict(list)
        for rattrs, c, _ in table_rows(html, tid):
            y = c.get("year_id", "")
            if not re.fullmatch(r"\d{4}", y):
                continue
            team = c.get("team_name_abbr", "")
            per_year[int(y)].append((team, c))
        for y, rows in per_year.items():
            combined = [c for t, c in rows if re.fullmatch(r"\d+TM|TOT", t)]
            use = combined[:1] if combined else [c for _, c in rows]
            s = defaultdict(float)
            for c in use:
                for k, name in fields.items():
                    if k == "p_ip":
                        s["IPouts"] += ip_to_outs(c.get(k, "0"))
                    else:
                        s[name] += num(c.get(k))
            res[kind][y] = s
    return res


def load_player_career(pid):
    """Published career totals (the 'N Yrs' footer rows) from a player page.

    Returns {"pitch": {"IPouts", "BF", "WAR"}, "bat": {"PA", "WAR"}}; missing
    tables give empty dicts.
    """
    path = os.path.join(RAW, f"player_{pid}.html")
    if not os.path.exists(path):
        return None
    html = _read_html(f"player_{pid}.html")
    out = {"pitch": {}, "bat": {}}
    specs = [
        ("pitch", "players_standard_pitching", {"p_ip": "IPouts", "p_bfp": "BF", "p_war": "WAR"}),
        ("bat", "players_standard_batting", {"b_pa": "PA", "b_war": "WAR"}),
    ]
    for kind, tid, fields in specs:
        for _, c, _ in table_rows(html, tid):
            if re.fullmatch(r"\d+ Yrs?", c.get("year_id", "")):
                for k, name in fields.items():
                    if k in c and c[k] != "":
                        out[kind][name] = ip_to_outs(c[k]) if k == "p_ip" else num(c[k])
                break
    return out


def load_war_leaderboard():
    """Career WAR leaderboard: {pid: {"WAR", "PA", "IPouts"}} (published totals)."""
    html = _read_html("WAR_career.html")
    out = {}
    m = re.search(r'<table\b[^>]*id="leader_standard_WAR"', html)
    if not m:
        return out
    body = html[m.end():html.find("</table>", m.end())]
    for rm in _ROW.finditer(body):
        tds = re.findall(r"<td\b[^>]*>(.*?)</td>", rm.group(2), re.S)
        link = re.search(r'/players/\w/(\w+)\.shtml', rm.group(2))
        if not link or len(tds) < 5:
            continue
        vals = [htmllib.unescape(_TAG.sub("", t)).strip() for t in tds]
        out[link.group(1)] = {"WAR": num(vals[2]), "PA": num(vals[3]),
                              "IPouts": ip_to_outs(vals[4]) if vals[4] else 0}
    return out


# ---------------------------------------------------------------------------
# Statistics
# ---------------------------------------------------------------------------
def z_alpha(w, n, alpha=0.5):
    return w / max(n, 1.0) ** alpha


def z2d(w_pos, pa, w_pitch, bf):
    i = w_pos * abs(w_pos) / max(pa, 1) + w_pitch * abs(w_pitch) / max(bf, 1)
    return math.copysign(math.sqrt(abs(i)), i)


def z2d_alpha(w_pos, pa, w_pitch, bf, alpha=0.5):
    """Signed two-coordinate combination for any exponent: sgn(I) sqrt|I| with
    I = sum_k W_k |W_k| / N_k^(2 alpha). alpha = 1/2 reproduces z2d."""
    i = (w_pos * abs(w_pos) / max(pa, 1) ** (2 * alpha)
         + w_pitch * abs(w_pitch) / max(bf, 1) ** (2 * alpha))
    return math.copysign(math.sqrt(abs(i)), i)


def z2d_lgamma(w_pos, pa, w_pitch, bf, alpha=0.5):
    """Value-consistent two-coordinate combination (l_gamma rule, Appendix):
    with gamma = 1/(1 - alpha),
        I = sum_k sgn(W_k) |W_k|^gamma / max(N_k, 1)^(gamma - 1)
          = sum_k sgn(Z_k) |Z_k|^gamma   (Z_k = W_k / N_k^alpha, since alpha*gamma = gamma - 1)
        Z = sgn(I) |I|^(1/gamma).
    alpha = 0 gives total WAR, alpha = 1/2 reproduces z2d (signed quadrature),
    and alpha >= 1 - 1e-12 evaluates the exact alpha -> 1^- limit (larger |Z_k|
    with Z_k = W_k / max(N_k, 1), breaking exact opposite-sign ties by larger
    floored exposure max(N_k, 1), returning 0.0 if exposures also coincide).
    Factoring out m = max(|Z_k|) prevents float overflow for alpha near 1."""
    if alpha == 0.0:
        return float(w_pos + w_pitch)
    n1 = max(pa, 1.0)
    n2 = max(bf, 1.0)
    if alpha >= 1.0 - 1e-12:
        z1 = w_pos / n1
        z2 = w_pitch / n2
        az1, az2 = abs(z1), abs(z2)
        if az1 != az2:
            return z1 if az1 > az2 else z2
        if z1 == z2:
            return z1
        if n1 != n2:
            return z1 if n1 > n2 else z2
        return 0.0
    g = 1.0 / (1.0 - alpha)
    z1 = w_pos / (n1 ** alpha)
    z2 = w_pitch / (n2 ** alpha)
    m = max(abs(z1), abs(z2))
    if m == 0.0:
        return 0.0
    i = sum(math.copysign((abs(z) / m) ** g, z)
            for z in (z1, z2) if z != 0.0)
    if i == 0.0:
        return 0.0
    return m * math.copysign(abs(i) ** (1.0 / g), i)


def auc(scores, labels):
    """Area under the ROC curve via the Mann-Whitney statistic (ties = 1/2)."""
    s = np.asarray(scores, float)
    y = np.asarray(labels, bool)
    n1, n0 = y.sum(), (~y).sum()
    if n1 == 0 or n0 == 0:
        return float("nan")
    ranks = rankdata(s)
    return (ranks[y].sum() - n1 * (n1 + 1) / 2) / (n1 * n0)


def bootstrap_auc_diff(sa, sb, labels, n_boot=2000, seed=12345, stratified=True):
    """95% percentile CI for AUC(sa) - AUC(sb), resampling players.

    Stratified by outcome so every resample keeps the same number of Hall of
    Famers (important when positives are rare, e.g. relief pitchers)."""
    rng = np.random.default_rng(seed)
    sa, sb, y = np.asarray(sa, float), np.asarray(sb, float), np.asarray(labels, bool)
    pos, neg = np.flatnonzero(y), np.flatnonzero(~y)
    diffs = []
    for _ in range(n_boot):
        if stratified:
            idx = np.concatenate([rng.choice(pos, len(pos)), rng.choice(neg, len(neg))])
        else:
            idx = rng.integers(0, len(y), len(y))
        diffs.append(auc(sa[idx], y[idx]) - auc(sb[idx], y[idx]))
    lo, hi = np.percentile(diffs, [2.5, 97.5])
    return float(lo), float(hi)


def bootstrap_auc_ci(s, labels, n_boot=2000, seed=12345):
    rng = np.random.default_rng(seed)
    s, y = np.asarray(s, float), np.asarray(labels, bool)
    pos, neg = np.flatnonzero(y), np.flatnonzero(~y)
    vals = []
    for _ in range(n_boot):
        idx = np.concatenate([rng.choice(pos, len(pos)), rng.choice(neg, len(neg))])
        vals.append(auc(s[idx], y[idx]))
    lo, hi = np.percentile(vals, [2.5, 97.5])
    return float(lo), float(hi)


def spearman(a, b):
    ra = rankdata(np.asarray(a, float))
    rb = rankdata(np.asarray(b, float))
    return float(np.corrcoef(ra, rb)[0, 1])


def spw(seasons, threshold, unit):
    """Gordon's Standardized Peak WAR (BRJ 52(1), 2023).

    seasons: iterable of (WAR, exposure). Seasons are sorted by WAR per `unit`
    exposure (descending) and WAR is cumulated until `threshold` exposure,
    interpolating within the season that crosses it. Players whose career
    exposure is below the threshold get their career WAR.
    """
    seasons = list(seasons)
    total_n = sum(n for _, n in seasons if n > 0)
    total_w = sum(w for w, _ in seasons)
    if total_n < threshold:
        return total_w
    seasons = [(w, n) for w, n in seasons if n > 0]
    seasons.sort(key=lambda t: t[0] / t[1] * unit, reverse=True)
    cum_w = cum_n = 0.0
    for w, n in seasons:
        if cum_n + n >= threshold:
            frac = (threshold - cum_n) / n
            return cum_w + frac * w
        cum_w += w
        cum_n += n
    return cum_w


def write_csv(name, header, rows):
    path = os.path.join(OUT, name)
    with open(path, "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(header)
        w.writerows(rows)
    return path
