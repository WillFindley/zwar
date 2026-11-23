#!/usr/bin/env python3
"""Download the raw Baseball-Reference inputs used by the ZWAR reproduction.

This is the ONLY script in the pipeline that touches the network. Everything
else reads the cached files under data/raw/.

Baseball-Reference asks automated clients to stay under 20 requests/minute;
we sleep REQUEST_GAP seconds between requests and skip files already cached.

Usage:
    python3 fetch_data.py                   # fetch anything not yet cached
    python3 fetch_data.py --pitcher-tables  # also: season pitching table for every
                                            # pitcher on the SP/RP JAWS pages (~70 min)
    python3 fetch_data.py --standings       # also: franchise histories (pennant races)
    python3 fetch_data.py --awards          # also: award voting and All-Star selections
                                            # (Chadwick Baseball Databank, 4 files)
    python3 fetch_data.py --refresh         # re-download everything
"""
import os
import re
import sys
import time
import urllib.request

ROOT = os.path.dirname(os.path.abspath(__file__))
RAW = os.path.join(ROOT, "data", "raw")
REQUEST_GAP = 4.0  # seconds; 15 requests/minute
UA = "Mozilla/5.0 (ZWAR reproduction script; contact findley@gmail.com)"

BREF = "https://www.baseball-reference.com"
FG_API = ("https://www.fangraphs.com/api/leaders/major-league/data"
          "?pos=all&lg=all&qual=0&type=8&season=2026&month=0&season1=1871"
          "&ind=0&pageitems=1000&pagenum=1&sortdir=default&sortstat=WAR")

# Season-level WAR tables published by Baseball-Reference and FanGraphs leaderboards.
FILES = {
    "war_daily_bat.txt": f"{BREF}/data/war_daily_bat.txt",
    "war_daily_pitch.txt": f"{BREF}/data/war_daily_pitch.txt",
    "WAR_career.html": f"{BREF}/leaders/WAR_career.shtml",
    "fangraphs_bat.json": f"{FG_API}&stats=bat",
    "fangraphs_pit.json": f"{FG_API}&stats=pit",
}

# JAWS position leaderboards (career WAR, WAR7, JAWS, HOF flag, career stats).
for pos in ["C", "1B", "2B", "3B", "SS", "LF", "CF", "RF", "SP", "RP"]:
    FILES[f"jaws_{pos}.html"] = f"{BREF}/leaders/jaws_{pos}.shtml"

# Player pages for active players and for the season-checkpoint examples.
PLAYERS = {
    # active / recently active players cited in the paper
    "skenepa01": "Paul Skenes",
    "troutmi01": "Mike Trout",
    "ohtansh01": "Shohei Ohtani",
    "chapmar01": "Aroldis Chapman",
    "janseke01": "Kenley Jansen",
    "kimbrcr01": "Craig Kimbrel",
    "kershcl01": "Clayton Kershaw",
    # season-checkpoint examples
    "goodedw01": "Dwight Gooden",
    "linceti01": "Tim Lincecum",
    "pujolal01": "Albert Pujols",
    "griffke02": "Ken Griffey Jr.",
    # two-way players / pitcher batting lines whose BF or PA are not on JAWS pages
    "ruthba01": "Babe Ruth",
    "wardjo01": "John Montgomery Ward",
    "dihigma99": "Martin Dihigo",
    "wallabo01": "Bobby Wallace",
    "youngcy01": "Cy Young",
    "grovele01": "Lefty Grove",
    "nichoki01": "Kid Nichols",
    "alexape01": "Grover Alexander",
    "johnsra05": "Randy Johnson",
    "mathech01": "Christy Mathewson",
    "johnswa01": "Walter Johnson",
    "ferrewe01": "Wes Ferrell",
    "ruffire01": "Red Ruffing",
    # SPW validation against Gordon (2023): exact season BF
    "martipe02": "Pedro Martinez",
    "koufasa01": "Sandy Koufax",
    "riverma01": "Mariano Rivera",
}
for pid in PLAYERS:
    FILES[f"player_{pid}.html"] = f"{BREF}/players/{pid[0]}/{pid}.shtml"


def fetch(url, dest):
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    with urllib.request.urlopen(req, timeout=120) as resp:
        data = resp.read()
    tmp = dest + ".part"
    with open(tmp, "wb") as fh:
        fh.write(data)
    os.replace(tmp, dest)
    return len(data)


def fetch_pitching_table(pid, dest):
    """Save only the regular-season standard pitching table of a player page
    (about 2% of the page), which carries season BF."""
    url = f"{BREF}/players/{pid[0]}/{pid}.shtml"
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    with urllib.request.urlopen(req, timeout=120) as resp:
        html = resp.read().decode("utf-8", "replace").replace("<!--", "").replace("-->", "")
    m = re.search(r'<table\b[^>]*\bid="players_standard_pitching"', html)
    if not m:
        raise ValueError("no players_standard_pitching table")
    seg = html[m.start():html.find("</table>", m.end()) + len("</table>")]
    with open(dest, "w", encoding="utf-8") as fh:
        fh.write(seg)
    return len(seg)


def jaws_pitcher_ids():
    ids = []
    for pos in ("SP", "RP"):
        path = os.path.join(RAW, f"jaws_{pos}.html")
        if os.path.exists(path):
            with open(path, encoding="utf-8") as fh:
                ids += re.findall(r'data-append-csv="([^"]+)" data-stat="player"', fh.read())
    return list(dict.fromkeys(ids))


def bulk_pitching_tables(refresh):
    """Exact season BF for every pitcher on the SP/RP JAWS pages."""
    out_dir = os.path.join(RAW, "pitching_tables")
    os.makedirs(out_dir, exist_ok=True)
    ids = jaws_pitcher_ids()
    todo = [p for p in ids if refresh or not (
        os.path.exists(os.path.join(out_dir, f"{p}.html"))
        or os.path.exists(os.path.join(RAW, f"player_{p}.html")))]
    print(f"pitching tables: {len(ids)} pitchers, {len(todo)} to fetch "
          f"(~{len(todo) * REQUEST_GAP / 60:.0f} min)", flush=True)
    for i, pid in enumerate(todo, 1):
        time.sleep(REQUEST_GAP)
        try:
            n = fetch_pitching_table(pid, os.path.join(out_dir, f"{pid}.html"))
            if i % 25 == 0 or i == len(todo):
                print(f"  [{i}/{len(todo)}] {pid} ({n:,} bytes)", flush=True)
        except Exception as exc:
            print(f"  FAILED {pid}: {exc}", flush=True)
            if "429" in str(exc):
                print("  rate limited; stopping. Re-run later to resume.", flush=True)
                return


# Franchise histories (season W, L, finish, postseason result) for every AL/NL
# team-season since 1901: the 30 current franchises (OAK covers all 1901-2026
# Athletics AL seasons) plus the 1901-02 Baltimore Orioles (BLA); ATH is the
# 1876 NL Philadelphia Athletic (filtered out by FIRST = 1901). Used for the
# season-value convexity estimate (12_season_value.py).
FRANCHISES = ["ANA", "ARI", "ATH", "ATL", "BAL", "BOS", "CHC", "CHW", "CIN", "CLE",
              "COL", "DET", "FLA", "HOU", "KCR", "LAD", "MIL", "MIN", "NYM", "NYY",
              "PHI", "PIT", "SDP", "SEA", "SFG", "STL", "TBD", "TEX", "TOR", "WSN", "BLA", "OAK"]


def franchise_histories(refresh):
    out_dir = os.path.join(RAW, "teams")
    os.makedirs(out_dir, exist_ok=True)
    fetched = 0
    for code in FRANCHISES:
        dest = os.path.join(out_dir, f"{code}.html")
        if os.path.exists(dest) and not refresh:
            continue
        time.sleep(REQUEST_GAP)
        try:
            n = fetch(f"{BREF}/teams/{code}/", dest)
            fetched += 1
            print(f"fetched  teams/{code}.html ({n:,} bytes)", flush=True)
        except Exception as exc:
            print(f"FAILED   teams/{code}.html: {exc}", flush=True)
    if fetched:
        with open(os.path.join(out_dir, "FETCHED_AT.txt"), "w") as fh:
            fh.write(time.strftime("%Y-%m-%d %H:%M:%S %Z") + "\n")


# Award voting and All-Star selections (Lahman / Chadwick Baseball Databank),
# used for the award- and All-Star-based benchmarks (15_forecast_benchmarks.py).
# The Chadwick Bureau repository is no longer online; the last public snapshot
# (January 2020: award voting through 2016, All-Star rosters through 2019) is
# mirrored in the source data of the CRAN `Lahman` package repository. The
# Databank's playerID matches Baseball-Reference's player_ID for nearly all
# players; People.csv carries the explicit bbrefID mapping.
DATABANK_ZIP = "https://github.com/cdalzell/Lahman/raw/HEAD/source-data/baseballdatabank-master.zip"
DATABANK_FILES = ["AwardsSharePlayers.csv", "AwardsPlayers.csv", "AllstarFull.csv", "People.csv"]


def databank(refresh):
    import io
    import zipfile
    out_dir = os.path.join(RAW, "databank")
    os.makedirs(out_dir, exist_ok=True)
    if not refresh and all(os.path.exists(os.path.join(out_dir, f)) for f in DATABANK_FILES):
        print("cached   databank/")
        return
    try:
        req = urllib.request.Request(DATABANK_ZIP, headers={"User-Agent": UA})
        with urllib.request.urlopen(req, timeout=300) as resp:
            zf = zipfile.ZipFile(io.BytesIO(resp.read()))
    except Exception as exc:
        print(f"FAILED   databank: {exc}", flush=True)
        return
    for name in DATABANK_FILES:
        with open(os.path.join(out_dir, name), "wb") as fh:
            fh.write(zf.read(f"baseballdatabank-master/core/{name}"))
        print(f"fetched  databank/{name}", flush=True)
    with open(os.path.join(out_dir, "FETCHED_AT.txt"), "w") as fh:
        fh.write(time.strftime("%Y-%m-%d %H:%M:%S %Z") + "\n")


def main():
    refresh = "--refresh" in sys.argv
    os.makedirs(RAW, exist_ok=True)
    first, fetched = True, 0
    for name, url in FILES.items():
        dest = os.path.join(RAW, name)
        if os.path.exists(dest) and not refresh:
            print(f"cached   {name}")
            continue
        if not first:
            time.sleep(REQUEST_GAP)
        first = False
        try:
            n = fetch(url, dest)
            fetched += 1
            print(f"fetched  {name} ({n:,} bytes)", flush=True)
        except Exception as exc:  # keep going; report at the end
            print(f"FAILED   {name}: {exc}", flush=True)
    if "--pitcher-tables" in sys.argv:
        bulk_pitching_tables(refresh)
    if "--standings" in sys.argv:
        franchise_histories(refresh)
    if "--awards" in sys.argv:
        databank(refresh)
    if fetched:
        with open(os.path.join(RAW, "FETCHED_AT.txt"), "w") as fh:
            fh.write(time.strftime("%Y-%m-%d %H:%M:%S %Z") + "\n")


if __name__ == "__main__":
    main()
