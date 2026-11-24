#!/usr/bin/env python3
"""All-time leaderboards at alpha = 1/5 (paper Section 6 tables).

Universe and conventions are those of 07_rank_checks.py (zwar/universe.py):
every player in B-Ref's season WAR files; WAR rounded to 0.1 as published;
PA from player pages / JAWS pages / summed seasons; BF from JAWS pages /
player pages / Table 11 secondary BF, else IPouts x 4.2/3; floor max(N, 1);
ties broken by player ID.

Scores, for every player:
  * position play  Z_a = WAR_pos / PA^a
  * pitching       Z_a = WAR_pitch / BF^a
  * unified        Z_a = sgn(I) |I|^(1/g), I = sum_k sgn(W_k)|W_k|^g / N_k^(g-1),
                   g = 1/(1-a)  (l_gamma rule, common.z2d_lgamma: total WAR at a = 0,
                   signed quadrature at a = 1/2)
  * pooled         (W_pos + W_pitch) / (PA + BF)^a                       (two-way table only)
Ranks at alpha = 0 (career WAR; for the unified board the l_gamma score at
alpha = 0, i.e. total WAR; standard
competition ranks '1224' because published WAR ties often), alpha = 0.2 and
alpha = 0.5 (strict ranks, ties by player ID, as in 07).
Sub-pool ranks: SP = SP JAWS page with >= 1,500 IP; RP = RP JAWS page;
two-way = the 18 players with >= 10 WAR in both coordinates.

Outputs: outputs/leaderboard_{pos,pitch,unified}.csv,
         outputs/tables/tab_{hitters,pitchers,relievers,twoway,unified}.tex,
         outputs/tables/table_values.py (values shown in the tables, the
         input to the table checks in 07_rank_checks.py),
         outputs/tables/ties.csv (adjacent near-ties at alpha = 0.2).
"""
import os
import pprint
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import HITTER_POS, OUT, load_jaws, write_csv, z2d  # noqa: E402
import universe as U  # noqa: E402

A = 0.2                 # headline exponent (gamma = 1.25)
ALPHAS = (0.0, 0.2, 0.5)
TIE = 0.10              # proposed resolution of Z_0.2 (cf. 0.005 for Z_1/2)
SP_MIN_OUTS = 4500      # 1,500 IP
TAB = os.path.join(OUT, "tables")
os.makedirs(TAB, exist_ok=True)

# Display names (B-Ref "name_common" differs from the paper's usage for a few)
NAME = {"aaronha01": "Hank Aaron", "martipe02": "Pedro Mart\\'{i}nez", "dihigma99": "Mart\\'{i}n Dihigo",
        "wardjo01": "John Montgomery Ward"}

# ---- row selections -------------------------------------------------------
N_TOP_HIT, N_TOP_SP, N_TOP_UNI = 15, 15, 25
HIT_ILLUS = ["troutmi01", "dimagjo01", "robinja02", "steartu99", "gibsojo99", "rosepe01"]
SP_ILLUS = ["kershcl01", "ryanno01", "paigesa01", "fostebi99"]
RP_SET = ["riverma01", "eckerde01", "wilheho01", "gossari01", "wagnebi02", "chapmar01",
          "nathajo01", "papeljo01", "hillejo01", "hoffmtr01", "henketo01", "smithle02",
          "janseke01", "kimbrcr01", "suttebr01"]
N_TOP_RP = 3            # plus the top relievers by Z_0.2 not already listed
# Roles as labelled in the paper; others by rp_role() (starts / IP per relief game)
RP_ROLE = {"riverma01": "Pure RP", "eckerde01": "SP/RP Hybrid", "wilheho01": "Multi-IP RP",
           "gossari01": "Multi-IP RP", "hillejo01": "Multi-IP RP"}
RP_BENCH = {"johnsra05": "HOF SP", "seaveto01": "HOF SP", "ryanno01": "HOF SP",
            "fellebo01": "HOF SP", "suttodo01": "300-Win HOF SP", "maricju01": "HOF SP",
            "bunniji01": "HOF SP", "koufasa01": "HOF SP", "fordwh01": "HOF SP",
            "wynnea01": "300-Win HOF SP", "morrija02": "HOF SP"}
UNI_ILLUS = ["grovele01", "troutmi01", "martipe02", "johnsra05", "seaveto01", "maddugr01", "mathech01",
             "kershcl01", "rosepe01", "robinja02", "steartu99", "riverma01", "gibsojo99",
             "ohtansh01", "roganbu99"]

# Role profiles of the 18 two-way players (from their B-Ref pages)
ROLE2 = {"ruthba01": "SP $\\to$ OF", "johnswa01": "SP + Hit/PH", "ohtansh01": "SP + DH",
         "roganbu99": "NgL SP + OF", "ferrewe01": "SP + Hit/PH", "ruffire01": "SP + Hit/PH",
         "carutbo01": "SP + OF", "wardjo01": "SP $\\to$ SS", "dihigma99": "NgL UT + SP",
         "uhlege01": "SP + Hit/PH", "lemonbo01": "3B/OF $\\to$ SP", "smithel01": "SP $\\to$ OF",
         "lucasre01": "SP + PH", "woodjo02": "SP $\\to$ OF", "seymocy01": "SP $\\to$ OF",
         "mullige01": "SP + Hit", "foutzda01": "SP $\\to$ 1B/OF", "rileed01": "NgL SP + 1B"}
# Position labels for the unified table (JAWS page position otherwise)
POSLAB = {"ruthba01": "OF / SP", "musiast01": "OF / 1B", "rodrial01": "SS / 3B",
          "robinfr02": "OF", "johnswa01": "SP / PH", "rosepe01": "OF / IF",
          "ohtansh01": "DH / SP", "roganbu99": "SP / OF", "henderi01": "LF"}
NGL = {"steartu99", "gibsojo99", "roganbu99", "fostebi99", "paigesa01", "dihigma99", "rileed01"}


# ---- formatting -------------------------------------------------------------
def f2(x):
    s = f"{x:.2f}"
    if s == "-0.00":
        s = "0.00"
    return f"${s}$" if s.startswith("-") else s


def f1(x):
    s = f"{x:.1f}"
    if s == "-0.0":
        s = "0.0"
    return f"${s}$" if s.startswith("-") else s


def thou(x):
    return f"{int(round(x)):,}"


def ip_str(outs):
    outs = int(round(outs))
    return f"{outs // 3:,}.{outs % 3}"


def pct(new, base):
    return f"${100 * (new / base - 1):+.1f}\\%$"


def bold(s):
    return f"\\textbf{{{s}}}"


def emph(s):
    return f"\\emph{{{s}}}"


def table(label, caption, colspec, header, rows, tabcolsep="5pt", midrule_after=None):
    out = ["\\begin{table}[htbp]", "\\centering", f"\\caption{{{caption}}}", f"\\label{{{label}}}",
           "\\footnotesize", f"\\setlength{{\\tabcolsep}}{{{tabcolsep}}}",
           "\\resizebox{\\textwidth}{!}{%", f"\\begin{{tabular}}{{{colspec}}}", "\\toprule"]
    out += [h + " \\\\" for h in header]
    out.append("\\midrule")
    for i, r in enumerate(rows):
        out.append(" & ".join(r) + " \\\\")
        if midrule_after and i + 1 in midrule_after and i + 1 < len(rows):
            out.append("\\midrule")
    out += ["\\bottomrule", "\\end{tabular}%", "}", "\\end{table}", ""]
    return "\n".join(out)


def main():
    u = U.build()
    pids, bat, pitch, jaws = u["pids"], u["bat"], u["pitch"], u["jaws"]
    pw, pn, tw, tn, outs = u["pos_w"], u["pos_n"], u["pit_w"], u["pit_n"], u["ipouts"]

    def nm(p):
        return NAME.get(p) or (bat.get(p) or pitch.get(p))["name"]

    # ---- scores and ranks -----------------------------------------------
    zpos = {a: {p: pw[p] / max(pn[p], 1) ** a for p in bat} for a in ALPHAS}
    zpit = {a: {p: tw[p] / max(tn[p], 1) ** a for p in pitch} for a in ALPHAS}
    zuni = {a: U.unified_scores(u, a) for a in ALPHAS}    # alpha = 0: total WAR
    zquad = {p: z2d(pw[p], pn[p], tw[p], tn[p]) for p in pids}
    # identical up to float noise (1e-16; only an exact tie deep in the table can swap)
    assert max(abs(zquad[p] - zuni[0.5][p]) for p in pids) < 1e-12, "l_gamma at 1/2 must equal quadrature"
    assert all(abs(zuni[0.0][p] - (pw[p] + tw[p])) < 1e-9 for p in pids), "l_gamma at 0 must be total WAR"
    zpool = {p: (pw[p] + tw[p]) / max(pn[p] + tn[p], 1) ** A for p in pids}

    def ranks(sc):
        return {0.0: U.min_ranks(sc[0.0]), 0.2: U.ranking(sc[0.2])[0], 0.5: U.ranking(sc[0.5])[0]}
    rpos, rpit, runi = ranks(zpos), ranks(zpit), ranks(zuni)
    order = {"pos": U.ranking(zpos[A])[1], "pitch": U.ranking(zpit[A])[1], "unified": U.ranking(zuni[A])[1]}

    # Sub-pools
    sp_pool = [d["pid"] for d in load_jaws("SP") if d["IPouts"] >= SP_MIN_OUTS]
    rp_pool = [d["pid"] for d in load_jaws("RP")]
    two_pool = [p for p in pids if pw[p] >= 10 and tw[p] >= 10]
    # Radon's inequality: l_gamma >= pooled for non-negative coordinates
    radon = {p: zuni[A][p] - zpool[p] for p in two_pool}
    assert all(v >= -1e-12 for v in radon.values()), "Radon's inequality violated"

    def sub(pool, sc):
        return U.ranking({p: sc[p] for p in pool})[0]
    rsp = {a: sub(sp_pool, zpit[a]) for a in (0.2, 0.5)}
    rrp = {a: sub(rp_pool, zpit[a]) for a in (0.2, 0.5)}
    r2w = {a: sub(two_pool, zuni[a]) for a in (0.2, 0.5)}

    # JAWS ranks (as 08_jaws_check.py: hitters across 8 positions; SP / RP pages)
    def jrank(players, key):
        sc = {d["pid"]: (d[key] if d[key] is not None else -1e9) for d in players}
        return U.min_ranks(sc)
    hit_j = [d for pos in HITTER_POS for d in load_jaws(pos)]
    sp_j, rp_j = load_jaws("SP"), load_jaws("RP")
    r_jh, r_jsp, r_sjsp, r_rj = jrank(hit_j, "JAWS"), jrank(sp_j, "JAWS"), jrank(sp_j, "S_JAWS"), jrank(rp_j, "R_JAWS")

    # Rounding sensitivity of Z_0.2 to +-0.05 WAR in each coordinate
    def rbound(p, coord):
        if coord == "pos":
            return 0.05 / max(pn[p], 1) ** A
        if coord == "pitch":
            return 0.05 / max(tn[p], 1) ** A
        # dZ/dW_k = (|W_k| / N_k)^(g-1) |I|^(1/g - 1) for the l_gamma rule
        g = 1.0 / (1.0 - A)
        z = abs(zuni[A][p]) or 1e-9
        return sum(0.05 * (abs(w) / max(n, 1)) ** (g - 1) * z ** (1 - g)
                   for w, n in ((pw[p], pn[p]), (tw[p], tn[p])) if w != 0) or 0.05 / max(pn[p] + tn[p], 1) ** A

    # ---- CSVs ------------------------------------------------------------
    hdr = ["rank_Z0.2", "pid", "name"]
    rows = []
    for p in order["pos"]:
        j = jaws.get(p, {})
        rows.append([rpos[0.2][p], p, nm(p), pw[p], int(pn[p]), round(650 * pw[p] / max(pn[p], 1), 3),
                     round(zpos[0.2][p], 4), round(zpos[0.5][p], 4), rpos[0.0][p], rpos[0.5][p],
                     j.get("pos", "") if j.get("pos") in HITTER_POS else "", j.get("JAWS", "") if p in r_jh else "",
                     r_jh.get(p, ""), round(rbound(p, "pos"), 4)])
    write_csv("leaderboard_pos.csv", hdr + ["WAR_pos", "PA", "WAR_per650", "Z0.2", "Z0.5", "rank_WAR",
                                            "rank_Z0.5", "jaws_pos", "JAWS", "JAWS_rank_8pos",
                                            "Z0.2_rounding_bound"], rows)
    rows = []
    for p in order["pitch"]:
        j = jaws.get(p, {})
        rows.append([rpit[0.2][p], p, nm(p), tw[p], round(tn[p], 1), int(p in u["approx"]), ip_str(outs[p]),
                     round(tn[p] / max(outs[p] / 3, 1e-9), 3) if outs[p] else "",
                     round(820 * tw[p] / max(tn[p], 1), 3), round(zpit[0.2][p], 4), round(zpit[0.5][p], 4),
                     rpit[0.0][p], rpit[0.5][p], rsp[0.2].get(p, ""), rsp[0.5].get(p, ""),
                     rrp[0.2].get(p, ""), rrp[0.5].get(p, ""),
                     j.get("pos", "") if j.get("pos") in ("SP", "RP") else "",
                     j.get("JAWS", "") if (p in r_jsp or p in r_rj) else "",
                     r_jsp.get(p, ""), j.get("S_JAWS", "") if p in r_sjsp else "", r_sjsp.get(p, ""),
                     j.get("R_JAWS", "") if p in r_rj else "", r_rj.get(p, ""), round(rbound(p, "pitch"), 4)])
    write_csv("leaderboard_pitch.csv", hdr + [
        "WAR_pitch", "BF", "BF_approx", "IP", "BF_per_IP", "WAR_per820", "Z0.2", "Z0.5", "rank_WAR",
        "rank_Z0.5", "SP_rank_Z0.2", "SP_rank_Z0.5", "RP_rank_Z0.2", "RP_rank_Z0.5", "jaws_page", "JAWS",
        "JAWS_rank_SP", "S_JAWS", "S_JAWS_rank", "R_JAWS", "R_JAWS_rank", "Z0.2_rounding_bound"], rows)
    rows = []
    for p in order["unified"]:
        rows.append([runi[0.2][p], p, nm(p), pw[p], int(pn[p]), tw[p], round(tn[p], 1),
                     round(pw[p] + tw[p], 1), round(zpos[0.2].get(p, 0.0), 4), round(zpit[0.2].get(p, 0.0), 4),
                     round(zuni[0.2][p], 4), round(zuni[0.5][p], 4), round(zpool[p], 4),
                     runi[0.0][p], runi[0.5][p], rpos[0.2].get(p, ""), rpit[0.2].get(p, ""),
                     r2w[0.2].get(p, ""), round(rbound(p, "unified"), 4)])
    write_csv("leaderboard_unified.csv", hdr + [
        "WAR_pos", "PA", "WAR_pitch", "BF", "WAR_total", "Zpos0.2", "Zpitch0.2", "Z0.2", "Z0.5", "Zpool0.2",
        "rank_WAR_total", "rank_Z0.5", "pos_rank_Z0.2", "pitch_rank_Z0.2", "twoway18_rank_Z0.2",
        "Z0.2_rounding_bound"], rows)

    # Values shown in the tables, collected for 07_rank_checks.py
    shown = {"pos": {}, "pitch": {}, "unified": {}, "sp": {}, "rp": {}, "twoway": {}}

    def rec(coord, p):
        sc, rk = {"pos": (zpos, rpos), "pitch": (zpit, rpit), "unified": (zuni, runi)}[coord]
        shown[coord][p] = (nm(p), round(sc[A][p], 2), rk[0.0][p], rk[0.2][p], rk[0.5][p])

    # ---- Table: hitters ------------------------------------------------------
    sel = order["pos"][:N_TOP_HIT] + sorted(HIT_ILLUS, key=lambda p: rpos[0.2][p])
    rates = {p: 650 * pw[p] / pn[p] for p in sel}
    top_rates = sorted(rates.values(), reverse=True)[:2]
    rows = []
    for p in sel:
        rec("pos", p)
        rt = f"{rates[p]:.2f}"
        rows.append([bold(rpos[0.2][p]), nm(p), f1(pw[p]), thou(pn[p]),
                     bold(rt) if rates[p] >= top_rates[-1] else rt,
                     f"{jaws[p]['JAWS']:.1f} (\\#{r_jh[p]})", str(rpos[0.0][p]), str(rpos[0.5][p]),
                     bold(f2(zpos[A][p]))])
    cap = ("Position-play coordinate at $\\alpha = \\tfrac15$, $Z_{1/5} = \\WAR_{\\mathrm{pos}} / \\max(\\PA, 1)^{1/5}$ "
           "(position-player $\\mathrm{bWAR}$) \\cite{bbref2026}, sorted by $Z_{1/5}$. All ranks are all-time "
           "position-play ranks: $\\WAR$ \\textbf{Rk} is the career-$\\WAR$ rank ($\\alpha = 0$; tied totals share "
           "the better rank) and $Z_{1/2}$ \\textbf{Rk} the rank under $\\Zpos = \\WAR_{\\mathrm{pos}}/\\sqrt{\\PA}$. "
           "$\\JAWS$ ranks are across all eight fielding positions combined. The full two-coordinate valuation "
           "appears in Tables~\\ref{tab:twoway}--\\ref{tab:unified}.")
    hdr = ["$Z_{1/5}$ \\textbf{Rk} & \\textbf{Player} & \\textbf{Pos $\\WAR$} & \\textbf{Career $\\PA$} & "
           "$\\WAR / 650\\text{ }\\PA$ & $\\JAWS$ \\textbf{(Rk)} & $\\WAR$ \\textbf{Rk} & $Z_{1/2}$ \\textbf{Rk} & "
           "$Z_{1/5} = \\dfrac{\\WAR_{\\mathrm{pos}}}{\\PA^{1/5}}$"]
    tex = table("tab:hitters", cap, "@{}clccccccc@{}", hdr, rows, "5pt", [N_TOP_HIT])
    open(os.path.join(TAB, "tab_hitters.tex"), "w").write(tex)
    tie_sets = {"tab:hitters": ("pos", sel)}

    # ---- Table: starting pitchers ---------------------------------------------
    sp_order = sorted(sp_pool, key=lambda p: rsp[0.2][p])
    sel = sp_order[:N_TOP_SP] + sorted(SP_ILLUS, key=lambda p: rsp[0.2][p])
    rates = {p: 820 * tw[p] / tn[p] for p in sel}
    top_rates = sorted(rates.values(), reverse=True)[:2]
    rows = []
    for p in sel:
        rec("pitch", p)
        shown["sp"][p] = (nm(p), rsp[0.2][p], rsp[0.5][p])
        j = jaws[p]
        rt = f"{rates[p]:.2f}"
        rows.append([f"{bold(rsp[0.2][p])} (\\#{rpit[0.2][p]})", nm(p), f1(tw[p]), thou(tn[p]),
                     f"{ip_str(outs[p])} ({tn[p] / (outs[p] / 3):.2f})",
                     bold(rt) if rates[p] >= top_rates[-1] else rt,
                     f"{j['JAWS']:.1f} (\\#{r_jsp[p]})", f"{j['S_JAWS']:.1f} (\\#{r_sjsp[p]})",
                     str(rpit[0.0][p]), f"{rsp[0.5][p]} (\\#{rpit[0.5][p]})", bold(f2(zpit[A][p]))])
    cap = ("Starting pitchers ($\\ge 1{,}500\\,\\IP$) at $\\alpha = \\tfrac15$, $Z_{1/5} = \\WAR_{\\mathrm{pitch}} / "
           "\\max(\\BF, 1)^{1/5}$ (pitching $\\mathrm{bWAR}$) \\cite{bbref2026}, sorted by $Z_{1/5}$. Columns 1 and "
           "10 give the rank among these starters with the rank among \\emph{all} pitchers in parentheses; "
           "$\\WAR$ \\textbf{Rk} ($\\alpha = 0$; tied totals share the better rank) is also among all pitchers, and "
           "$Z_{1/2}$ is $\\Zpitch = \\WAR_{\\mathrm{pitch}}/\\sqrt{\\BF}$. Baseball-Reference $\\JAWS$ and "
           "$\\SJAWS$ include pitcher batting.")
    hdr = ["$Z_{1/5}$ \\textbf{SP Rk} & & \\textbf{Pitch} & \\textbf{Career} & \\textbf{Career $\\IP$} & "
           "$\\WAR\\,/$ & $\\JAWS$ & $\\SJAWS$ & $\\WAR$ & $Z_{1/2}$ \\textbf{SP Rk} & "
           "$Z_{1/5} = $",
           "\\textbf{(All)} & \\textbf{Pitcher} & $\\WAR$ & \\textbf{$\\BF$} & \\textbf{($\\BF/\\IP$)} & "
           "$820\\text{ }\\BF$ & \\textbf{(Rk)} & \\textbf{(Rk)} & \\textbf{Rk} & \\textbf{(All)} & "
           "$\\WAR_{\\mathrm{pitch}}/\\BF^{1/5}$"]
    tex = table("tab:pitchers", cap, "@{}clccccccccc@{}", hdr, rows, "5pt", [N_TOP_SP])
    open(os.path.join(TAB, "tab_pitchers.tex"), "w").write(tex)
    tie_sets["tab:pitchers"] = ("pitch", sel)

    # ---- Table: relievers and HOF starter benchmarks ------------------------
    rp_order = sorted(rp_pool, key=lambda p: rrp[0.2][p])
    extra = [p for p in rp_order if p not in RP_SET][:N_TOP_RP]
    rel = RP_SET + extra
    sel = sorted(rel + list(RP_BENCH), key=lambda p: rpit[0.2][p])

    def rp_role(p):
        if p in RP_ROLE:
            return RP_ROLE[p]
        d = jaws[p]
        relief_g = max(d["G"] - d["GS"], 1)
        if d["GS"] >= 100:
            return "SP/RP Hybrid"
        relief_ip = d["IPouts"] / 3 - d["GS"] * 6.0   # rough: ~6 IP per start
        return "Multi-IP RP" if relief_ip / relief_g >= 1.7 else "Pure RP"
    rows = []
    for p in sel:
        rec("pitch", p)
        j = jaws[p]
        common = [f1(tw[p]) + f" (\\#{rpit[0.0][p]})", thou(tn[p]),
                  f"{ip_str(outs[p])} ({tn[p] / (outs[p] / 3):.2f})", f"{820 * tw[p] / tn[p]:.2f}",
                  f"{j['JAWS']:.1f}"]
        if p in RP_BENCH:
            rows.append([bold(rpit[0.2][p]), "---", emph(f"{nm(p)} ({RP_BENCH[p]})")]
                        + [emph(c) for c in common] + ["---", emph(str(rpit[0.5][p])), emph(f2(zpit[A][p]))])
        else:
            shown["rp"][p] = (nm(p), rrp[0.2][p], rrp[0.5][p])
            rows.append([bold(rpit[0.2][p]), bold(rrp[0.2][p]), f"{bold(nm(p))} ({rp_role(p)})"] + common
                        + [f"{j['R_JAWS']:.1f} (\\#{r_rj[p]})", f"{rpit[0.5][p]} ({rrp[0.5][p]})",
                           bold(f2(zpit[A][p]))])
    cap = ("Relief pitchers and Hall of Fame starter benchmarks (italics) at $\\alpha = \\tfrac15$, $Z_{1/5} = "
           "\\WAR_{\\mathrm{pitch}} / \\max(\\BF, 1)^{1/5}$, sorted by $Z_{1/5}$ across \\emph{all} pitchers "
           "\\cite{bbref2026}. $\\mathrm{RP}$ classification, $\\mathrm{RP}$ ranks (column 2) and $\\RJAWS$ ranks "
           "follow Baseball-Reference's Relief Pitcher JAWS leaderboard \\cite{bbrefjawsrp}; Hybrid roles have "
           "$\\ge 100$ starts. Parenthetical "
           "ranks after pitching $\\WAR$ are career-$\\WAR$ ranks ($\\alpha = 0$) among all pitchers; "
           "$Z_{1/2}$ \\textbf{Rk} is the all-pitcher rank under $\\Zpitch = \\WAR_{\\mathrm{pitch}}/\\sqrt{\\BF}$ "
           "(RP rank in parentheses). Baseball-Reference $\\JAWS$ and $\\RJAWS$ include pitcher batting.")
    hdr = ["\\textbf{All-Pitch} & \\textbf{RP} & \\textbf{Pitcher} & \\textbf{Pitch $\\WAR$} & \\textbf{Career} & "
           "\\textbf{Career $\\IP$} & $\\WAR\\,/$ & & $\\RJAWS$ & $Z_{1/2}$ \\textbf{Rk} & $Z_{1/5} = $",
           "$Z_{1/5}$ \\textbf{Rk} & \\textbf{Rk} & \\textbf{(Role / HOF SP Benchmark)} & \\textbf{(Rk)} & "
           "\\textbf{$\\BF$} & \\textbf{($\\BF/\\IP$)} & $820\\text{ }\\BF$ & $\\JAWS$ & \\textbf{(RP Rk)} & "
           "\\textbf{(RP)} & $\\WAR_{\\mathrm{pitch}}/\\BF^{1/5}$"]
    # midrule between the top-100 block and the rest
    cut = [i + 1 for i in range(len(sel) - 1) if rpit[0.2][sel[i]] <= 100 < rpit[0.2][sel[i + 1]]]
    tex = table("tab:relievers", cap, "@{}cclcccccccc@{}", hdr, rows, "4pt", cut)
    open(os.path.join(TAB, "tab_relievers.tex"), "w").write(tex)
    tie_sets["tab:relievers"] = ("pitch", sel)

    # ---- Table: two-way players ----------------------------------------------
    sel = sorted(two_pool, key=lambda p: r2w[0.2][p])
    rows = []
    for p in sel:
        rec("unified", p)
        zp, zt = zpos[A][p], zpit[A][p]
        base = max(zp, zt)
        shown["twoway"][p] = (nm(p), round(zp, 2), round(zt, 2), round(zpool[p], 2), round(zuni[A][p], 2),
                              r2w[0.2][p], r2w[0.5][p])
        approx = "$^{*}$" if p in u["approx"] else ""
        rows.append([f"{bold(r2w[0.2][p])} (\\#{thou(runi[0.2][p])})", f"{bold(nm(p))} ({ROLE2[p]})",
                     f"{f1(pw[p])} ({thou(pn[p])})", f"{f1(tw[p])} ({thou(tn[p])}{approx} / {ip_str(outs[p])})",
                     f1(pw[p] + tw[p]), bold(f2(zp)) if zp >= zt else f2(zp), bold(f2(zt)) if zt > zp else f2(zt),
                     f"{f2(zpool[p])} ({pct(zpool[p], base)})", str(r2w[0.5][p]),
                     bold(f"{f2(zuni[A][p])} ({pct(zuni[A][p], base)})")])
    approx_names = [nm(p) for p in sel if p in u["approx"]]
    cap = ("Two-coordinate valuation at $\\alpha = \\tfrac15$ for all $n = 18$ players with $\\ge 10\\,\\WAR$ in both "
           "coordinates \\cite{bbref2026}, sorted by the $\\ell_\\gamma$ combination $Z_{1/5,\\mathrm{2D}} = "
           "\\sgn(\\Ical_{1/5})|\\Ical_{1/5}|^{1/\\gamma}$, $\\Ical_{1/5} = \\sum_k \\sgn(\\WAR_k)"
           "|\\WAR_k|^{\\gamma}/N_k^{\\gamma-1}$, with $\\gamma = 1/(1-\\alpha) = \\tfrac54$ at "
           "$\\alpha = \\tfrac15$. $Z_{1/5,\\mathrm{pos}}$ and $Z_{1/5,\\mathrm{pitch}}$ are the single-coordinate $Z_{1/5}$ scores and "
           "$Z_{1/5,\\mathrm{pool}} = (\\WAR_{\\mathrm{pos}} + \\WAR_{\\mathrm{pitch}})/(\\PA + \\BF)^{1/5}$; percentage changes "
           "are relative to $\\max(Z_{1/5,\\mathrm{pos}}, Z_{1/5,\\mathrm{pitch}})$. Column 1 gives the rank among the 18 with the all-time "
           "unified rank in parentheses; $Z_{1/2}$ \\textbf{Rk} is the rank among the 18 under "
           "Equation~\\eqref{eq:universal_zwar} ($\\gamma = 2$). Total $\\WAR$ is the sum of the rounded components "
           "and can differ by $0.1$ from Baseball-Reference's published career totals (e.g., Ruth $182.6$, Ruffing $68.6$)"
           + (f"; $^{{*}}$$\\BF$ estimated at $4.2$ per inning ({', '.join(approx_names)})" if approx_names else "")
           + ".")
    hdr = ["& \\textbf{Player} & \\textbf{Pos $\\WAR$} & \\textbf{Pitch $\\WAR$} & \\textbf{Total} & & & $Z_{1/5,\\mathrm{pool}}$ & "
           "$Z_{1/2}$ & $Z_{1/5,\\mathrm{2D}}$",
           "\\textbf{Rk (All)} & \\textbf{(Role Profile)} & \\textbf{($\\PA$)} & \\textbf{($\\BF$ / $\\IP$)} & "
           "\\textbf{$\\WAR$} & $Z_{1/5,\\mathrm{pos}}$ & $Z_{1/5,\\mathrm{pitch}}$ & \\textbf{($\\Delta\\%$)} & \\textbf{Rk} & "
           "\\textbf{($\\Delta\\%$)}"]
    tex = table("tab:twoway", cap, "@{}clcccccccc@{}", hdr, rows, "4pt", None)
    open(os.path.join(TAB, "tab_twoway.tex"), "w").write(tex)
    tie_sets["tab:twoway"] = ("unified", sel)

    # ---- Table: unified ------------------------------------------------------
    sel = order["unified"][:N_TOP_UNI] + sorted(UNI_ILLUS, key=lambda p: runi[0.2][p])
    rows = []
    for p in sel:
        rec("unified", p)
        is_p = tw[p] > pw[p]
        j = jaws.get(p, {})
        lab = POSLAB.get(p) or j.get("pos", "")
        if p in rrp[0.2]:
            crk = f"\\#{rpit[0.2][p]} Pitch / \\#{rrp[0.2][p]} RP"
        elif p == "ohtansh01":
            crk = "Active"
        elif p == "roganbu99":
            crk = "NgL"
        elif is_p:
            crk = f"\\#{rpit[0.2][p]} Pitch"
        else:
            crk = f"\\#{rpos[0.2][p]} Pos" + (", NgL" if p in NGL else "")
        zp, zt = zpos[A].get(p, 0.0), zpit[A].get(p, 0.0)
        name = bold(nm(p)) if (is_p or p in two_pool) else nm(p)
        if p == "ruthba01":
            name = bold(nm(p))
        rows.append([bold(runi[0.2][p]), name, f"{lab} ({crk})", f"{f1(pw[p])} / {f1(tw[p])} ({f1(pw[p] + tw[p])})",
                     f"{thou(pn[p])} / {thou(tn[p])}", bold(f2(zp)) if zp >= zt else f2(zp),
                     bold(f2(zt)) if zt > zp else f2(zt), str(runi[0.0][p]), str(runi[0.5][p]),
                     bold(f2(zuni[A][p]))])
    cap = ("Unified all-time leaderboard at $\\alpha = \\tfrac15$ \\cite{bbref2026}, sorted by the $\\ell_\\gamma$ "
           "two-\\hspace{0pt}coordinate score $Z_{1/5} \\equiv Z_{1/5,\\mathrm{2D}} = \\sgn(\\Ical_{1/5})|\\Ical_{1/5}|^{1/\\gamma}$ with "
           "$\\gamma = 1/(1-\\alpha) = \\tfrac54$, $\\Ical_{1/5} = \\sgn(\\WAR_{\\mathrm{pos}})"
           "|\\WAR_{\\mathrm{pos}}|^{\\gamma}/\\allowbreak\\max(\\PA, 1)^{\\gamma-1} + \\sgn(\\WAR_{\\mathrm{pitch}})"
           "|\\WAR_{\\mathrm{pitch}}|^{\\gamma}/\\allowbreak\\max(\\BF, 1)^{\\gamma-1} "
           "= \\sum_k \\sgn(Z_{1/5,k})|Z_{1/5,k}|^{\\gamma}$, and $1\\,\\PA \\equiv 1\\,\\BF$. "
           "$Z_{1/5,\\mathrm{pos}}$, $Z_{1/5,\\mathrm{pitch}}$ and the "
           "coordinate ranks in column 3 are single-coordinate $Z_{1/5}$ values and ranks. The same rule gives "
           "total career $\\WAR$ at $\\alpha = 0$ ($\\WAR$ \\textbf{Rk}; tied totals share the better rank) and "
           "Equation~\\eqref{eq:universal_zwar} at $\\alpha = \\tfrac12$ ($Z_{1/2}$ \\textbf{Rk}). Totals are sums "
           "of the rounded components shown and can differ by $0.1$ from Baseball-Reference's published career "
           "totals (e.g., Ruth, Young, Randy Johnson). Pitchers and featured two-way players are shown in bold.")
    hdr = ["\\textbf{All-Time Rk} & \\textbf{Player} & \\textbf{Positions (Coord.\\ Rk)} & "
           "\\textbf{Pos / Pitch $\\WAR$ (Tot)} & \\textbf{Exposure ($\\PA$ / $\\BF$)} & "
           "$Z_{1/5,\\mathrm{pos}}$ & $Z_{1/5,\\mathrm{pitch}}$ & "
           "$\\WAR$ \\textbf{Rk} & $Z_{1/2}$ \\textbf{Rk} & \\textbf{Unified $Z_{1/5}$}"]
    tex = table("tab:unified", cap, "@{}cllccccccc@{}", hdr, rows, "4.8pt", [N_TOP_UNI])
    open(os.path.join(TAB, "tab_unified.tex"), "w").write(tex)
    tie_sets["tab:unified"] = ("unified", sel)

    # ---- values for 07, near-ties ------------------------------------------
    with open(os.path.join(TAB, "table_values.py"), "w") as fh:
        fh.write('"""Values shown in outputs/tables/*.tex (written by 17_leaderboards.py).\n\n'
                 "pos/pitch/unified: {pid: (name, Z_0.2 shown, WAR rank, Z_0.2 rank, Z_0.5 rank)}\n"
                 "sp/rp: {pid: (name, Z_0.2 sub-pool rank, Z_0.5 sub-pool rank)}\n"
                 "twoway: {pid: (name, Zpos_0.2, Zpitch_0.2, Zpool_0.2, Z2D_0.2, rank18_0.2, rank18_0.5)}\n"
                 '"""\n')
        for k, v in shown.items():
            fh.write(f"{k.upper()} = {pprint.pformat(v, width=110, sort_dicts=False)}\n\n")

    # Near-ties: for every table row, the adjacent gaps in the full ranking and
    # the rank band of players within the rounding bound / within TIE.
    tie_rows = []
    for lab, (coord, sel) in tie_sets.items():
        sc = {"pos": zpos[A], "pitch": zpit[A], "unified": zuni[A]}[coord]
        full = order[coord]
        vals = [sc[q] for q in full]
        idx = {q: i for i, q in enumerate(full)}
        for p in sel:
            i, v, rb = idx[p], sc[p], rbound(p, coord)
            lo_t = sum(1 for x in vals if x > v + TIE) + 1
            hi_t = sum(1 for x in vals if x >= v - TIE)
            lo_r = sum(1 for x in vals if x > v + 2 * rb) + 1
            hi_r = sum(1 for x in vals if x >= v - 2 * rb)
            gap_up = vals[i - 1] - v if i else ""
            gap_dn = v - vals[i + 1] if i + 1 < len(vals) else ""
            nxt = full[i + 1] if i + 1 < len(full) else None
            tie_rows.append([lab, coord, i + 1, nm(p), round(v, 4), round(rb, 4),
                             round(gap_up, 4) if gap_up != "" else "", round(gap_dn, 4) if gap_dn != "" else "",
                             nm(nxt) if nxt else "", int(nxt in sel), f"{lo_r}-{hi_r}", f"{lo_t}-{hi_t}"])
    write_csv(os.path.join("tables", "ties.csv"),
              ["table", "coordinate", "rank_Z0.2", "player", "Z0.2", "rounding_bound", "gap_to_prev",
               "gap_to_next", "next_player", "next_in_table", "rank_band_2x_rounding", "rank_band_tie0.10"],
              tie_rows)
    n_tab_ties = sum(1 for r in tie_rows if r[9] and r[7] != "" and r[7] < TIE)

    # ---- summary -------------------------------------------------------------
    bounds = [rbound(p, "pos") for p in order["pos"][:100]] + [rbound(p, "pitch") for p in order["pitch"][:100]]
    print(f"+-0.05 WAR moves Z_0.2 by {min(bounds):.4f}-{max(bounds):.4f} (top-100 hitters and pitchers); "
          f"proposed tie threshold {TIE}")
    for k in (25, 50, 100):
        n_p = sum(1 for p in order["unified"][:k] if tw[p] > pw[p])
        print(f"unified alpha = 0.2: pitchers in top {k}: {n_p}")
    for lab, (coord, sel) in tie_sets.items():
        print(f"{lab}: {len(sel)} rows written")
    print(f"{n_tab_ties} adjacent pairs of table rows closer than {TIE} -> outputs/tables/ties.csv")


if __name__ == "__main__":
    main()
