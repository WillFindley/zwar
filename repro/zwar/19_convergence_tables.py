#!/usr/bin/env python3
"""LaTeX tables for the convergence analysis (paper Section 5 and Appendix A).

Reads the outputs of 11, 15, 16 and 18 and writes
  outputs/tables/tab_convergence.tex   summary by benchmark group (Table "convergence")
  outputs/tables/tab_forecast.tex      forecasts: argmax alpha by design and outcome,
                                       with exposure / rate persistence (Table "forecast")
  outputs/tables/tab_expert.tex        expert top-100 lists (Table "expert")
  outputs/tables/app_benchmarks.tex    every benchmark (Appendix "benchmarks")
Run after 16_alpha_convergence.py and 18_implied_alpha.py.
"""
import csv
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import OUT  # noqa: E402

TAB = os.path.join(OUT, "tables")
os.makedirs(TAB, exist_ok=True)


def read(name):
    with open(os.path.join(OUT, name), newline="") as fh:
        return list(csv.DictReader(fh))


def f3(x):
    return f"{float(x):.3f}"


def fa(x):
    x = float(x)
    return f"{x:.2f}"


def interval(lo, hi):
    return f"[{float(lo):.2f}, {float(hi):.2f}]"


def ireg(r):
    v = r.get("implied_alpha_star", "")
    if v in ("", "nan"):
        return "---"
    v, lo, hi = float(v), r.get("implied_alpha_star_lo", ""), r.get("implied_alpha_star_hi", "")
    if v < -2:
        return "$<-2$"
    s = f"${v:.2f}$"
    try:
        lo, hi = float(lo), float(hi)
        if hi - lo < 4:
            s = f"${v:.2f}$ $[{lo:.2f}, {hi:.2f}]$"
    except ValueError:
        pass
    return s


conv = read("alpha_convergence.csv")
head = [r for r in conv if r["in_headline"] == "1"]

# ---------------------------------------------------------------- summary text
summ = open(os.path.join(OUT, "alpha_convergence_summary.txt")).read()


def grp(label):
    m = re.search(r"^\s*%s\s+n=\s*(\d+)\s+median argmax ([\d.]+) \(IQR ([\d.]+)-([\d.]+)\); intervals containing "
                  r"0\.2: (\d+)/\d+, containing 0\.5: (\d+)/\d+; m\(0\.2\) > m\(0\.5\) in (\d+)/\d+ \(CI excludes 0 "
                  r"in favour of 0\.2: (\d+), of 0\.5: (\d+)\); m\(0\.2\) > m\(0\) in (\d+)/\d+ \(CI > 0: (\d+), < 0: (\d+)\)"
                  % re.escape(label), summ, re.M)
    return m.groups()


def regret(label):
    i = summ.index("Regret of a fixed alpha")
    block = summ[i:]
    m = re.search(r"^\s*%s\s+n=\s*\d+\s+minimax-regret alpha ([\d.]+) \(max regret ([\d.]+)\); min-mean-regret alpha "
                  r"([\d.]+) \(mean regret ([\d.]+)\).*?\n\s+(.*?)\(mean/max regret\)" % re.escape(label), block, re.M | re.S)
    mm, mx, mn, mean, vals = m.groups()
    d = dict(re.findall(r"a=([\d.]+)\s+([\d.]+/[\d.]+)", vals))
    return mm, mn, d


groups = [("Judgments of finished careers", "judgment"), ("Concurrent season honors", "concurrent"),
          ("Forecasts, hitters", "forecast-hitters"), ("Forecasts, pitchers", "forecast-pitchers"),
          ("All benchmarks", "all career-value")]
lines = [r"\begin{table}[htbp]", r"\centering",
         r"\caption{Summary of the $42$ benchmarks by group. $\hat\alpha$: exponent maximizing each benchmark's metric "
         r"on a $0.05$ grid (median and interquartile range across benchmarks). ``Interval contains'': number of "
         r"benchmarks whose 95\% bootstrap interval for $\hat\alpha$ contains $\tfrac15$ / $\tfrac12$. "
         r"``$\tfrac15$ vs.\ $\tfrac12$'' and ``$\tfrac15$ vs.\ $0$'': number of benchmarks on which $\alpha = \tfrac15$ "
         r"scores higher, with the number of 95\% bootstrap intervals for the difference that exclude zero in favor of "
         r"$\tfrac15$ / against it in parentheses. Regret is the shortfall of a fixed exponent from each benchmark's best "
         r"exponent, in AUC or Spearman units (mean / maximum over the group). The pennant-race estimates (Table~\ref{tab:gamma}) give $\alpha = 0.14$--$0.23$.}",
         r"\label{tab:convergence}", r"\footnotesize", r"\resizebox{\textwidth}{!}{%",
         r"\begin{tabular}{@{}lrcccccccc@{}}", r"\toprule",
         r" & & & \multicolumn{2}{c}{\textbf{Interval contains}} & & & \multicolumn{3}{c}{\textbf{Regret (mean / max)}} \\",
         r"\cmidrule(lr){4-5} \cmidrule(lr){8-10}",
         r"\textbf{Group} & $n$ & $\hat\alpha$ median (IQR) & $\tfrac15$ & $\tfrac12$ & $\tfrac15$ vs.\ $\tfrac12$ & "
         r"$\tfrac15$ vs.\ $0$ & $\alpha = 0$ & $\alpha = \tfrac15$ & $\alpha = \tfrac12$ \\", r"\midrule"]
for label, key in groups:
    n, med, q1, q3, in2, in5, g25, s25, s52, g20, s20, s02 = grp(key)
    mm, mn, d = regret(key)

    def rg(a):
        mean, mx = d[a].split("/")
        return f"{float(mean):.4f} / {float(mx):.4f}"
    if key == "all career-value":
        lines.append(r"\midrule")
    lines.append(f"{label} & {n} & {float(med):.2f} ({float(q1):.2f}--{float(q3):.2f}) & {in2} & {in5} & "
                 f"{g25} ({s25} / {s52}) & {g20} ({s20} / {s02}) & {rg('0')} & {rg('0.2')} & {rg('0.5')} \\\\")
mmr = {k: regret(k)[:2] for _, k in groups}
mmtxt = (r" Regret-minimizing exponents (minimax / min-mean): judgments " + " / ".join(mmr["judgment"])
         + "; concurrent honors " + " / ".join(mmr["concurrent"]) + "; forecasts, hitters "
         + " / ".join(mmr["forecast-hitters"]) + "; forecasts, pitchers " + " / ".join(mmr["forecast-pitchers"])
         + "; all benchmarks " + " / ".join(mmr["all career-value"]) + ".")
lines[2] = lines[2][:-1] + mmtxt + "}"
lines += [r"\bottomrule", r"\end{tabular}%", "}", r"\end{table}", ""]
open(os.path.join(TAB, "tab_convergence.tex"), "w").write("\n".join(lines))

# ---------------------------------------------------------------- forecast table
by = {r["benchmark"]: r for r in conv}
des = {(r["role"], r["design"], r["careers_to"]): r for r in read("implied_alpha_designs.csv")}


def cell(name):
    r = by.get(name)
    if r is None:
        return "---"
    star = "" if r["alpha0.2_in_interval"] == "1" else "$^{\\dagger}$"
    return f"{fa(r['argmax_alpha'])} {interval(r['boot_lo'], r['boot_hi'])}{star}"


rows = []
for role, rl in (("Hitters", "H"), ("Pitchers", "P")):
    aw = "MVP" if rl == "H" else "MVP+CY"
    for design, lab, cut in (("checkpoint k=3", "3 seasons", "2023"), ("checkpoint k=5", "5 seasons", "2023"),
                             ("midpoint", "Midpoint", "2016")):
        if design.startswith("checkpoint"):
            war = f"{role}, {design} (careers to 2023): future WAR"
            hof = f"{role}, {design} (careers to 2023): Hall of Fame"
        else:
            war = f"{role}, {design} (careers to 2016): future WAR"
            hof = f"{role}, {design} (careers to 2016): Hall of Fame"
        ast = f"{role}, {design} (careers to 2016): future All-Star selections"
        awd = f"{role}, {design} (careers to 2016): future award shares ({aw})"
        dd = des[(role, design, cut)]
        rows.append(f"{role}, {lab} & {cell(war)} & {cell(ast)} & {cell(awd)} & {cell(hof)} & "
                    f"{float(dd['beta']):.2f} & {float(dd['kappa']):.2f} & {float(dd['rate_spearman']):.2f} \\\\")
    if rl == "H":
        rows.append(r"\midrule")
lines = [r"\begin{table}[htbp]", r"\centering",
         r"\caption{Forecasts from early-career checkpoints (after three or five seasons in the role) and from the first "
         r"half of a career (midpoint split). Entries are the exponent $\hat\alpha$ that maximizes the Spearman "
         r"correlation with the future outcome (AUC for Hall of Fame election), with its 95\% bootstrap interval; "
         r"$^{\dagger}$ marks intervals that exclude $\tfrac15$. Last three columns: exposure persistence $\beta$ "
         r"(slope of $\log N_{\mathrm{future}}$ on $\log N$), rate persistence $\kappa$ (slope of $\log r_{\mathrm{future}}$ "
         r"on $\log r$, players with positive $\WAR$ in both periods) and the Spearman correlation $\rho_r$ between early "
         r"and future rates. If future rate and exposure were independent, Proposition~\ref{prop:target} would put the "
         r"optimum for a cumulative target at $\alpha = 0$ whenever $\beta \ge \kappa$; this matches the pitcher and "
         r"midpoint designs but not the hitter checkpoints (Section~\ref{sec:forecast}). Future $\WAR$ at checkpoints uses careers ending by 2023; all other outcomes careers ending by 2016 "
         r"(Hall of Fame: by 2010).}",
         r"\label{tab:forecast}", r"\footnotesize", r"\resizebox{\textwidth}{!}{%",
         r"\begin{tabular}{@{}lccccccc@{}}", r"\toprule",
         r" & \multicolumn{4}{c}{\textbf{$\hat\alpha$ [95\% interval] for the future outcome}} & \multicolumn{3}{c}{\textbf{Persistence}} \\",
         r"\cmidrule(lr){2-5} \cmidrule(l){6-8}",
         r"\textbf{Design} & $\WAR$ & All-Star selections & Award shares & Hall of Fame & $\beta$ & $\kappa$ & $\rho_r$ \\",
         r"\midrule"] + rows + [r"\bottomrule", r"\end{tabular}%", "}", r"\end{table}", ""]
open(os.path.join(TAB, "tab_forecast.tex"), "w").write("\n".join(lines))

# ---------------------------------------------------------------- expert table
ex = {(r["list"], r["metric"]): r for r in read("expert_rankings.csv")}
summ11 = open(os.path.join(OUT, "expert_summary.txt")).read()
best = re.findall(r"best alpha: Spearman ([\d.]+) \(([\d.]+)\); AUC ([\d.]+) \(([\d.]+)\)", summ11)
cols = ["WAR", "JAWS", "Z0.20", "Z0.25", "Z0.50", "Z1.00", "Z0.50_c1.2", "Z0.50_c59/41"]
body = []
for (lst, lab, n), b in zip((("tsn1998", "Sporting News 1998", "1{,}592"), ("espn2022", "ESPN 2022", "2{,}082")), best):
    r1 = " & ".join(f"{float(ex[(lst, c)]['spearman_list_order']):.3f} / {float(ex[(lst, c)]['membership_auc']):.3f}"
                    for c in cols)
    r2 = " & ".join(ex[(lst, c)]["pitchers_in_top100"] for c in cols)
    body.append(f"{lab} & $\\rho$ / AUC & {r1} & {float(b[0]):.2f} / {float(b[2]):.2f} \\\\")
    body.append(f"($n = {n}$) & pitchers & {r2} & \\\\")
    body.append(r"\midrule")
body = body[:-1]
lines = [r"\begin{table}[htbp]", r"\centering",
         r"\caption{Agreement with expert top-100 lists, careers through the season before publication. Entries are the "
         r"Spearman correlation with list order among the $100$ listed players / the AUC for list membership in the "
         r"universe; the second row of each list gives the number of pitchers in the metric's top $100$ (lists: $28$ and "
         r"$27$). Two-way records are combined by Definition~\ref{def:twoway}; $c$ multiplies pitcher scores. The final "
         r"column gives the in-sample optimal exponents $\hat\alpha_\rho$ / $\hat\alpha_{\mathrm{AUC}}$ on a $0.05$ grid "
         r"(achieving $\rho = %s$, $\mathrm{AUC} = %s$ on Sporting News 1998 and $\rho = %s$, $\mathrm{AUC} = %s$ on "
         r"ESPN 2022).}" % (best[0][1], best[0][3], best[1][1], best[1][3]),
         r"\label{tab:expert}", r"\footnotesize", r"\setlength{\tabcolsep}{4pt}", r"\resizebox{\textwidth}{!}{%",
         r"\begin{tabular}{@{}llccccccccc@{}}", r"\toprule",
         r" & & & & & & & & $Z_{1/2}$ & $Z_{1/2}$ & $\hat\alpha$ \\",
         r"\textbf{List} & & $\WAR$ & $\JAWS$ & $Z_{1/5}$ & $Z_{1/4}$ & $Z_{1/2}$ & $Z_1$ & ($c = 1.2$) & "
         r"($c = 59/41$) & ($\rho$ / AUC) \\", r"\midrule"] + body + [r"\bottomrule", r"\end{tabular}%", "}",
                                                                      r"\end{table}", ""]
open(os.path.join(TAB, "tab_expert.tex"), "w").write("\n".join(lines))

# ---------------------------------------------------------------- appendix: all benchmarks
def short(name):
    s = name
    s = s.replace("Hall of Fame AUC: ", "HOF: ").replace("Expert list ", "")
    s = s.replace(" (careers to 2023)", "").replace(" (careers to 2016)", "")
    s = s.replace("checkpoint k=", "checkpoint ").replace("Hitters (8 positions pooled)", "Hitters")
    s = s.replace(": Spearman with list order", ", list order").replace(": membership AUC (universe 1592)", ", membership")
    s = s.replace(": membership AUC (universe 2082)", ", membership")
    s = s.replace("future award shares (MVP+CY)", "future MVP+CY shares").replace("future award shares (MVP)",
                                                                                 "future MVP shares")
    s = s.replace("career award shares (MVP+CY)", "MVP+CY shares").replace("career award shares (MVP)", "MVP shares")
    s = s.replace("career All-Star selections", "All-Star selections").replace(", concurrent", "")
    s = s.replace("future All-Star selections", "future All-Star")
    return s.replace("+", "\\,+\\,") if "HOF:" in s else s


sections = [("judgment", "Judgments of finished careers"), ("concurrent", "Concurrent season honors"),
            ("forecast", "Forecasts"), ("talent-contrast", "Contrast: future per-event rate (not a career-value target)")]
body = []
for cat, title in sections:
    rs = [r for r in conv if r["category"] == cat and (r["in_headline"] == "1" or cat == "talent-contrast")]
    if cat == "talent-contrast":
        rs = [r for r in rs if "2023" in r["benchmark"] or "midpoint" in r["benchmark"]]
    body.append(r"\multicolumn{8}{@{}l}{\emph{%s}} \\" % title)
    for r in rs:
        body.append(f"{short(r['benchmark'])} & {int(float(r['n'])):,} & {f3(r['m(0)'])} & {f3(r['m(0.2)'])} & "
                    f"{f3(r['m(0.5)'])} & {f3(r['m(1)'])} & {fa(r['argmax_alpha'])} "
                    f"{interval(r['boot_lo'], r['boot_hi'])} & {ireg(r)} \\\\".replace(",", "{,}", 1)
                    if False else
                    f"{short(r['benchmark'])} & {int(float(r['n']))} & {f3(r['m(0)'])} & {f3(r['m(0.2)'])} & "
                    f"{f3(r['m(0.5)'])} & {f3(r['m(1)'])} & {fa(r['argmax_alpha'])} "
                    f"{interval(r['boot_lo'], r['boot_hi'])} & {ireg(r)} \\\\")
    body.append(r"\midrule")
body = body[:-1]
lines = [r"\section{Every benchmark}", r"\label{app:benchmarks}", "",
         r"Table~\ref{tab:benchmarks} lists every benchmark of Section~\ref{sec:convergence}: its metric (AUC for "
         r"Hall of Fame election and list membership, Spearman correlation otherwise) at $\alpha = 0$, $\tfrac15$, "
         r"$\tfrac12$ and $1$, the maximizing exponent $\hat\alpha$ with its 95\% bootstrap interval, and the "
         r"regression-implied exponent $\alpha_{\mathrm{reg}} = -c_N/c_W$ from a regression of the target on $\log W$ and "
         r"$\log N$ (players with $W > 0$; 95\% bootstrap interval shown unless it is wider than $4$; values below $-2$ "
         r"are shown as $<-2$). A negative $\alpha_{\mathrm{reg}}$ means that, in the log-linear fit, the target rewards "
         r"exposure even more than career $\WAR$ does; for most such benchmarks the best member of the family is "
         r"$\alpha = 0$, but not for hitters' checkpoint forecasts of future $\WAR$ and MVP shares, where the rank-based "
         r"optimum is interior (the fit excludes players with $W \le 0$, who matter for the Spearman criterion). "
         r"Pitcher forecasts have very negative values because, once $\log N$ is known, early $\WAR$ adds little. "
         r"Across the $42$ benchmarks the Spearman correlation between $\hat\alpha$ and $\alpha_{\mathrm{reg}}$ is "
         r"$0.79$. The last block shows that future per-event rates, a talent target, call for large exponents at "
         r"checkpoints ($0.95$--$1$) but not in the pitcher midpoint design ($0.20$).",
         "", r"\begin{table}[htbp]", r"\centering",
         r"\caption{Every benchmark. $m(\alpha)$ is the benchmark's metric at exponent $\alpha$.}",
         r"\label{tab:benchmarks}", r"\scriptsize", r"\setlength{\tabcolsep}{3.5pt}",
         r"\begin{tabular}{@{}lrcccccc@{}}", r"\toprule",
         r"\textbf{Benchmark} & $n$ & $m(0)$ & $m(\tfrac15)$ & $m(\tfrac12)$ & $m(1)$ & $\hat\alpha$ [95\%] & "
         r"$\alpha_{\mathrm{reg}}$ [95\%] \\", r"\midrule"] + body + [r"\bottomrule", r"\end{tabular}", r"\end{table}", ""]
open(os.path.join(TAB, "app_benchmarks.tex"), "w").write("\n".join(lines))
print("wrote tab_convergence.tex, tab_forecast.tex, tab_expert.tex, app_benchmarks.tex to", TAB)

# Figure 1 is drawn by 16_alpha_convergence.py; copy it next to the paper.
import shutil  # noqa: E402
FIG_SRC = os.path.join(OUT, "figures", "fig_alpha_curves.pdf")
FIG_DST = os.path.join(os.path.dirname(os.path.dirname(OUT)), "figures")
if os.path.exists(FIG_SRC):
    os.makedirs(FIG_DST, exist_ok=True)
    shutil.copy2(FIG_SRC, FIG_DST)
    print("copied Figure 1 to", FIG_DST)
