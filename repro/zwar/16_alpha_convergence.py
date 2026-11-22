#!/usr/bin/env python3
"""Where do the benchmarks put alpha? One table and one headline figure across
every benchmark of the exponent in Z_alpha = W / N^alpha.

Benchmarks assembled (alpha grid 0..1 step 0.05 throughout):
  judgment (career-level, existing):
    * Hall of Fame AUC for the eight pools of 04_hof_validation.py (pools
      rebuilt with the same code; checked against outputs/hof_auc.csv)
    * expert top-100 lists, TSN 1998 and ESPN 2022, as in 11_expert_rankings.py
      with c = 1: Spearman with list order (the 100 listed players) and list
      membership AUC (checked against outputs/expert_rankings.csv). Two-way
      careers are combined with the l_gamma rule (11.z_two_way, the default);
      the previous signed-quadrature combination is listed as reference rows
      (checked against outputs/expert_rankings_quadrature.csv) and is not used
      in the headline summary or figure.
  forecast (existing, 10_checkpoint_prediction.py, careers ending by 2023):
    * checkpoint k = 3, 5 future WAR (Spearman) and Hall of Fame (AUC)
      (checked against outputs/checkpoint_prediction.csv)
  forecast / concurrent (new, 15_forecast_benchmarks.py, careers ending by 2016;
    read from outputs/forecast_benchmarks*.csv):
    * checkpoint and career-midpoint forecasts of future All-Star selections,
      award shares, WAR and Hall of Fame; concurrent career All-Star / award
      benchmarks in the Hall-of-Fame-style pools.
    * Script 15's checkpoint Hall of Fame benchmarks use exactly the same
      players and labels as script 10's (both restrict to careers ending by
      2010), and its checkpoint future-WAR benchmarks are the 2016-cutoff
      variant of script 10's; both are listed but flagged as duplicates and
      left out of the headline summary and the figure.
  talent-contrast: future rate W / N (scripts 10 and 15), listed, never pooled
    with the career-value benchmarks.
  pennant: implied alpha = 1 - 1/gamma from 12_season_value.py (log-log
    slope estimator, linear logit; World Series and pennant; context-neutral
    and actual-context) with its bootstrap 95% interval (outputs/season_value.csv).
    A point / band, not a curve.

For every curve benchmark: metric at alpha = 0, 0.2, 0.5, 1; argmax alpha; a
1,000-resample player bootstrap (stratified by outcome for AUCs; for the
expert Spearman the 100 listed players are resampled) of the argmax (median,
95% interval) and of m(0.2) - m(0.5), m(0.2) - m(0) (alpha_bench.py). The
script-15 statistics are read from its summary file (same machinery).
Regret of a fixed alpha in a benchmark = max_alpha m - m(alpha) (metric units);
the summary reports mean / max regret by category and the minimax-regret and
min-mean-regret alpha. If outputs/implied_alpha.csv (18_implied_alpha.py)
exists, its regression-implied alpha* is added as a column.

Caveat: the benchmarks are not independent (overlapping pools, the same
players and the same WAR data recur), so counts across benchmarks are
descriptive, not a meta-analytic test.

Outputs: outputs/alpha_convergence.csv, outputs/alpha_curves.csv (long:
         benchmark, category, alpha, metric), outputs/alpha_convergence_summary.txt,
         outputs/figures/fig_alpha_curves.pdf and .png (matplotlib, optional)
"""
import csv
from decimal import Decimal, ROUND_HALF_UP
import importlib.util
import os
import sys
import tempfile

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import OUT, write_csv  # noqa: E402
import alpha_bench as ab  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
FIG = os.path.join(OUT, "figures")
LOG = []
CAREER = ("judgment", "forecast", "concurrent")
REGRET_ALPHAS = (0.0, 0.1, 0.15, 0.2, 0.25, 0.3, 0.5, 1.0)


def log(msg=""):
    print(msg)
    LOG.append(msg)


def load_script(fname, modname):
    spec = importlib.util.spec_from_file_location(modname, os.path.join(HERE, fname))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def read_csv(name):
    with open(os.path.join(OUT, name), newline="", encoding="utf-8") as fh:
        return list(csv.DictReader(fh))


class Checker:
    """Compare reproduced numbers with an existing output file (4-dp rounding)."""

    def __init__(self, label):
        self.label, self.n, self.bad = label, 0, []

    def check(self, what, got, want, tol=6e-5):
        self.n += 1
        if want is None or abs(float(got) - float(want)) > tol:
            self.bad.append(f"{what}: reproduced {got:.4f} vs file {want}")

    def report(self):
        log(f"  check vs {self.label}: {self.n - len(self.bad)}/{self.n} values match"
            + ("" if not self.bad else "; MISMATCHES: " + "; ".join(self.bad[:10])))


# ---------------------------------------------------------------------------
# Benchmark data sets (also imported by 18_implied_alpha.py). Each is a dict:
#   benchmark, category, source, metric, kind ("auc" / "spearman"), short,
#   key (bootstrap seed name), W, N (arrays for the W / N^alpha family;
#   for two-way expert careers W = total WAR, N = PA + BF), y, optional S
#   (score matrix when it is not W / N^alpha), role_group, design_group.
# ---------------------------------------------------------------------------
HOF_POOLS = ["Hitters (8 positions pooled)", "Starting pitchers", "Relief pitchers", "Hitters + SP pooled",
             "SP + RP pooled", "Contested hitters", "Contested SP", "Contested hitters + SP"]


def hof_sets():
    m04 = load_script("04_hof_validation.py", "hof04")
    from pools import hitters, pitchers, hof_eligible
    H = hof_eligible(hitters())
    SP = hof_eligible(pitchers("SP"))
    RP = hof_eligible(pitchers("RP"))

    def contested(ps):
        return [p for p in ps if p["W"] >= 40]
    pools = dict(zip(HOF_POOLS, [H, SP, RP, H + SP, SP + RP, contested(H), contested(SP),
                                 contested(H) + contested(SP)]))
    out = []
    for name in HOF_POOLS:
        ps = pools[name]
        out.append(dict(benchmark=f"Hall of Fame AUC: {name}", category="judgment", source="04",
                        metric="AUC", kind="auc", short=f"HOF {name}", key=f"HOF | {name}", pool=name,
                        W=np.array([p["W"] for p in ps], float), N=np.array([p["N"] for p in ps], float),
                        y=m04.labels(ps), role_group="", design_group=""))
    return out


def expert_sets(quadrature=False):
    m11 = load_script("11_expert_rankings.py", "expert11")
    comb = m11.z_unified if quadrature else m11.z_two_way
    tag = " [quadrature, reference]" if quadrature else ""
    ktag = " | quadrature" if quadrature else ""
    lists = m11.load_lists()
    out = []
    for lst, cutoff in m11.LISTS.items():
        entries = lists[lst]
        listed = {pid for _, pid, _ in entries}
        car = m11.careers_through(cutoff)
        uni = [pid for pid, p in car.items() if p["war"] >= m11.MIN_WAR or pid in listed]
        y = np.array([pid in listed for pid in uni])
        ranks = np.array([r for r, _, _ in entries], float)
        lp = [pid for _, pid, _ in entries]
        label = {"tsn1998": "TSN 1998", "espn2022": "ESPN 2022"}[lst]

        def arrays(ids):
            S = np.array([[comb(car[pid], a) for a in ab.ALPHAS] for pid in ids])
            W = np.array([car[pid]["war"] for pid in ids], float)
            N = np.array([car[pid]["pa"] + car[pid]["bf"] for pid in ids], float)
            return S, W, N
        S, W, N = arrays(lp)
        out.append(dict(benchmark=f"Expert list {label}: Spearman with list order{tag}", category="judgment",
                        source="11", metric="Spearman", kind="spearman", short=f"{label} order",
                        key=f"expert | {lst} | spearman{ktag}", S=S, W=W, N=N, y=-ranks, lst=lst,
                        which="spearman", quadrature=quadrature, role_group="", design_group=""))
        S, W, N = arrays(uni)
        out.append(dict(benchmark=f"Expert list {label}: membership AUC (universe {len(uni)}){tag}",
                        category="judgment", source="11", metric="AUC", kind="auc", short=f"{label} membership",
                        key=f"expert | {lst} | auc{ktag}", S=S, W=W, N=N, y=y, lst=lst, which="auc",
                        quadrature=quadrature, role_group="", design_group=""))
    return out


def checkpoint_sets():
    m10 = load_script("10_checkpoint_prediction.py", "ckpt10")
    out = []
    for role, label in (("H", "Hitters"), ("P", "Pitchers")):
        for k in (3, 5):
            P = m10.build(role, k)
            W = np.array([p["W"] for p in P], float)
            N = np.array([p["N"] for p in P], float)
            ir = np.array([i for i, p in enumerate(P) if p["fN"] >= m10.MIN_N[role]])
            ih = np.array([i for i, p in enumerate(P) if p["last"] <= m10.LAST_HOF and not p["excl"]])
            base = f"{label}, checkpoint k={k} (careers to 2023)"
            common = dict(source="10", role=label, k=k, role_group=label, design_group="checkpoint")
            out.append(dict(benchmark=f"{base}: future WAR", category="forecast", metric="Spearman",
                            kind="spearman", short=f"{label[0]} k={k} fut WAR",
                            key=f"ckpt10 | {role} | {k} | futWAR", W=W, N=N,
                            y=np.array([p["fW"] for p in P], float), col="rho_future_WAR", **common))
            out.append(dict(benchmark=f"{base}: Hall of Fame", category="forecast", metric="AUC", kind="auc",
                            short=f"{label[0]} k={k} HOF", key=f"ckpt10 | {role} | {k} | HOF", W=W[ih], N=N[ih],
                            y=np.array([P[i]["hof"] for i in ih]), col="auc_hof", **common))
            out.append(dict(benchmark=f"{base}: future rate", category="talent-contrast", metric="Spearman",
                            kind="spearman", short=f"{label[0]} k={k} fut rate",
                            key=f"ckpt10 | {role} | {k} | futrate", W=W[ir], N=N[ir],
                            y=np.array([P[i]["fW"] / P[i]["fN"] for i in ir]), col="rho_future_rate", **common))
    return out


def benchmark_name_15(role, design, outcome):
    """Name used in alpha_convergence.csv for a script-15 benchmark."""
    return f"{role}, {design} (careers to 2016): {outcome}"


def duplicate_note_15(design, outcome):
    if design.startswith("checkpoint") and outcome == "Hall of Fame":
        return "same sample as script 10 checkpoint HOF"
    if design.startswith("checkpoint") and outcome == "future WAR":
        return "2016-cutoff variant of script 10 checkpoint future WAR"
    return ""


def script15_benchmarks():
    try:
        summ = read_csv("forecast_benchmarks_summary.csv")
        long_ = read_csv("forecast_benchmarks.csv")
    except FileNotFoundError:
        log("  outputs/forecast_benchmarks*.csv missing: run 15_forecast_benchmarks.py first")
        return []
    curves = {}
    for r in long_:
        curves.setdefault(r["benchmark"], {})[float(r["alpha"])] = float(r["metric"])
    out = []
    for r in summ:
        d = {k: (float(r[k]) if r[k] not in ("",) else "") for k in ab.SUMMARY_FIELDS}
        d["n"] = int(float(r["n"]))
        d["has02"], d["has05"] = bool(int(float(r["has02"]))), bool(int(float(r["has05"])))
        d["curve"] = np.array([curves[r["benchmark"]][float(a)] for a in ab.ALPHAS])
        d["kind"] = "auc" if r["metric_name"] == "AUC" else "spearman"
        role_s = {"Hitters": "H", "Pitchers": "P"}.get(r["role"], r["role"].split(" ")[0])
        des_s = r["design"].replace("checkpoint ", "").replace("midpoint", "mid")
        out_s = (r["outcome"].replace("future ", "fut ").replace("career ", "").replace("selections", "")
                 .replace("award shares", "awards").replace("Hall of Fame", "HOF").strip())
        d.update(benchmark=benchmark_name_15(r["role"], r["design"], r["outcome"]),
                 category=r["category"], source="15", metric=r["metric_name"],
                 duplicate=duplicate_note_15(r["design"], r["outcome"]),
                 short=f"{role_s} {des_s} {out_s}" if r["design"] != "concurrent" else f"{role_s} conc. {out_s}",
                 role_group=r["role"] if r["role"] in ("Hitters", "Pitchers") else "",
                 design_group=("checkpoint" if r["design"].startswith("checkpoint") else r["design"]))
        out.append(d)
    return out


def pennant_rows():
    rows = {(r["outcome"], r["logit"]): r for r in read_csv("season_value.csv")}
    out = []
    for oc, lab in (("ws", "World Series"), ("pennant", "pennant")):
        r = rows[(oc, "linear")]
        for ctx, g, lo, hi in (("context-neutral", "gamma_neutral_slope", "ns_lo", "ns_hi"),
                               ("actual-context", "gamma_actual_slope", "as_lo", "as_hi")):
            gm, gl, gh = float(r[g]), float(r[lo]), float(r[hi])
            a, al, ah = 1 - 1 / gm, 1 - 1 / gl, 1 - 1 / gh
            out.append(dict(benchmark=f"Pennant races, {lab}, {ctx}: implied alpha = 1 - 1/gamma",
                            category="pennant", source="12", metric="implied alpha (log-log slope)",
                            n="", argmax=a, boot_median="", boot_lo=al, boot_hi=ah,
                            has02=al <= 0.2 <= ah, has05=al <= 0.5 <= ah, gamma=gm))
    return out


# ---------------------------------------------------------------------------
# Analysis of the existing benchmarks, with reproduction checks
# ---------------------------------------------------------------------------
def run_sets(sets):
    out = []
    for s in sets:
        S = s["S"] if "S" in s else ab.z_matrix(s["W"], s["N"])
        r = ab.analyse(S, s["y"], s["kind"], s["key"])
        r.update({k: v for k, v in s.items() if k not in ("S", "W", "N", "y")})
        out.append(r)
    return out


def check_hof(res):
    ref = {r["pool"]: r for r in read_csv("hof_auc.csv")}
    chk = Checker("hof_auc.csv")
    for r in res:
        f = ref.get(r["pool"], {})
        chk.check(f"{r['pool']} n", r["n"], f.get("n"), 0)
        chk.check(f"{r['pool']} AUC(0.5)", r["m0.5"], f.get("ZWAR"))
        chk.check(f"{r['pool']} AUC(0.2)", r["m0.2"], f.get("Z_alpha0.2"))
        chk.check(f"{r['pool']} best alpha", r["argmax"], f.get("best_alpha"))
        chk.check(f"{r['pool']} best AUC", r["m_argmax"], f.get("best_alpha_auc"))
    chk.report()


def check_expert(res, fname):
    try:
        ref = {(r["list"], r["metric"]): r for r in read_csv(fname)}
    except FileNotFoundError:
        log(f"  {fname} missing: run 11_expert_rankings.py")
        return
    chk = Checker(fname)
    for r in res:
        col = "spearman_list_order" if r["which"] == "spearman" else "membership_auc"
        for j, a in enumerate(ab.ALPHAS):
            chk.check(f"{r['lst']} Z{a:.2f} {col}", r["curve"][j], ref.get((r["lst"], f"Z{a:.2f}"), {}).get(col))
    chk.report()


def check_checkpoint(res):
    ref = {(r["role"], r["k_seasons"], r["alpha"]): r for r in read_csv("checkpoint_prediction.csv")}
    chk = Checker("checkpoint_prediction.csv")
    for r in res:
        for j, a in enumerate(ab.ALPHAS):
            f = ref.get((r["role"], str(r["k"]), f"{a}"), {})
            chk.check(f"{r['short']} a={a}", r["curve"][j], f.get(r["col"]))
    chk.report()


# ---------------------------------------------------------------------------
# Figure
# ---------------------------------------------------------------------------
def figure(bench, band):
    os.environ.setdefault("MPLCONFIGDIR", os.path.join(tempfile.gettempdir(), "zwar_mplconfig"))
    os.makedirs(os.environ["MPLCONFIGDIR"], exist_ok=True)
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        from matplotlib.lines import Line2D
        from matplotlib.patches import Patch
    except ImportError:
        log("matplotlib not installed: figure skipped")
        return
    plt.rcParams.update({
        "font.family": "serif", "font.serif": ["STIXGeneral", "Times New Roman", "DejaVu Serif"],
        "mathtext.fontset": "stix", "font.size": 9, "axes.labelsize": 9, "axes.titlesize": 9,
        "xtick.labelsize": 8, "ytick.labelsize": 8, "legend.fontsize": 7.5,
        "axes.spines.top": False, "axes.spines.right": False, "pdf.fonttype": 42})
    col = {"judgment": "#0072B2", "concurrent": "#E69F00", "forecast": "#009E73"}
    names = {"judgment": "Hall of Fame / expert lists", "concurrent": "All-Star / awards (concurrent)",
             "forecast": "forecasts"}
    a = ab.ALPHAS
    fig, axes = plt.subplots(1, 2, figsize=(6.5, 3.6), sharey=True)
    panels = [(axes[0], ("judgment", "concurrent"), "(a) Career judgments"),
              (axes[1], ("forecast",), "(b) Forecasts")]
    for ax, cats, title in panels:
        B = [b for b in bench if b["category"] in cats]
        ax.axvspan(band[0], band[1], color="#BBBBBB", alpha=0.45, lw=0, zorder=0)
        ax.text((band[0] + 0.2) / 2, 0.30, "pennant races", ha="center", va="center", fontsize=7,
                color="#444444", rotation=90)
        ax.axvline(0.2, color="black", lw=0.9, zorder=1)
        ax.axvline(0.5, color="black", lw=0.9, ls=(0, (4, 2.5)), zorder=1)
        norm = []
        for b in B:
            c = np.asarray(b["curve"], float)
            z = (c - c.min()) / (c.max() - c.min()) if c.max() > c.min() else np.ones_like(c)
            norm.append(z)
            ax.plot(a, z, color=col[b["category"]], lw=0.8, alpha=0.45, zorder=2)
            ax.plot([b["argmax"]], [1.0], "o", ms=3.2, color=col[b["category"]], alpha=0.8,
                    mec="none", zorder=5, clip_on=False)
        med = np.median(np.array(norm), axis=0)
        ax.plot(a, med, color="black", lw=2.4, zorder=4)
        ax.set_title(f"{title}, {len(B)} benchmarks", loc="left", pad=6)
        ax.set_xlim(0, 1)
        ax.set_ylim(-0.03, 1.06)
        ax.set_xticks([0, 0.2, 0.5, 0.8, 1.0])
        ax.set_xticklabels(["0", "0.2", "0.5", "0.8", "1"])
        ax.set_xlabel(r"exponent $\alpha$ in $\mathrm{WAR}/N^{\alpha}$")
    axes[0].set_ylabel("score, rescaled within benchmark\n(min = 0, max = 1)")
    handles = [Line2D([], [], color=col[c], lw=1.2, label=names[c]) for c in ("judgment", "concurrent", "forecast")]
    handles += [Line2D([], [], color="black", lw=2.4, label="median curve (panel)"),
                Patch(color="#BBBBBB", alpha=0.6, label=r"pennant-race $\alpha = 1 - 1/\gamma$"),
                Line2D([], [], color="black", lw=0.9, label=r"$\alpha = 1/5$"),
                Line2D([], [], color="black", lw=0.9, ls=(0, (4, 2.5)),
                       label=r"$\alpha = 1/2$ (z-statistic hypothesis)")]
    fig.legend(handles=handles, loc="lower center", ncol=3, frameon=False, bbox_to_anchor=(0.5, -0.01),
               handlelength=2.0, columnspacing=1.2)
    fig.tight_layout(rect=(0, 0.13, 1, 1), w_pad=1.0)
    os.makedirs(FIG, exist_ok=True)
    for ext in ("pdf", "png"):
        fig.savefig(os.path.join(FIG, f"fig_alpha_curves.{ext}"), dpi=300, bbox_inches="tight")
    plt.close(fig)
    log(f"figure: {os.path.join(FIG, 'fig_alpha_curves.pdf')} (+ .png, 300 dpi)")


# ---------------------------------------------------------------------------
# Summaries
# ---------------------------------------------------------------------------
def groups(head):
    def fc(**kw):
        return [b for b in head if b["category"] == "forecast"
                and all(b.get(k) == v for k, v in kw.items())]
    return [("all career-value", head),
            ("judgment", [b for b in head if b["category"] == "judgment"]),
            ("concurrent", [b for b in head if b["category"] == "concurrent"]),
            ("forecast", [b for b in head if b["category"] == "forecast"]),
            ("forecast-hitters", fc(role_group="Hitters")),
            ("forecast-pitchers", fc(role_group="Pitchers")),
            ("forecast-checkpoint", fc(design_group="checkpoint")),
            ("forecast-midpoint", fc(design_group="midpoint"))]


def _fmt2(x):
    return str(Decimal(str(round(float(x), 6))).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP))


def count_line(lab, H):
    am = np.array([b["argmax"] for b in H])
    return (f"  {lab:20s} n={len(H):2d}  median argmax {_fmt2(np.median(am))} (IQR {_fmt2(np.percentile(am, 25))}-"
            f"{_fmt2(np.percentile(am, 75))}); intervals containing 0.2: {sum(b['has02'] for b in H)}/{len(H)}, "
            f"containing 0.5: {sum(b['has05'] for b in H)}/{len(H)}; m(0.2) > m(0.5) in "
            f"{sum(b['d02_05'] > 0 for b in H)}/{len(H)} (CI excludes 0 in favour of 0.2: "
            f"{sum(b['d02_05_lo'] > 0 for b in H)}, of 0.5: {sum(b['d02_05_hi'] < 0 for b in H)}); "
            f"m(0.2) > m(0) in {sum(b['d02_0'] > 0 for b in H)}/{len(H)} (CI > 0: {sum(b['d02_0_lo'] > 0 for b in H)}, "
            f"< 0: {sum(b['d02_0_hi'] < 0 for b in H)})")


def regret_block(lab, H):
    C = np.array([b["curve"] for b in H])
    R = C.max(axis=1, keepdims=True) - C
    rng = np.ptp(C, axis=1)
    Nn = 1 - R / np.where(rng > 0, rng, 1.0)[:, None]
    med = np.median(Nn, axis=0)
    mx, mn = R.max(axis=0), R.mean(axis=0)
    jmm, jmean = int(np.argmin(mx)), int(np.argmin(mn))
    jx = {a: int(np.flatnonzero(np.isclose(ab.ALPHAS, a))[0]) for a in REGRET_ALPHAS}
    lines = [f"  {lab:20s} n={len(H):2d}  minimax-regret alpha {ab.ALPHAS[jmm]:.2f} (max regret {mx[jmm]:.4f}); "
             f"min-mean-regret alpha {ab.ALPHAS[jmean]:.2f} (mean regret {mn[jmean]:.4f}); "
             f"median normalized curve peaks at {ab.ALPHAS[ab.argmax_idx(med)]:.2f}",
             "  " + " " * 22 + "  ".join(f"a={a:<4g} {mn[jx[a]]:.4f}/{mx[jx[a]]:.4f}" for a in REGRET_ALPHAS)
             + "   (mean/max regret)"]
    return lines


def main():
    log("Reproducing existing benchmarks")
    hof = run_sets(hof_sets())
    check_hof(hof)
    exp = run_sets(expert_sets())
    check_expert(exp, "expert_rankings.csv")
    expq = run_sets(expert_sets(quadrature=True))
    check_expert(expq, "expert_rankings_quadrature.csv")
    ck = run_sets(checkpoint_sets())
    check_checkpoint(ck)
    bench = hof + exp + ck
    new = script15_benchmarks()
    c10 = {b["short"]: b for b in ck}
    for b in new:
        if b.get("duplicate", "").startswith("same sample"):
            ref = c10.get(b["short"])
            if ref is not None:
                same = ref["n"] == b["n"] and np.allclose(ref["curve"], b["curve"], atol=1e-4)
                log(f"  script 15 '{b['short']}' identical to script 10 (n and curve): {same}")
    for b in expq:
        b["duplicate"] = "quadrature two-way combination (previous default; reference)"
    bench += new + expq
    for b in bench:
        b.setdefault("duplicate", "")
    pen = pennant_rows()
    band = (min(p["argmax"] for p in pen), max(p["argmax"] for p in pen))

    implied = {}
    if os.path.exists(os.path.join(OUT, "implied_alpha.csv")):
        implied = {r["benchmark"]: r for r in read_csv("implied_alpha.csv")}
        log(f"  regression-implied alpha* read from outputs/implied_alpha.csv ({len(implied)} benchmarks)")

    head = [b for b in bench if b["category"] in CAREER and not b["duplicate"]]
    rows = []
    for b in bench + pen:
        is_curve = "curve" in b
        im = implied.get(b["benchmark"], {})
        rows.append([
            b["benchmark"], b["category"], b["source"], b["n"], b["metric"],
            *(round(b[f"m{x:g}"], 6) if is_curve else "" for x in ab.A_REPORT),
            round(b["argmax"], 6), b["boot_median"] if not is_curve else round(b["boot_median"], 2),
            round(b["boot_lo"], 6), round(b["boot_hi"], 6), int(bool(b["has02"])), int(bool(b["has05"])),
            *((round(b["d02_05"], 6), round(b["d02_05_lo"], 6), round(b["d02_05_hi"], 6),
               round(b["d02_0"], 6), round(b["d02_0_lo"], 6), round(b["d02_0_hi"], 6)) if is_curve else [""] * 6),
            im.get("alpha_star", ""), im.get("alpha_star_lo", ""), im.get("alpha_star_hi", ""),
            int(b in head) if is_curve else 0, b.get("duplicate", "")])
    write_csv("alpha_convergence.csv",
              ["benchmark", "category", "source_script", "n", "metric", "m(0)", "m(0.2)", "m(0.5)", "m(1)",
               "argmax_alpha", "boot_median", "boot_lo", "boot_hi", "alpha0.2_in_interval",
               "alpha0.5_in_interval", "d02_05", "d02_05_lo", "d02_05_hi", "d02_0", "d02_0_lo", "d02_0_hi",
               "implied_alpha_star", "implied_alpha_star_lo", "implied_alpha_star_hi",
               "in_headline", "note"], rows)
    write_csv("alpha_curves.csv", ["benchmark", "category", "alpha", "metric"],
              [[b["benchmark"], b["category"] + ("" if not b["duplicate"] else " (not in headline)"),
                a, round(float(m), 6)] for b in bench for a, m in zip(ab.ALPHAS, b["curve"])])

    log()
    log(f"{'benchmark':80s} {'n':>5s} {'m(0)':>6s} {'m(.2)':>6s} {'m(.5)':>6s} {'m(1)':>6s} "
        f"{'argmax':>6s} {'95% boot':>11s}  m.2-m.5 [95% CI]      m.2-m0 [95% CI]")
    for b in bench:
        flag = "" if b in head else ("  (talent contrast)" if b["category"] == "talent-contrast"
                                     else "  (reference)" if "quadrature" in b["duplicate"] else "  (dup)")
        im = implied.get(b["benchmark"])
        star = f"  alpha* {float(im['alpha_star']):.2f}" if im and im.get("alpha_star") not in ("", None) else ""
        log(f"{b['benchmark'][:80]:80s} {b['n']:5d} {b['m0']:6.3f} {b['m0.2']:6.3f} {b['m0.5']:6.3f} "
            f"{b['m1']:6.3f} {b['argmax']:6.2f} [{b['boot_lo']:.2f},{b['boot_hi']:.2f}]  "
            f"{b['d02_05']:+.3f} [{b['d02_05_lo']:+.3f},{b['d02_05_hi']:+.3f}]  "
            f"{b['d02_0']:+.3f} [{b['d02_0_lo']:+.3f},{b['d02_0_hi']:+.3f}]{star}{flag}")
    for p in pen:
        log(f"{p['benchmark'][:80]:80s}  gamma {p['gamma']:.3f}  implied alpha {p['argmax']:.3f} "
            f"[{p['boot_lo']:.3f}, {p['boot_hi']:.3f}]")
    log()
    log(f"Headline (career-value curve benchmarks; duplicates, quadrature reference rows and talent "
        f"contrasts excluded): {len(head)}")
    for lab, H in groups(head):
        if H:
            log(count_line(lab, H))
    log(f"  pennant-race implied alpha (4 slope estimates): {band[0]:.3f}-{band[1]:.3f}")
    log()
    log("Regret of a fixed alpha = max_alpha m - m(alpha), metric units (AUC or Spearman), by category")
    for lab, H in [g for g in groups(head) if g[0] in ("all career-value", "judgment", "concurrent", "forecast",
                                                         "forecast-hitters", "forecast-pitchers")]:
        for line in regret_block(lab, H):
            log(line)
    log("  NOTE: benchmarks overlap (shared players, nested pools), so these counts are descriptive.")
    log()
    figure(head, band)
    with open(os.path.join(OUT, "alpha_convergence_summary.txt"), "w") as fh:
        fh.write("\n".join(LOG) + "\n")


if __name__ == "__main__":
    main()
