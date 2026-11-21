# From Total WAR to WAR Rate: The α-Family and the Empirical Case for α ≈ 1/5

Paper and reproduction code for *From Total WAR to WAR Rate: The α-Family and the Empirical Case for α ≈ 1/5* (Findley, 2026).

## Contents

- `zwar_paper.pdf` / `zwar_paper.tex` — full manuscript
- `figures/fig_alpha_curves.pdf` — Figure 1 used by the paper
- `repro/` — offline reproduction and validation pipeline (see [`repro/README.md`](repro/README.md) for setup, data sources, and step-by-step details)
- `lean/` — Lean 4 / Mathlib formal proofs verifying all propositions, identities, and inequalities in the paper (see [`lean/README.md`](lean/README.md))

## Data & IP Policy

Third-party datasets (Baseball-Reference, FanGraphs, Lahman/Baseball Databank, and published editorial top-100 lists) and derived pipeline outputs (`repro/data/` and `repro/outputs/`) are intentionally excluded from this public repository. Use `repro/fetch_data.py` and the instructions in [`repro/README.md`](repro/README.md) to download inputs and regenerate all outputs locally.
