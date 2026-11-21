#!/usr/bin/env python3
"""Run the full (offline) reproduction pipeline in order.

Requires data/raw/ to be populated first:
    python3 fetch_data.py --pitcher-tables --standings --awards
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
STEPS = [
    "01_verify_arithmetic.py",   # derived numbers from the paper's own inputs
    "02_verify_inputs.py",       # paper inputs vs Baseball-Reference
    "03_spw_check.py",           # SPW implementation vs Gordon (2023)
    "04_hof_validation.py",      # Hall of Fame AUCs, CIs, CV alpha, SPW, c grid
    "05_alpha_sensitivity.py",   # Table 8 ranks and Spearman correlations
    "06_sigma.py",               # role-specific sigma and implied c
    "17_leaderboards.py",        # alpha = 1/5 leaderboard tables (07 checks the printed values)
    "07_rank_checks.py",         # all-time ranks and Z_1/5 values printed in the leaderboard tables
    "08_jaws_check.py",          # JAWS / S-JAWS / R-JAWS values and ranks
    "09_fwar_check.py",          # Section 10 FanGraphs fWAR robustness checks
    "10_checkpoint_prediction.py",  # early-career checkpoint forecasts
    "11_expert_rankings.py",     # agreement with expert top-100 lists
    "12_season_value.py",        # season-value convexity gamma from pennant races
    "13_null_baseline.py",       # evidence against league-average / All-Star nulls
    "14_season_unit.py",         # seasons vs events as the exposure unit of the value reading
    "15_forecast_benchmarks.py", # checkpoint / midpoint forecasts of WAR, All-Star, awards, HOF
    "18_implied_alpha.py",       # regression-implied exponents; exposure and rate persistence
    "16_alpha_convergence.py",   # all benchmarks: argmax alpha, bootstrap CIs, regret, Figure 1
    "19_convergence_tables.py",  # LaTeX tables for Section 5 / Appendix A; copies Figure 1
]


def main():
    failed = []
    for step in STEPS:
        print(f"\n{'=' * 78}\n{step}\n{'=' * 78}", flush=True)
        rc = subprocess.call([sys.executable, os.path.join(HERE, "zwar", step)])
        if rc != 0:
            failed.append(step)
    print("\nAll steps completed." if not failed else f"\nFailed steps: {failed}")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
