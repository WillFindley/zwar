# Formal Lean 4 Proofs (`ZwarProofs`)

Formal verification in Lean 4 + Mathlib (`v4.26.0`) of every derivation, proposition, identity, and inequality in *From Total WAR to WAR Rate: The α-Family and the Empirical Case for α ≈ 1/5* (Findley, 2026).

## Building and Checking

From this directory (`lean/`):

```bash
lake exe cache get
lake build
```

All theorems compile against Mathlib with zero `sorry`s and only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Mapping to `zwar_paper.tex`

| Paper Reference | Lean Theorem(s) in `ZwarProofs.lean` |
|---|---|
| Eq. (`eq:family`) & Remark (`rem:interp`, geometric mean) | `z_alpha_zero`, `z_alpha_one`, `z_alpha_weighted_geom_mean`, `abs_z_alpha_weighted_geom_mean`, `abs_z_half_geom_mean` |
| Proposition 1 (`prop:alpha`, marginal-rate threshold) | `prop_alpha_hasDerivAt`, `prop_alpha_continuous_iff`, `prop_alpha_discrete_iff`, `prop_alpha_discrete_le_continuous`, `prop_alpha_taylor_isBigO`, `prop_alpha_taylor_isLittleO` |
| Proposition 2 (`prop:target`, target scaling & forecast/regression) | `prop_target_eq`, `prop_target_order_equiv`, `prop_target_forecast_log`, `prop_target_regression_implied` |
| Proposition 3 (`prop:frequentist`, z-statistic member) | `prop_frequentist_mean`, `prop_frequentist_var`, `prop_frequentist_sd`, `prop_frequentist_snr`, `prop_frequentist_part_a`, `prop_frequentist_part_b` |
| Proposition 4 (`prop:gamma`, convex season value) | `prop_gamma_val`, `prop_gamma_order_equiv` |
| Definition 1 (`def:twoway`) & Appendix B / Sec. 6.3 | `twoway_I_alt_form`, `twoway_single_role_right`, `twoway_single_role_left`, `twoway_alpha_zero`, `twoway_pos_ratio_bound`, `stouffer_eq_zpool`, `reliever_rate_multiple` |
| Proposition 5 (`prop:lagrange`) & Remark (`rem:partition`) | `prop_lagrange_identity`, `prop_lagrange_nonneg`, `prop_lagrange_both_neg`, `rem_partition_general_lagrange` |
| Appendix E (`app:radon`, Radon's inequality & power-mean) | `radon_inequality`, `radon_equality_iff`, `twoway_ge_zpool_all_alpha`, `twoway_eq_zpool_iff`, `power_mean_season_bound`, `power_mean_season_eq_iff` |
| Proposition 6 (`prop:null`, threshold against a null rate) | `prop_null_hasDerivAt`, `prop_null_iff`, `prop_null_alpha_eff` |
| Remark (`rem:interp`, Gaussian KL divergence) | `kl_gaussian_zwar` |
