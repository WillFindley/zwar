import Mathlib

/-!
# Formal Verification of Derivations in *From Total WAR to WAR Rate*

This file formalizes and verifies every mathematical proposition, identity,
and inequality in `zwar_paper.tex` against Mathlib (`v4.26.0`), with zero
`sorry`s and only standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`).
-/

open scoped Real BigOperators MeasureTheory ProbabilityTheory Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set Finset

noncomputable section

namespace ZwarProofs

/-! ## Section 0: Core Definitions -/

/-- The one-parameter α-family `Z_α = W / N^α`. -/
def Z_alpha (W N α : ℝ) : ℝ := W / N ^ α

/-- Generalized score against a null rate `r₀`: `Z_{α,r₀} = (W - r₀ N) / N^α`. -/
def Z_null (W N r₀ α : ℝ) : ℝ := (W - r₀ * N) / N ^ α

/-- Exponent `γ = 1 / (1 - α)` linking season-value convexity and two-way combination. -/
def gamma (α : ℝ) : ℝ := 1 / (1 - α)

/-- Signed power `sgn(x) * |x|^p`. -/
def signedPow (x p : ℝ) : ℝ := Real.sign x * |x| ^ p

/-- Two-coordinate inner sum `I_α = ∑_k sgn(W_k) |W_k|^γ / N_k^(γ - 1)`. -/
def I_twoway (W_pos PA W_pitch BF α : ℝ) : ℝ :=
  signedPow W_pos (gamma α) / PA ^ (gamma α - 1) +
  signedPow W_pitch (gamma α) / BF ^ (gamma α - 1)

/-- Value-consistent two-coordinate score `Z_{α,2D} = sgn(I_α) |I_α|^(1/γ)` (Definition 1). -/
def Z_twoway (W_pos PA W_pitch BF α : ℝ) : ℝ :=
  signedPow (I_twoway W_pos PA W_pitch BF α) (1 / gamma α)

/-- Pooled-exposure score `(W_pos + W_pitch) / (PA + BF)^α`. -/
def Z_pool (W_pos PA W_pitch BF α : ℝ) : ℝ :=
  (W_pos + W_pitch) / (PA + BF) ^ α

lemma gamma_pos {α : ℝ} (hα : α < 1) : 0 < gamma α := by
  unfold gamma
  have : 0 < 1 - α := sub_pos.mpr hα
  positivity

lemma one_le_gamma {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) : 1 ≤ gamma α := by
  unfold gamma
  rw [one_le_div (sub_pos.mpr h1)]
  linarith

lemma one_lt_gamma {α : ℝ} (h0 : 0 < α) (h1 : α < 1) : 1 < gamma α := by
  unfold gamma
  rw [one_lt_div (sub_pos.mpr h1)]
  linarith

lemma one_div_gamma {α : ℝ} : 1 / gamma α = 1 - α := by
  unfold gamma
  rw [one_div_one_div]

lemma alpha_mul_gamma {α : ℝ} (h1 : α ≠ 1) : α * gamma α = gamma α - 1 := by
  unfold gamma
  have hsub : 1 - α ≠ 0 := sub_ne_zero.mpr h1.symm
  field_simp [hsub]
  ring

lemma gamma_sub_one_div_gamma {α : ℝ} (h1 : α ≠ 1) : (gamma α - 1) / gamma α = α := by
  unfold gamma
  have hsub : 1 - α ≠ 0 := sub_ne_zero.mpr h1.symm
  field_simp [hsub]
  ring

lemma signedPow_nonneg {x p : ℝ} (hx : 0 ≤ x) (hp : 0 < p) : signedPow x p = x ^ p := by
  unfold signedPow
  rcases eq_or_lt_of_le hx with rfl | hpos
  · simp [Real.sign_zero, Real.zero_rpow hp.ne']
  · rw [Real.sign_of_pos hpos, one_mul, abs_of_pos hpos]

lemma signedPow_neg {x p : ℝ} (hx : x < 0) : signedPow x p = -((-x) ^ p) := by
  unfold signedPow
  rw [Real.sign_of_neg hx, abs_of_neg hx]
  ring

lemma signedPow_zero_left {p : ℝ} (hp : 0 < p) : signedPow 0 p = 0 := by
  unfold signedPow
  simp [Real.sign_zero, Real.zero_rpow hp.ne']

private lemma real_sign_mul_abs (x : ℝ) : Real.sign x * |x| = x := by
  rcases lt_trichotomy x 0 with hneg | rfl | hpos
  · rw [Real.sign_of_neg hneg, abs_of_neg hneg]; ring
  · simp [Real.sign_zero]
  · rw [Real.sign_of_pos hpos, abs_of_pos hpos, one_mul]

lemma signedPow_one_right (x : ℝ) : signedPow x 1 = x := by
  unfold signedPow
  rw [Real.rpow_one, real_sign_mul_abs]

/-! ## Section 1: Eq. (4) Endpoints and Weighted Geometric Mean -/

theorem z_alpha_zero (W N : ℝ) : Z_alpha W N 0 = W := by
  simp [Z_alpha]

theorem z_alpha_one (W N : ℝ) : Z_alpha W N 1 = W / N := by
  simp [Z_alpha]

/-- Appendix F (`app:units`): with the floor `max 0 1 = 1`, a zero-exposure player scores `W`. -/
theorem z_alpha_zero_exposure (W α : ℝ) : Z_alpha W (max 0 1) α = W := by
  unfold Z_alpha
  norm_num

/-- Section 6.1 (`sec:hitters`): scaling `(W, N)` by `c > 0` scales `Z_α` by `c^(1 - α)`. -/
theorem z_alpha_homogeneous_scaling {c W N α : ℝ} (hc : 0 < c) (hN : 0 < N) :
    Z_alpha (c * W) (c * N) α = c ^ (1 - α) * Z_alpha W N α := by
  unfold Z_alpha
  rw [Real.mul_rpow hc.le hN.le, Real.rpow_sub hc, Real.rpow_one]
  have hcα : c ^ α ≠ 0 := (Real.rpow_pos_of_pos hc α).ne'
  have hNα : N ^ α ≠ 0 := (Real.rpow_pos_of_pos hN α).ne'
  field_simp [hcα, hNα]

/-- Section 6.1 (`sec:hitters`): pairwise crossover exponent between shorter (`N₁`) and longer (`N₂`)
positive careers (`Z_α(W₁, N₁) > Z_α(W₂, N₂)` iff `α > log(W₂/W₁) / log(N₂/N₁)`). -/
theorem z_alpha_crossover_iff {W₁ N₁ W₂ N₂ α : ℝ}
    (hW₁ : 0 < W₁) (hW₂ : 0 < W₂) (hN₁ : 0 < N₁) (hNlt : N₁ < N₂) :
    Z_alpha W₁ N₁ α > Z_alpha W₂ N₂ α ↔
      α > Real.log (W₂ / W₁) / Real.log (N₂ / N₁) := by
  have hN₂ : 0 < N₂ := hN₁.trans hNlt
  have hZ₁ : 0 < Z_alpha W₁ N₁ α := by unfold Z_alpha; positivity
  have hZ₂ : 0 < Z_alpha W₂ N₂ α := by unfold Z_alpha; positivity
  have hlogN : 0 < Real.log (N₂ / N₁) := Real.log_pos ((one_lt_div hN₁).mpr hNlt)
  rw [gt_iff_lt, gt_iff_lt, ← Real.log_lt_log_iff hZ₂ hZ₁]
  unfold Z_alpha
  rw [Real.log_div hW₂.ne' (Real.rpow_pos_of_pos hN₂ _).ne',
      Real.log_div hW₁.ne' (Real.rpow_pos_of_pos hN₁ _).ne',
      Real.log_rpow hN₂, Real.log_rpow hN₁,
      Real.log_div hW₂.ne' hW₁.ne',
      div_lt_iff₀ hlogN, Real.log_div hN₂.ne' hN₁.ne']
  constructor <;> intro h <;> linarith

theorem z_alpha_weighted_geom_mean {W N α : ℝ} (hW : 0 ≤ W) (hN : 0 < N) :
    Z_alpha W N α = W ^ (1 - α) * (W / N) ^ α := by
  unfold Z_alpha
  rw [Real.div_rpow hW hN.le]
  have h1 : W ^ (1 - α) * W ^ α = W := by
    rcases eq_or_lt_of_le hW with rfl | hWpos
    · by_cases hα : α = 0
      · subst hα; simp
      · by_cases h1 : 1 - α = 0
        · have : α = 1 := by linarith
          subst this; simp
        · simp [Real.zero_rpow h1, Real.zero_rpow hα]
    · rw [← Real.rpow_add hWpos]
      simp
  calc W / N ^ α
      = (W ^ (1 - α) * W ^ α) / N ^ α := by rw [h1]
    _ = W ^ (1 - α) * (W ^ α / N ^ α) := by ring

theorem abs_z_alpha_weighted_geom_mean {W N α : ℝ} (hN : 0 < N) :
    |Z_alpha W N α| = |W| ^ (1 - α) * |W / N| ^ α := by
  unfold Z_alpha
  have hNα : 0 < N ^ α := Real.rpow_pos_of_pos hN α
  rw [abs_div, abs_of_pos hNα, abs_div, abs_of_pos hN]
  exact z_alpha_weighted_geom_mean (abs_nonneg W) hN

theorem abs_z_half_geom_mean {W N : ℝ} (hN : 0 < N) :
    |Z_alpha W N (1 / 2)| = Real.sqrt (|W| * |W / N|) := by
  rw [abs_z_alpha_weighted_geom_mean hN]
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [hhalf, ← Real.mul_rpow (abs_nonneg W) (abs_nonneg (W / N)), Real.sqrt_eq_rpow]

/-! ## Section 2: Proposition 1 (`prop:alpha`, Marginal-Rate Threshold) -/

theorem prop_alpha_hasDerivAt {W : ℝ → ℝ} {r_marg N α : ℝ}
    (hW : HasDerivAt W r_marg N) (hN : 0 < N) :
    HasDerivAt (fun n => Z_alpha (W n) n α)
      (N ^ (-α) * (r_marg - α * (W N / N))) N := by
  unfold Z_alpha
  have hpow : HasDerivAt (fun n : ℝ => n ^ α) (α * N ^ (α - 1)) N := by
    simpa using Real.hasDerivAt_rpow_const (Or.inl hN.ne')
  have hdiv := hW.div hpow (Real.rpow_pos_of_pos hN α).ne'
  convert hdiv using 1
  have hNne : N ≠ 0 := hN.ne'
  have hp1 : N ^ α ≠ 0 := (Real.rpow_pos_of_pos hN α).ne'
  have hpow_sub : N ^ (α - 1) = N ^ α / N := by
    rw [Real.rpow_sub hN, Real.rpow_one]
  have hpow_neg : N ^ (-α) = (N ^ α)⁻¹ := Real.rpow_neg hN.le α
  rw [hpow_sub, hpow_neg]
  field_simp [hNne, hp1]

theorem prop_alpha_continuous_iff {W N r_marg α : ℝ} (hN : 0 < N) :
    N ^ (-α) * (r_marg - α * (W / N)) > 0 ↔ r_marg > α * (W / N) := by
  have hpos : 0 < N ^ (-α) := Real.rpow_pos_of_pos hN (-α)
  rw [gt_iff_lt, mul_pos_iff_of_pos_left hpos, sub_pos, gt_iff_lt]

theorem prop_alpha_continuous_lt_iff {W N r_marg α : ℝ} (hN : 0 < N) :
    N ^ (-α) * (r_marg - α * (W / N)) < 0 ↔ r_marg < α * (W / N) := by
  have hpos : 0 < N ^ (-α) := Real.rpow_pos_of_pos hN (-α)
  constructor
  · intro h
    by_contra hge
    have hnn : 0 ≤ N ^ (-α) * (r_marg - α * (W / N)) :=
      mul_nonneg hpos.le (sub_nonneg.mpr (le_of_not_gt hge))
    linarith
  · intro h
    exact mul_neg_of_pos_of_neg hpos (sub_neg.mpr h)

theorem prop_alpha_discrete_iff {W N ΔW ΔN α : ℝ}
    (hN : 0 < N) (hΔN : 0 < ΔN) :
    Z_alpha (W + ΔW) (N + ΔN) α > Z_alpha W N α ↔
      ΔW / ΔN > (((1 + ΔN / N) ^ α - 1) / (ΔN / N)) * (W / N) := by
  unfold Z_alpha
  have hN_add : 0 < N + ΔN := by linarith
  have hpowN : 0 < N ^ α := Real.rpow_pos_of_pos hN α
  have hpowN_add : 0 < (N + ΔN) ^ α := Real.rpow_pos_of_pos hN_add α
  have hratio : (N + ΔN) / N = 1 + ΔN / N := by field_simp [hN.ne']
  have hpow_ratio : (N + ΔN) ^ α / N ^ α = (1 + ΔN / N) ^ α := by
    rw [← Real.div_rpow hN_add.le hN.le, hratio]
  have hrhs :
      (((1 + ΔN / N) ^ α - 1) / (ΔN / N)) * (W / N) =
        (((N + ΔN) ^ α / N ^ α - 1) * W) / ΔN := by
    rw [hpow_ratio]
    field_simp [hN.ne', hΔN.ne']
  rw [hrhs, gt_iff_lt, gt_iff_lt, div_lt_div_iff₀ hpowN hpowN_add]
  rw [div_lt_div_iff₀ hΔN hΔN]
  have hmul :
      W * (N + ΔN) ^ α < (W + ΔW) * N ^ α ↔
        ((N + ΔN) ^ α / N ^ α - 1) * W < ΔW := by
    calc W * (N + ΔN) ^ α < (W + ΔW) * N ^ α
        ↔ (W * (N + ΔN) ^ α) / N ^ α < ((W + ΔW) * N ^ α) / N ^ α :=
          (div_lt_div_iff_of_pos_right hpowN).symm
      _ ↔ ((N + ΔN) ^ α / N ^ α) * W < W + ΔW := by
          field_simp [hpowN.ne']
      _ ↔ ((N + ΔN) ^ α / N ^ α - 1) * W < ΔW := by
          constructor <;> intro h <;> linarith
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul.trans (mul_lt_mul_iff_left₀ hΔN).symm

theorem prop_alpha_discrete_le_continuous {α x : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hx : 0 < x) :
    ((1 + x) ^ α - 1) / x ≤ α := by
  let f : ℝ → ℝ := fun t => (1 + t) ^ α
  let f' : ℝ → ℝ := fun t => α * (1 + t) ^ (α - 1)
  have hf_cont : ContinuousOn f (Icc 0 x) := by
    intro t ht
    have hpos : 0 < 1 + t := by linarith [ht.1]
    exact ((continuousAt_const.add continuousAt_id).rpow_const (Or.inl hpos.ne')).continuousWithinAt
  have hf_deriv : ∀ t ∈ Ioo 0 x, HasDerivAt f (f' t) t := by
    intro t ht
    have hpos : 0 < 1 + t := by linarith [ht.1]
    have hd := (hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)
    simpa [f, f'] using hd.rpow_const (Or.inl hpos.ne')
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f f' hx hf_cont hf_deriv
  have h1 : f 0 = 1 := by simp [f]
  have h2 : f x = (1 + x) ^ α := rfl
  rw [h2, h1, sub_zero] at hslope
  rw [← hslope]
  have hcpos : 1 ≤ 1 + c := by linarith [hc.1]
  have hpow_le : (1 + c) ^ (α - 1) ≤ 1 := by
    have hle : α - 1 ≤ 0 := by linarith
    simpa using Real.rpow_le_rpow_of_exponent_le hcpos hle
  calc f' c = α * (1 + c) ^ (α - 1) := rfl
    _ ≤ α * 1 := mul_le_mul_of_nonneg_left hpow_le hα0
    _ = α := mul_one α

private lemma mvt_abs_bound {f f' : ℝ → ℝ} {K : ℝ} {k : ℕ}
    (hK : 0 ≤ K) (hf0 : f 0 = 0)
    (hderiv : ∀ t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), |f' t| ≤ K * |t| ^ k)
    {x : ℝ} (hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    |f x| ≤ K * |x| ^ (k + 1) := by
  have hf_cont : ∀ a b, a ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) → b ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) →
      ContinuousOn f (Icc a b) := by
    intro a b ha hb t ht
    have ht' : t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) :=
      ⟨by linarith [ha.1, ht.1], by linarith [hb.2, ht.2]⟩
    exact (hderiv t ht').continuousAt.continuousWithinAt
  have h0 : (0 : ℝ) ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := ⟨by norm_num, by norm_num⟩
  rcases lt_trichotomy x 0 with hneg | rfl | hpos
  · have hderiv' : ∀ t ∈ Ioo x 0, HasDerivAt f (f' t) t := fun t ht =>
      hderiv t ⟨by linarith [hx.1, ht.1], by linarith [ht.2]⟩
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f f' hneg (hf_cont x 0 hx h0) hderiv'
    have hcmem : c ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) :=
      ⟨by linarith [hx.1, hc.1], by linarith [hc.2]⟩
    have hfx : f x = f' c * x := by
      rw [hslope, hf0]; field_simp [hneg.ne]; ring
    have hcle : |c| ≤ |x| := by
      rw [abs_of_neg hc.2, abs_of_neg hneg]; linarith [hc.1]
    calc |f x| = |f' c| * |x| := by rw [hfx, abs_mul]
      _ ≤ (K * |c| ^ k) * |x| := mul_le_mul_of_nonneg_right (hbound c hcmem) (abs_nonneg x)
      _ ≤ (K * |x| ^ k) * |x| := by gcongr
      _ = K * |x| ^ (k + 1) := by rw [pow_succ]; ring
  · simp [hf0]
  · have hderiv' : ∀ t ∈ Ioo 0 x, HasDerivAt f (f' t) t := fun t ht =>
      hderiv t ⟨by linarith [ht.1], by linarith [hx.2, ht.2]⟩
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f f' hpos (hf_cont 0 x h0 hx) hderiv'
    have hcmem : c ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) :=
      ⟨by linarith [hc.1], by linarith [hx.2, hc.2]⟩
    have hfx : f x = f' c * x := by
      rw [hslope, hf0, sub_zero, sub_zero, div_mul_cancel₀ _ hpos.ne']
    have hcle : |c| ≤ |x| := by
      rw [abs_of_pos hc.1, abs_of_pos hpos]; exact hc.2.le
    calc |f x| = |f' c| * |x| := by rw [hfx, abs_mul]
      _ ≤ (K * |c| ^ k) * |x| := mul_le_mul_of_nonneg_right (hbound c hcmem) (abs_nonneg x)
      _ ≤ (K * |x| ^ k) * |x| := by gcongr
      _ = K * |x| ^ (k + 1) := by rw [pow_succ]; ring

/-- Second-order Taylor expansion of the discrete threshold factor `(1+x)^α`:
`((1 + x)^α - 1)/x - (α - α*(1-α)/2 * x) = O(x^2)` as `x → 0`, `x ≠ 0`. -/
theorem prop_alpha_taylor_isBigO (α : ℝ) :
    (fun x : ℝ => ((1 + x) ^ α - 1) / x - (α - α * (1 - α) / 2 * x))
      =O[𝓝[≠] (0 : ℝ)] (fun x : ℝ => x ^ 2) := by
  let R : ℝ → ℝ := fun x => (1 + x) ^ α - (1 + α * x + α * (α - 1) / 2 * x ^ 2)
  let R' : ℝ → ℝ := fun x => α * (1 + x) ^ (α - 1) - (α + α * (α - 1) * x)
  let R'' : ℝ → ℝ := fun x => α * (α - 1) * ((1 + x) ^ (α - 2) - 1)
  let h : ℝ → ℝ := fun x => (1 + x) ^ (α - 2) - 1
  let h' : ℝ → ℝ := fun x => (α - 2) * (1 + x) ^ (α - 3)
  have hh'_cont : ContinuousOn (fun t => |h' t|) (Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
    refine continuous_abs.comp_continuousOn ?_
    intro t ht
    have hpos : 0 < 1 + t := by linarith [ht.1]
    exact (continuousAt_const.mul
      ((continuousAt_const.add continuousAt_id).rpow_const (Or.inl hpos.ne'))).continuousWithinAt
  obtain ⟨t_max, _, ht_max⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨(0 : ℝ), by norm_num, by norm_num⟩ hh'_cont
  let M : ℝ := |h' t_max|
  have hM : 0 ≤ M := abs_nonneg _
  have hh_deriv : ∀ t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), HasDerivAt h (h' t) t := by
    intro t ht
    have hpos : 0 < 1 + t := by linarith [ht.1]
    have hd := ((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)).rpow_const (p := α - 2) (Or.inl hpos.ne')
    convert hd.sub (hasDerivAt_const t (1 : ℝ)) using 1
    simp only [h', zero_add, one_mul, sub_zero]
    rw [show (α - 2) - 1 = α - 3 by ring]
    rfl
  have hh_bound : ∀ t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), |h t| ≤ M * |t| ^ (0 + 1) :=
    fun t ht => mvt_abs_bound hM (by simp [h]) hh_deriv
      (fun u hu => by simpa using ht_max hu) ht
  let C : ℝ := |α * (α - 1)| * M
  have hC : 0 ≤ C := mul_nonneg (abs_nonneg _) hM
  have hR''_bound : ∀ t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), |R'' t| ≤ C * |t| ^ 1 := by
    intro t ht
    calc |R'' t| = |α * (α - 1)| * |h t| := by simp [R'', h, abs_mul]
      _ ≤ |α * (α - 1)| * (M * |t| ^ (0 + 1)) := mul_le_mul_of_nonneg_left (hh_bound t ht) (abs_nonneg _)
      _ = C * |t| ^ 1 := by simp [C]; ring
  have hR'_deriv : ∀ t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), HasDerivAt R' (R'' t) t := by
    intro t ht
    have hpos : 0 < 1 + t := by linarith [ht.1]
    have hd1 : HasDerivAt (fun x : ℝ => (1 + x) ^ (α - 1)) ((α - 1) * (1 + t) ^ (α - 2)) t := by
      convert ((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)).rpow_const (p := α - 1)
        (Or.inl hpos.ne') using 1
      simp only [zero_add, one_mul]
      rw [show (α - 1) - 1 = α - 2 by ring]
      rfl
    have hd2 := (hasDerivAt_const t α).mul hd1
    have hd3 := (hasDerivAt_const t α).add ((hasDerivAt_const t (α * (α - 1))).mul (hasDerivAt_id t))
    convert hd2.sub hd3 using 1
    simp [R'']; ring
  have hR'_bound : ∀ t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), |R' t| ≤ C * |t| ^ 2 :=
    fun t ht => mvt_abs_bound hC (by simp [R']) hR'_deriv hR''_bound ht
  have hR_deriv : ∀ t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), HasDerivAt R (R' t) t := by
    intro t ht
    have hpos : 0 < 1 + t := by linarith [ht.1]
    have hd1 : HasDerivAt (fun x : ℝ => (1 + x) ^ α) (α * (1 + t) ^ (α - 1)) t := by
      convert ((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)).rpow_const (p := α)
        (Or.inl hpos.ne') using 1
      simp only [zero_add, one_mul]
      rfl
    have hd2 := (hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_const t α).mul (hasDerivAt_id t))
    have hd3 := (hasDerivAt_const t (α * (α - 1) / 2)).mul ((hasDerivAt_id t).pow 2)
    convert hd1.sub (hd2.add hd3) using 1
    simp [R']; ring
  have hR_bound : ∀ t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), |R t| ≤ C * |t| ^ 3 :=
    fun t ht => mvt_abs_bound hC (by simp [R]) hR_deriv hR'_bound ht
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds
    (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)),
    self_mem_nhdsWithin] with x hx_ball hx_ne
  have hx0 : x ≠ 0 := hx_ne
  have hx_mem : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := by
    rw [Real.dist_eq, sub_zero] at hx_ball
    exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  have h_eq : ((1 + x) ^ α - 1) / x - (α - α * (1 - α) / 2 * x) = R x / x := by
    simp only [R]
    field_simp [hx0]
    ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, h_eq, abs_div, abs_sq]
  rw [div_le_iff₀ (abs_pos.mpr hx0)]
  calc |R x| ≤ C * |x| ^ 3 := hR_bound x hx_mem
    _ = C * x ^ 2 * |x| := by rw [pow_succ, sq_abs]; ring

theorem prop_alpha_taylor_isLittleO (α : ℝ) :
    (fun x : ℝ => ((1 + x) ^ α - 1) / x - (α - α * (1 - α) / 2 * x))
      =o[𝓝[≠] (0 : ℝ)] (fun x : ℝ => x) := by
  have hbig := prop_alpha_taylor_isBigO α
  have hsq : (fun x : ℝ => x ^ 2) =o[𝓝[≠] (0 : ℝ)] (fun x : ℝ => x) := by
    have h1 : (fun x : ℝ => x) =o[𝓝[≠] (0 : ℝ)] (fun _ : ℝ => (1 : ℝ)) := by
      rw [Asymptotics.isLittleO_iff]
      intro c hc
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Metric.ball_mem_nhds (0 : ℝ) hc)] with x hx
      rw [Real.dist_eq, sub_zero] at hx
      simpa using hx.le
    simpa [pow_two] using h1.mul_isBigO (Asymptotics.isBigO_refl _ _)
  exact hbig.trans_isLittleO hsq

/-! ## Section 3: Proposition 2 (`prop:target`, Target Scaling and Forecast/Regression Scaling) -/

theorem prop_target_eq {c a b W N : ℝ} (ha : a ≠ 0) (hW : 0 < W) (hN : 0 < N) :
    c * (W / N) ^ a * N ^ b = c * (Z_alpha W N (1 - b / a)) ^ a := by
  unfold Z_alpha
  rw [Real.div_rpow hW.le hN.le, Real.div_rpow hW.le (Real.rpow_pos_of_pos hN _).le]
  rw [← Real.rpow_mul hN.le]
  have hexp : (1 - b / a) * a = a - b := by field_simp [ha]
  rw [hexp, Real.rpow_sub hN]
  have hNb : N ^ b ≠ 0 := (Real.rpow_pos_of_pos hN b).ne'
  have hNa : N ^ a ≠ 0 := (Real.rpow_pos_of_pos hN a).ne'
  field_simp [hNb, hNa]

theorem prop_target_order_equiv {c a b W₁ N₁ W₂ N₂ : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hW₁ : 0 < W₁) (hN₁ : 0 < N₁) (hW₂ : 0 < W₂) (hN₂ : 0 < N₂) :
    c * (W₁ / N₁) ^ a * N₁ ^ b < c * (W₂ / N₂) ^ a * N₂ ^ b ↔
      Z_alpha W₁ N₁ (1 - b / a) < Z_alpha W₂ N₂ (1 - b / a) := by
  rw [prop_target_eq ha.ne' hW₁ hN₁, prop_target_eq ha.ne' hW₂ hN₂]
  rw [mul_lt_mul_iff_right₀ hc]
  have hZ₁ : 0 ≤ Z_alpha W₁ N₁ (1 - b / a) := by unfold Z_alpha; positivity
  have hZ₂ : 0 ≤ Z_alpha W₂ N₂ (1 - b / a) := by unfold Z_alpha; positivity
  exact Real.rpow_lt_rpow_iff hZ₁ hZ₂ ha

theorem prop_target_forecast_log {W N c₁ c₂ κ β : ℝ}
    (hW : 0 < W) (hN : 0 < N) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    Real.log (c₁ * (W / N) ^ κ * (c₂ * N ^ β)) =
      κ * Real.log W + (β - κ) * Real.log N + Real.log (c₁ * c₂) := by
  have hr : 0 < W / N := div_pos hW hN
  have h1 : 0 < (W / N) ^ κ := Real.rpow_pos_of_pos hr κ
  have h2 : 0 < N ^ β := Real.rpow_pos_of_pos hN β
  have hrewrite : c₁ * (W / N) ^ κ * (c₂ * N ^ β) = (c₁ * c₂) * ((W / N) ^ κ * N ^ β) := by ring
  rw [hrewrite, Real.log_mul (mul_pos hc₁ hc₂).ne' (mul_pos h1 h2).ne']
  rw [Real.log_mul h1.ne' h2.ne', Real.log_rpow hr, Real.log_rpow hN, Real.log_div hW.ne' hN.ne']
  ring

theorem prop_target_regression_implied {W N c_W c_N : ℝ}
    (hW : 0 < W) (hN : 0 < N) (hcW : c_W ≠ 0) :
    c_W * Real.log W + c_N * Real.log N = c_W * Real.log (Z_alpha W N (-c_N / c_W)) := by
  unfold Z_alpha
  have hNpow : 0 < N ^ (-c_N / c_W) := Real.rpow_pos_of_pos hN _
  rw [Real.log_div hW.ne' hNpow.ne', Real.log_rpow hN]
  field_simp [hcW]
  ring

/-- Section 3.2 (`sec:target`) & Table 6 (`tab:forecast`): when `κ > 0`, the forecast
exponent `1 - β/κ` clips to `0` (`≤ 0`) if and only if durability persists at least as strongly
as rate (`κ ≤ β`). -/
theorem prop_target_forecast_clip {κ β : ℝ} (hκ : 0 < κ) :
    1 - β / κ ≤ 0 ↔ κ ≤ β := by
  rw [sub_nonpos, one_le_div hκ]

/-- Section 5.1 (`sec:benchmarks`): when `c_W > 0`, ranking by the log-linear regression score
`c_W log W + c_N log N` is equivalent to ranking by `Z_alpha` at `-c_N / c_W`. -/
theorem prop_target_regression_order_equiv {W₁ N₁ W₂ N₂ c_W c_N : ℝ}
    (hW₁ : 0 < W₁) (hN₁ : 0 < N₁) (hW₂ : 0 < W₂) (hN₂ : 0 < N₂) (hcW : 0 < c_W) :
    c_W * Real.log W₁ + c_N * Real.log N₁ < c_W * Real.log W₂ + c_N * Real.log N₂ ↔
      Z_alpha W₁ N₁ (-c_N / c_W) < Z_alpha W₂ N₂ (-c_N / c_W) := by
  rw [prop_target_regression_implied hW₁ hN₁ hcW.ne',
      prop_target_regression_implied hW₂ hN₂ hcW.ne',
      mul_lt_mul_iff_right₀ hcW]
  have hZ₁ : 0 < Z_alpha W₁ N₁ (-c_N / c_W) := by unfold Z_alpha; positivity
  have hZ₂ : 0 < Z_alpha W₂ N₂ (-c_N / c_W) := by unfold Z_alpha; positivity
  exact Real.log_lt_log_iff hZ₁ hZ₂

/-! ## Section 4: Proposition 3 (`prop:frequentist`, The z-Statistic Member) -/

section Frequentist

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem prop_frequentist_mean {n : ℕ} (hn : 0 < n) (w : Fin n → Ω → ℝ)
    {r α : ℝ} (hint : ∀ i, Integrable (w i) μ) (hmean : ∀ i, ∫ ω, w i ω ∂μ = r) :
    ∫ ω, Z_alpha (∑ i, w i ω) (n : ℝ) α ∂μ = r * (n : ℝ) ^ (1 - α) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have heq : (fun ω => Z_alpha (∑ i, w i ω) (n : ℝ) α) = fun ω => (∑ i, w i ω) / (n : ℝ) ^ α := rfl
  rw [heq, integral_div, integral_finset_sum Finset.univ fun i _ => hint i]
  simp_rw [hmean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Real.rpow_sub hn_pos, Real.rpow_one]
  have hpow : (n : ℝ) ^ α ≠ 0 := (Real.rpow_pos_of_pos hn_pos α).ne'
  field_simp [hpow]

theorem prop_frequentist_var {n : ℕ} (hn : 0 < n) (w : Fin n → Ω → ℝ)
    {σ α : ℝ} (hL2 : ∀ i, MemLp (w i) 2 μ)
    (hvar : ∀ i, variance (w i) μ = σ ^ 2)
    (huncorr : ∀ i j, i ≠ j → cov[w i, w j; μ] = 0) :
    variance (fun ω => Z_alpha (∑ i, w i ω) (n : ℝ) α) μ =
      (σ * (n : ℝ) ^ ((1 / 2 : ℝ) - α)) ^ 2 := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have heq : (fun ω => Z_alpha (∑ i, w i ω) (n : ℝ) α) =
      fun ω => ((n : ℝ) ^ α)⁻¹ * (∑ i, w i ω) := by
    ext ω; unfold Z_alpha; rw [div_eq_inv_mul]
  rw [heq, variance_const_mul, variance_fun_sum hL2]
  have hsum : ∑ i : Fin n, ∑ j : Fin n, cov[w i, w j; μ] = (n : ℝ) * σ ^ 2 := by
    have hinner : ∀ i : Fin n, ∑ j : Fin n, cov[w i, w j; μ] = σ ^ 2 := by
      intro i
      rw [Finset.sum_eq_single i]
      · rw [covariance_self (hL2 i).aemeasurable, hvar i]
      · intro j _ hji; exact huncorr i j hji.symm
      · intro hi; exact absurd (Finset.mem_univ i) hi
    simp_rw [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsum]
  have hpow_half : (n : ℝ) ^ ((1 / 2 : ℝ) - α) * (n : ℝ) ^ ((1 / 2 : ℝ) - α) =
      (n : ℝ) * ((n : ℝ) ^ α)⁻¹ ^ 2 := by
    rw [← Real.rpow_add hn_pos]
    have hexp : ((1 / 2 : ℝ) - α) + ((1 / 2 : ℝ) - α) = 1 - 2 * α := by ring
    rw [hexp, Real.rpow_sub hn_pos, Real.rpow_one, mul_comm (2 : ℝ) α,
      Real.rpow_mul hn_pos.le, Real.rpow_two]
    have hne : (n : ℝ) ^ α ≠ 0 := (Real.rpow_pos_of_pos hn_pos α).ne'
    field_simp [hne]
  calc (((n : ℝ) ^ α)⁻¹) ^ 2 * ((n : ℝ) * σ ^ 2)
      = σ ^ 2 * ((n : ℝ) * (((n : ℝ) ^ α)⁻¹) ^ 2) := by ring
    _ = σ ^ 2 * ((n : ℝ) ^ ((1 / 2 : ℝ) - α) * (n : ℝ) ^ ((1 / 2 : ℝ) - α)) := by rw [← hpow_half]
    _ = (σ * (n : ℝ) ^ ((1 / 2 : ℝ) - α)) ^ 2 := by ring

theorem prop_frequentist_sd {n : ℕ} (hn : 0 < n) (w : Fin n → Ω → ℝ)
    {σ α : ℝ} (hσ : 0 < σ) (hL2 : ∀ i, MemLp (w i) 2 μ)
    (hvar : ∀ i, variance (w i) μ = σ ^ 2)
    (huncorr : ∀ i j, i ≠ j → cov[w i, w j; μ] = 0) :
    Real.sqrt (variance (fun ω => Z_alpha (∑ i, w i ω) (n : ℝ) α) μ) =
      σ * (n : ℝ) ^ ((1 / 2 : ℝ) - α) := by
  rw [prop_frequentist_var hn w hL2 hvar huncorr]
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnonneg : 0 ≤ σ * (n : ℝ) ^ ((1 / 2 : ℝ) - α) :=
    mul_nonneg hσ.le (Real.rpow_pos_of_pos hn_pos _).le
  exact Real.sqrt_sq hnonneg

theorem prop_frequentist_snr {r σ N α : ℝ} (hσ : σ ≠ 0) (hN : 0 < N) :
    (r * N ^ (1 - α)) / (σ * N ^ ((1 / 2 : ℝ) - α)) = r * Real.sqrt N / σ := by
  rw [Real.sqrt_eq_rpow]
  have hsub : N ^ (1 - α) / N ^ ((1 / 2 : ℝ) - α) = N ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_sub hN]
    congr 1; ring
  calc (r * N ^ (1 - α)) / (σ * N ^ ((1 / 2 : ℝ) - α))
      = (r / σ) * (N ^ (1 - α) / N ^ ((1 / 2 : ℝ) - α)) := by field_simp [hσ]
    _ = (r / σ) * N ^ (1 / 2 : ℝ) := by rw [hsub]
    _ = r * N ^ (1 / 2 : ℝ) / σ := by ring

theorem prop_frequentist_part_a {W N σ : ℝ} (hN : 0 < N) (hσ : σ ≠ 0) :
    (W / N) / (σ / Real.sqrt N) = Z_alpha W N (1 / 2) / σ := by
  unfold Z_alpha
  rw [← Real.sqrt_eq_rpow]
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN.le
  have hsne : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
  field_simp [hN.ne', hσ, hsne]
  rw [Real.sq_sqrt hN.le]

theorem prop_frequentist_part_b {σ α : ℝ} (hσ : 0 < σ) :
    (∀ N₁ N₂ : ℝ, 0 < N₁ → 0 < N₂ →
      σ * N₁ ^ ((1 / 2 : ℝ) - α) = σ * N₂ ^ ((1 / 2 : ℝ) - α)) ↔ α = 1 / 2 := by
  constructor
  · intro h
    have heq := h 2 1 (by norm_num) zero_lt_one
    rw [mul_left_cancel_iff_of_pos hσ, Real.one_rpow] at heq
    by_contra hne
    have hexp : (1 / 2 : ℝ) - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    rcases lt_or_gt_of_ne hexp with hlt | hgt
    · have : (2 : ℝ) ^ ((1 / 2 : ℝ) - α) < (2 : ℝ) ^ (0 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hlt
      rw [Real.rpow_zero] at this
      linarith
    · have : (2 : ℝ) ^ (0 : ℝ) < (2 : ℝ) ^ ((1 / 2 : ℝ) - α) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hgt
      rw [Real.rpow_zero] at this
      linarith
  · rintro rfl N₁ N₂ _ _
    simp

/-- Section 7 & Appendix H (`app:uncert`): relative sampling noise `SD(Z_α) / E[Z_α] = σ / (r √n)`
is invariant across all `α`. -/
theorem prop_frequentist_rel_sd_invariant {n : ℕ} (hn : 0 < n) (w : Fin n → Ω → ℝ)
    {r σ α : ℝ} (hr : r ≠ 0) (hσ : 0 < σ)
    (hL2 : ∀ i, MemLp (w i) 2 μ)
    (hmean : ∀ i, ∫ ω, w i ω ∂μ = r)
    (hvar : ∀ i, variance (w i) μ = σ ^ 2)
    (huncorr : ∀ i j, i ≠ j → cov[w i, w j; μ] = 0) :
    Real.sqrt (variance (fun ω => Z_alpha (∑ i, w i ω) (n : ℝ) α) μ) /
      (∫ ω, Z_alpha (∑ i, w i ω) (n : ℝ) α ∂μ) =
    σ / (r * Real.sqrt (n : ℝ)) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hint : ∀ i, Integrable (w i) μ := fun i => (hL2 i).integrable one_le_two
  rw [prop_frequentist_sd hn w hσ hL2 hvar huncorr,
      prop_frequentist_mean hn w hint hmean, Real.sqrt_eq_rpow]
  have hpow : (n : ℝ) ^ ((1 / 2 : ℝ) - α) / (n : ℝ) ^ (1 - α) = ((n : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
    rw [← Real.rpow_sub hn_pos, ← Real.rpow_neg hn_pos.le]
    congr 1; ring
  have h1 : (n : ℝ) ^ (1 - α) ≠ 0 := (Real.rpow_pos_of_pos hn_pos _).ne'
  have h2 : (n : ℝ) ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hn_pos _).ne'
  calc (σ * (n : ℝ) ^ ((1 / 2 : ℝ) - α)) / (r * (n : ℝ) ^ (1 - α))
      = (σ / r) * ((n : ℝ) ^ ((1 / 2 : ℝ) - α) / (n : ℝ) ^ (1 - α)) := by field_simp [hr, h1]
    _ = (σ / r) * ((n : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by rw [hpow]
    _ = σ / (r * (n : ℝ) ^ (1 / 2 : ℝ)) := by field_simp [hr, h2]

/-- Section 3.3 (`sec:zstat`, noise boundary): non-negative pairwise covariances across events
imply `Var(W) ≥ n σ²`. -/
theorem prop_frequentist_nonneg_cov_var_ge {n : ℕ} (w : Fin n → Ω → ℝ)
    {σ : ℝ} (hL2 : ∀ i, MemLp (w i) 2 μ)
    (hvar : ∀ i, variance (w i) μ = σ ^ 2)
    (hcov : ∀ i j, i ≠ j → 0 ≤ cov[w i, w j; μ]) :
    (n : ℝ) * σ ^ 2 ≤ variance (fun ω => ∑ i, w i ω) μ := by
  rw [variance_fun_sum hL2]
  have hrow : ∀ i : Fin n, σ ^ 2 ≤ ∑ j : Fin n, cov[w i, w j; μ] := by
    intro i
    rw [← Finset.add_sum_erase Finset.univ (fun j => cov[w i, w j; μ]) (Finset.mem_univ i),
        covariance_self (hL2 i).aemeasurable, hvar i]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun j hj =>
      hcov i j (Finset.ne_of_mem_erase hj).symm)
  calc (n : ℝ) * σ ^ 2
      = ∑ _i : Fin n, σ ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, cov[w i, w j; μ] :=
        Finset.sum_le_sum fun i _ => hrow i

/-- Section 3.3 (`sec:zstat`, noise boundary): non-negative pairwise covariances imply
`SD(W) ≥ σ √n`. -/
theorem prop_frequentist_nonneg_cov_sd_ge {n : ℕ} (w : Fin n → Ω → ℝ)
    {σ : ℝ} (hσ : 0 ≤ σ) (hL2 : ∀ i, MemLp (w i) 2 μ)
    (hvar : ∀ i, variance (w i) μ = σ ^ 2)
    (hcov : ∀ i j, i ≠ j → 0 ≤ cov[w i, w j; μ]) :
    σ * Real.sqrt (n : ℝ) ≤ Real.sqrt (variance (fun ω => ∑ i, w i ω) μ) := by
  have hge := prop_frequentist_nonneg_cov_var_ge w hL2 hvar hcov
  have hsqrt := Real.sqrt_le_sqrt hge
  rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq hσ, mul_comm] at hsqrt
  exact hsqrt

/-- Section 3.3 (`sec:zstat`): any model with `Var(W) < n σ²` requires strictly negative
covariance between some pair of distinct events. -/
theorem prop_frequentist_sublinear_var_exists_neg_cov {n : ℕ} (w : Fin n → Ω → ℝ)
    {σ : ℝ} (hL2 : ∀ i, MemLp (w i) 2 μ)
    (hvar : ∀ i, variance (w i) μ = σ ^ 2)
    (hlt : variance (fun ω => ∑ i, w i ω) μ < (n : ℝ) * σ ^ 2) :
    ∃ i j, i ≠ j ∧ cov[w i, w j; μ] < 0 := by
  by_contra h
  push_neg at h
  exact absurd (prop_frequentist_nonneg_cov_var_ge w hL2 hvar h) (not_le_of_gt hlt)

/-- Section 3.3 (`sec:zstat`): if `SD(W) = σ n^α` with `α < 1/2` (`n ≥ 2`, `σ > 0`),
there must exist negatively correlated events `i ≠ j` with `Cov(w_i, w_j) < 0`. -/
theorem prop_frequentist_sub_sqrt_sd_exists_neg_cov {n : ℕ} (hn : 2 ≤ n) (w : Fin n → Ω → ℝ)
    {σ α : ℝ} (hσ : 0 < σ) (hα : α < 1 / 2)
    (hL2 : ∀ i, MemLp (w i) 2 μ)
    (hvar : ∀ i, variance (w i) μ = σ ^ 2)
    (hsd : Real.sqrt (variance (fun ω => ∑ i, w i ω) μ) = σ * (n : ℝ) ^ α) :
    ∃ i j, i ≠ j ∧ cov[w i, w j; μ] < 0 := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hn_pos : (0 : ℝ) < n := by positivity
  have hvar_eq : variance (fun ω => ∑ i, w i ω) μ = σ ^ 2 * (n : ℝ) ^ (2 * α) := by
    have hsq := congrArg (· ^ 2) hsd
    dsimp only at hsq
    rw [Real.sq_sqrt (variance_nonneg _ _), mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ α) 2,
        ← Real.rpow_mul hn_pos.le] at hsq
    rw [show α * ((2 : ℕ) : ℝ) = 2 * α by ring] at hsq
    exact hsq
  have hpow_lt : (n : ℝ) ^ (2 * α) < (n : ℝ) := by
    simpa [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hn1 (by linarith : 2 * α < 1)
  have hlt : variance (fun ω => ∑ i, w i ω) μ < (n : ℝ) * σ ^ 2 := by
    rw [hvar_eq, mul_comm (n : ℝ) (σ ^ 2)]
    exact mul_lt_mul_of_pos_left hpow_lt (sq_pos_of_pos hσ)
  exact prop_frequentist_sublinear_var_exists_neg_cov w hL2 hvar hlt

/-- Section 3.3 (`sec:zstat`): persistent positive covariance (`Cov ≥ c > 0` for `i ≠ j`,
`n ≥ 2`) pushes total variance strictly above `n σ²`. -/
theorem prop_frequentist_pos_cov_var_gt {n : ℕ} (hn : 2 ≤ n) (w : Fin n → Ω → ℝ)
    {σ c : ℝ} (hc : 0 < c) (hL2 : ∀ i, MemLp (w i) 2 μ)
    (hvar : ∀ i, variance (w i) μ = σ ^ 2)
    (hcov : ∀ i j, i ≠ j → c ≤ cov[w i, w j; μ]) :
    (n : ℝ) * σ ^ 2 + (n : ℝ) * ((n : ℝ) - 1) * c ≤ variance (fun ω => ∑ i, w i ω) μ ∧
      (n : ℝ) * σ ^ 2 < variance (fun ω => ∑ i, w i ω) μ := by
  have hle : (n : ℝ) * σ ^ 2 + (n : ℝ) * ((n : ℝ) - 1) * c ≤
      variance (fun ω => ∑ i, w i ω) μ := by
    rw [variance_fun_sum hL2]
    have hcard : ∀ i : Fin n, ((Finset.univ.erase i).card : ℝ) = (n : ℝ) - 1 := by
      intro i
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      have hn1 : 1 ≤ n := by omega
      rw [Nat.cast_sub hn1, Nat.cast_one]
    have hrow : ∀ i : Fin n, σ ^ 2 + ((n : ℝ) - 1) * c ≤ ∑ j : Fin n, cov[w i, w j; μ] := by
      intro i
      rw [← Finset.add_sum_erase Finset.univ (fun j => cov[w i, w j; μ]) (Finset.mem_univ i),
          covariance_self (hL2 i).aemeasurable, hvar i]
      have hsum : ((n : ℝ) - 1) * c ≤ ∑ j ∈ Finset.univ.erase i, cov[w i, w j; μ] :=
        calc ((n : ℝ) - 1) * c
            = ∑ _j ∈ Finset.univ.erase i, c := by
              rw [Finset.sum_const, nsmul_eq_mul, hcard i]
          _ ≤ ∑ j ∈ Finset.univ.erase i, cov[w i, w j; μ] :=
              Finset.sum_le_sum fun j hj => hcov i j (Finset.ne_of_mem_erase hj).symm
      linarith
    calc (n : ℝ) * σ ^ 2 + (n : ℝ) * ((n : ℝ) - 1) * c
        = ∑ _i : Fin n, (σ ^ 2 + ((n : ℝ) - 1) * c) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, cov[w i, w j; μ] :=
          Finset.sum_le_sum fun i _ => hrow i
  refine ⟨hle, ?_⟩
  have hn_pos : (0 : ℝ) < n := by positivity
  have hn_sub : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hpos : 0 < (n : ℝ) * ((n : ℝ) - 1) * c := mul_pos (mul_pos hn_pos hn_sub) hc
  linarith

end Frequentist

/-! ## Section 5: Proposition 4 (`prop:gamma`, Convex Season Value) -/

theorem prop_gamma_val {W N E γ : ℝ} (hγ : 1 ≤ γ) (hW : 0 ≤ W) (hN : 0 < N) (hE : 0 < E) :
    let S := N / E
    let r := W / N
    let α := 1 - 1 / γ
    S * (r * E) ^ γ = E ^ (γ - 1) * W ^ γ * N ^ (1 - γ) ∧
    (S * (r * E) ^ γ) ^ (1 / γ) = E ^ α * Z_alpha W N α ∧
    (S * (r * E) ^ γ) ^ (1 / γ) = W / S ^ α ∧
    gamma α = γ := by
  intro S r α
  have hγpos : 0 < γ := by linarith
  have hEq1 : S * (r * E) ^ γ = E ^ (γ - 1) * W ^ γ * N ^ (1 - γ) := by
    have hrE : r * E = (W * E) / N := by simp only [r]; ring
    rw [hrE, Real.div_rpow (mul_nonneg hW hE.le) hN.le, Real.mul_rpow hW hE.le]
    have hE' : E ^ γ / E = E ^ (γ - 1) := by rw [Real.rpow_sub hE, Real.rpow_one]
    have hN' : N / N ^ γ = N ^ (1 - γ) := by rw [Real.rpow_sub hN, Real.rpow_one]
    calc (N / E) * (W ^ γ * E ^ γ / N ^ γ)
        = (E ^ γ / E) * W ^ γ * (N / N ^ γ) := by ring
      _ = E ^ (γ - 1) * W ^ γ * N ^ (1 - γ) := by rw [hE', hN']
  have hEq2 : (S * (r * E) ^ γ) ^ (1 / γ) = E ^ α * Z_alpha W N α := by
    rw [hEq1]
    have h1 : 0 ≤ E ^ (γ - 1) * W ^ γ :=
      mul_nonneg (Real.rpow_pos_of_pos hE _).le (Real.rpow_nonneg hW _)
    rw [Real.mul_rpow h1 (Real.rpow_pos_of_pos hN _).le,
        Real.mul_rpow (Real.rpow_pos_of_pos hE _).le (Real.rpow_nonneg hW _)]
    rw [← Real.rpow_mul hE.le, ← Real.rpow_mul hW, ← Real.rpow_mul hN.le]
    have ha1 : (γ - 1) * (1 / γ) = α := by simp only [α]; field_simp [hγpos.ne']
    have ha2 : γ * (1 / γ) = 1 := by field_simp [hγpos.ne']
    have ha3 : (1 - γ) * (1 / γ) = -α := by simp only [α]; field_simp [hγpos.ne']; ring
    rw [ha1, ha2, ha3, Real.rpow_one, Real.rpow_neg hN.le]
    unfold Z_alpha
    ring
  have hEq3 : (S * (r * E) ^ γ) ^ (1 / γ) = W / S ^ α := by
    rw [hEq2]
    unfold Z_alpha
    have hS_pow : S ^ α = N ^ α / E ^ α := Real.div_rpow hN.le hE.le α
    rw [hS_pow]
    have hEα : E ^ α ≠ 0 := (Real.rpow_pos_of_pos hE _).ne'
    have hNα : N ^ α ≠ 0 := (Real.rpow_pos_of_pos hN _).ne'
    field_simp [hEα, hNα]
  have hEq4 : gamma α = γ := by
    unfold gamma
    simp only [α]
    have : 1 - (1 - 1 / γ) = 1 / γ := by ring
    rw [this, one_div_one_div]
  exact ⟨hEq1, hEq2, hEq3, hEq4⟩

theorem prop_gamma_order_equiv {W₁ N₁ W₂ N₂ E γ : ℝ}
    (hγ : 1 ≤ γ) (hE : 0 < E) (hW₁ : 0 ≤ W₁) (hN₁ : 0 < N₁) (hW₂ : 0 ≤ W₂) (hN₂ : 0 < N₂) :
    (N₁ / E) * ((W₁ / N₁) * E) ^ γ < (N₂ / E) * ((W₂ / N₂) * E) ^ γ ↔
      Z_alpha W₁ N₁ (1 - 1 / γ) < Z_alpha W₂ N₂ (1 - 1 / γ) := by
  have hγpos : 0 < γ := by linarith
  have hv1 := (prop_gamma_val hγ hW₁ hN₁ hE).2.1
  have hv2 := (prop_gamma_val hγ hW₂ hN₂ hE).2.1
  have h1nn : 0 ≤ (N₁ / E) * ((W₁ / N₁) * E) ^ γ := by positivity
  have h2nn : 0 ≤ (N₂ / E) * ((W₂ / N₂) * E) ^ γ := by positivity
  rw [← Real.rpow_lt_rpow_iff h1nn h2nn (one_div_pos.mpr hγpos)]
  rw [hv1, hv2, mul_lt_mul_iff_right₀ (Real.rpow_pos_of_pos hE _)]

/-! ## Section 6: Definition 1 (`def:twoway`) and Appendix B / Sec. 6.3 Properties -/

theorem twoway_I_alt_form {W N α : ℝ} (hN : 0 < N) (hα : α < 1) :
    signedPow W (gamma α) / N ^ (gamma α - 1) = signedPow (Z_alpha W N α) (gamma α) := by
  unfold Z_alpha signedPow
  have hNα : 0 < N ^ α := Real.rpow_pos_of_pos hN α
  have hsgn : Real.sign (W / N ^ α) = Real.sign W := by
    rcases lt_trichotomy W 0 with hneg | rfl | hpos
    · rw [Real.sign_of_neg hneg, Real.sign_of_neg (div_neg_of_neg_of_pos hneg hNα)]
    · simp [Real.sign_zero]
    · rw [Real.sign_of_pos hpos, Real.sign_of_pos (div_pos hpos hNα)]
  rw [hsgn, abs_div, abs_of_pos hNα, Real.div_rpow (abs_nonneg W) hNα.le]
  rw [← Real.rpow_mul hN.le, alpha_mul_gamma hα.ne]
  ring

theorem twoway_single_role_right {W₁ N₁ N₂ α : ℝ} (hN₁ : 0 < N₁) (hα : α < 1) :
    Z_twoway W₁ N₁ 0 N₂ α = Z_alpha W₁ N₁ α := by
  unfold Z_twoway I_twoway
  have hg : 0 < gamma α := gamma_pos hα
  rw [signedPow_zero_left hg, zero_div, add_zero, twoway_I_alt_form hN₁ hα]
  unfold signedPow
  have hsgn : Real.sign (Real.sign (Z_alpha W₁ N₁ α) * |Z_alpha W₁ N₁ α| ^ gamma α) =
      Real.sign (Z_alpha W₁ N₁ α) := by
    rcases lt_trichotomy (Z_alpha W₁ N₁ α) 0 with hneg | h0 | hpos
    · have hpow : 0 < |Z_alpha W₁ N₁ α| ^ gamma α := Real.rpow_pos_of_pos (abs_pos.mpr hneg.ne) _
      rw [Real.sign_of_neg hneg, Real.sign_of_neg (by linarith)]
    · simp [h0, Real.sign_zero, Real.zero_rpow hg.ne']
    · have hpow : 0 < |Z_alpha W₁ N₁ α| ^ gamma α := Real.rpow_pos_of_pos (abs_pos.mpr hpos.ne') _
      rw [Real.sign_of_pos hpos, one_mul, Real.sign_of_pos hpow]
  rw [hsgn, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  rcases eq_or_ne (Z_alpha W₁ N₁ α) 0 with h0 | hne
  · simp [h0, Real.zero_rpow hg.ne']
  · have habs_sgn : |Real.sign (Z_alpha W₁ N₁ α)| = 1 := by
      rcases Real.sign_apply_eq_of_ne_zero _ hne with h | h <;> simp [h]
    rw [habs_sgn, one_mul, ← Real.rpow_mul (abs_nonneg _), mul_one_div_cancel hg.ne', Real.rpow_one]
    exact real_sign_mul_abs _

theorem twoway_single_role_left {W₂ N₁ N₂ α : ℝ} (hN₂ : 0 < N₂) (hα : α < 1) :
    Z_twoway 0 N₁ W₂ N₂ α = Z_alpha W₂ N₂ α := by
  have hcomm : Z_twoway 0 N₁ W₂ N₂ α = Z_twoway W₂ N₂ 0 N₁ α := by
    unfold Z_twoway I_twoway; rw [add_comm]
  rw [hcomm]
  exact twoway_single_role_right hN₂ hα

theorem twoway_alpha_zero (W₁ N₁ W₂ N₂ : ℝ) :
    Z_twoway W₁ N₁ W₂ N₂ 0 = W₁ + W₂ := by
  unfold Z_twoway I_twoway
  have hg : gamma 0 = 1 := by unfold gamma; norm_num
  rw [hg, sub_self, Real.rpow_zero, Real.rpow_zero, div_one, div_one, one_div_one,
      signedPow_one_right, signedPow_one_right, signedPow_one_right]

theorem twoway_pos_ratio_bound {Z₁ Z₂ α : ℝ}
    (hZ₁ : 0 < Z₁) (hZ₂ : 0 ≤ Z₂) (hle : Z₂ ≤ Z₁) (h1 : α < 1) :
    (Z₁ ^ (gamma α) + Z₂ ^ (gamma α)) ^ (1 / gamma α) =
      Z₁ * (1 + (Z₂ / Z₁) ^ (gamma α)) ^ (1 / gamma α) ∧
    (Z₁ ^ (gamma α) + Z₂ ^ (gamma α)) ^ (1 / gamma α) ≤ 2 ^ (1 - α) * Z₁ := by
  have hg : 0 < gamma α := gamma_pos h1
  have heq : (Z₁ ^ gamma α + Z₂ ^ gamma α) ^ (1 / gamma α) =
      Z₁ * (1 + (Z₂ / Z₁) ^ gamma α) ^ (1 / gamma α) := by
    have hfac : Z₁ ^ gamma α + Z₂ ^ gamma α = Z₁ ^ gamma α * (1 + (Z₂ / Z₁) ^ gamma α) := by
      rw [Real.div_rpow hZ₂ hZ₁.le]
      have hne : Z₁ ^ gamma α ≠ 0 := (Real.rpow_pos_of_pos hZ₁ _).ne'
      field_simp [hne]
    rw [hfac, Real.mul_rpow (Real.rpow_pos_of_pos hZ₁ _).le (by positivity),
        ← Real.rpow_mul hZ₁.le, mul_one_div_cancel hg.ne', Real.rpow_one]
  refine ⟨heq, ?_⟩
  rw [heq, mul_comm Z₁]
  gcongr
  rw [← one_div_gamma]
  refine Real.rpow_le_rpow (by positivity) ?_ (one_div_pos.mpr hg).le
  have hr : Z₂ / Z₁ ≤ 1 := (div_le_one hZ₁).mpr hle
  have : (Z₂ / Z₁) ^ gamma α ≤ (1 : ℝ) ^ gamma α :=
    Real.rpow_le_rpow (div_nonneg hZ₂ hZ₁.le) hr hg.le
  linarith [Real.one_rpow (gamma α)]

theorem stouffer_eq_zpool {W_pos PA W_pitch BF : ℝ} (hPA : 0 < PA) (hBF : 0 < BF) :
    (Real.sqrt PA * Z_alpha W_pos PA (1 / 2) + Real.sqrt BF * Z_alpha W_pitch BF (1 / 2)) /
      Real.sqrt (PA + BF) = Z_pool W_pos PA W_pitch BF (1 / 2) := by
  unfold Z_alpha Z_pool
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  have h1 : Real.sqrt PA ≠ 0 := (Real.sqrt_pos.mpr hPA).ne'
  have h2 : Real.sqrt BF ≠ 0 := (Real.sqrt_pos.mpr hBF).ne'
  field_simp [h1, h2]

theorem reliever_rate_multiple {r_RP r_SP N c α : ℝ} (hN : 0 < N) (hc : 0 < c) :
    r_RP * (N / c) ^ (1 - α) = r_SP * N ^ (1 - α) ↔ r_RP = c ^ (1 - α) * r_SP := by
  rw [Real.div_rpow hN.le hc.le]
  have hNpow : N ^ (1 - α) ≠ 0 := (Real.rpow_pos_of_pos hN _).ne'
  have hcpow : c ^ (1 - α) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
  constructor <;> intro h
  · have h1 : r_RP / c ^ (1 - α) = r_SP := by
      apply mul_right_cancel₀ hNpow
      linarith [show r_RP * (N ^ (1 - α) / c ^ (1 - α)) = (r_RP / c ^ (1 - α)) * N ^ (1 - α) by ring]
    rw [(div_eq_iff hcpow).mp h1, mul_comm]
  · rw [h]; field_simp [hcpow]

/-- Section 6.4 (`sec:twoway_empirical`): exact two-coordinate positive ratio formula for
`Z_{α,2D}` with `Z₁ ≥ Z₂ ≥ 0` and `ρ = Z₂/Z₁`: equals `Z₁ (1 + ρ^γ)^(1/γ)`, lies in
`[Z₁, 2^(1-α) Z₁]`, equals `Z₁` iff `Z₂ = 0`, and equals `2^(1-α) Z₁` iff `ρ = 1`. -/
theorem twoway_pos_ratio_exact {W₁ N₁ W₂ N₂ α : ℝ}
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hα : α < 1)
    (hZ₁ : 0 < Z_alpha W₁ N₁ α) (hZ₂ : 0 ≤ Z_alpha W₂ N₂ α)
    (hle : Z_alpha W₂ N₂ α ≤ Z_alpha W₁ N₁ α) :
    let Z₁ := Z_alpha W₁ N₁ α
    let Z₂ := Z_alpha W₂ N₂ α
    let ρ := Z₂ / Z₁
    Z_twoway W₁ N₁ W₂ N₂ α = Z₁ * (1 + ρ ^ gamma α) ^ (1 / gamma α) ∧
    (Z₁ ≤ Z_twoway W₁ N₁ W₂ N₂ α ∧ (Z_twoway W₁ N₁ W₂ N₂ α = Z₁ ↔ Z₂ = 0)) ∧
    (Z_twoway W₁ N₁ W₂ N₂ α ≤ 2 ^ (1 - α) * Z₁ ∧ (Z_twoway W₁ N₁ W₂ N₂ α = 2 ^ (1 - α) * Z₁ ↔ ρ = 1)) := by
  intro Z₁ Z₂ ρ
  have hg : 0 < gamma α := gamma_pos hα
  have hinv : 0 < 1 / gamma α := one_div_pos.mpr hg
  have hW₁ : 0 ≤ W₁ := by
    have hpow : 0 < N₁ ^ α := Real.rpow_pos_of_pos hN₁ α
    calc 0 ≤ Z₁ * N₁ ^ α := by positivity
      _ = W₁ := div_mul_cancel₀ W₁ hpow.ne'
  have hW₂ : 0 ≤ W₂ := by
    have hpow : 0 < N₂ ^ α := Real.rpow_pos_of_pos hN₂ α
    calc 0 ≤ Z₂ * N₂ ^ α := by positivity
      _ = W₂ := div_mul_cancel₀ W₂ hpow.ne'
  have hI : I_twoway W₁ N₁ W₂ N₂ α = Z₁ ^ gamma α + Z₂ ^ gamma α := by
    unfold I_twoway
    rw [twoway_I_alt_form hN₁ hα, twoway_I_alt_form hN₂ hα,
        signedPow_nonneg hZ₁.le hg, signedPow_nonneg hZ₂ hg]
  have hInn : 0 ≤ I_twoway W₁ N₁ W₂ N₂ α := by rw [hI]; positivity
  have hZtw : Z_twoway W₁ N₁ W₂ N₂ α = (Z₁ ^ gamma α + Z₂ ^ gamma α) ^ (1 / gamma α) := by
    unfold Z_twoway
    rw [signedPow_nonneg hInn hinv, hI]
  obtain ⟨heq, hle_bound⟩ := twoway_pos_ratio_bound hZ₁ hZ₂ hle hα
  have hform : Z_twoway W₁ N₁ W₂ N₂ α = Z₁ * (1 + ρ ^ gamma α) ^ (1 / gamma α) := by
    rw [hZtw, heq]
  have hρ_nn : 0 ≤ ρ := div_nonneg hZ₂ hZ₁.le
  have hge_Z1 : Z₁ ≤ Z_twoway W₁ N₁ W₂ N₂ α := by
    rw [hform]
    calc Z₁ = Z₁ * (1 : ℝ) ^ (1 / gamma α) := by simp
      _ ≤ Z₁ * (1 + ρ ^ gamma α) ^ (1 / gamma α) := by
          gcongr
          linarith [Real.rpow_nonneg hρ_nn (gamma α)]
  have heq_Z1_iff : Z_twoway W₁ N₁ W₂ N₂ α = Z₁ ↔ Z₂ = 0 := by
    have h1_iff : (1 + ρ ^ gamma α) ^ (1 / gamma α) = 1 ↔ 1 + ρ ^ gamma α = 1 := by
      have h1pow : (1 : ℝ) ^ (1 / gamma α) = 1 := Real.one_rpow _
      calc (1 + ρ ^ gamma α) ^ (1 / gamma α) = 1
          ↔ (1 + ρ ^ gamma α) ^ (1 / gamma α) = (1 : ℝ) ^ (1 / gamma α) := by rw [h1pow]
        _ ↔ 1 + ρ ^ gamma α = 1 :=
            Real.rpow_left_inj (by positivity) zero_le_one hinv.ne'
    rw [hform, mul_eq_left₀ hZ₁.ne', h1_iff]
    constructor
    · intro h
      have hρ0 : ρ ^ gamma α = 0 := by linarith
      rw [Real.rpow_eq_zero_iff_of_nonneg hρ_nn] at hρ0
      exact (div_eq_zero_iff.mp hρ0.1).resolve_right hZ₁.ne'
    · intro h
      have hρ0 : ρ = 0 := by simp [ρ, h]
      rw [hρ0, Real.zero_rpow hg.ne', add_zero]
  have heq_2_iff : Z_twoway W₁ N₁ W₂ N₂ α = 2 ^ (1 - α) * Z₁ ↔ ρ = 1 := by
    rw [hform, mul_comm (2 ^ (1 - α)) Z₁, mul_eq_mul_left_iff, or_iff_left hZ₁.ne',
        ← one_div_gamma, Real.rpow_left_inj (by positivity) (by norm_num) hinv.ne']
    constructor
    · intro h
      have hρ1 : ρ ^ gamma α = 1 := by linarith
      rw [← Real.one_rpow (gamma α), Real.rpow_left_inj hρ_nn zero_le_one hg.ne'] at hρ1
      exact hρ1
    · intro h
      rw [h, Real.one_rpow]
      norm_num
  exact ⟨hform, ⟨hge_Z1, heq_Z1_iff⟩, ⟨hZtw ▸ hle_bound, heq_2_iff⟩⟩

private lemma signedPow_mul_pos {c x p : ℝ} (hc : 0 < c) :
    signedPow (c * x) p = c ^ p * signedPow x p := by
  unfold signedPow
  have hsgn : Real.sign (c * x) = Real.sign x := by
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · rw [Real.sign_of_neg hx, Real.sign_of_neg (mul_neg_of_pos_of_neg hc hx)]
    · simp [Real.sign_zero]
    · rw [Real.sign_of_pos hx, Real.sign_of_pos (mul_pos hc hx)]
  rw [hsgn, abs_mul, abs_of_pos hc, Real.mul_rpow hc.le (abs_nonneg x)]
  ring

/-- Scaling all exposures and values in `Z_{α,2D}` by `c > 0` scales the score by `c^(1 - α)`. -/
theorem z_twoway_homogeneous_scaling {c W₁ N₁ W₂ N₂ α : ℝ}
    (hc : 0 < c) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hα : α < 1) :
    Z_twoway (c * W₁) (c * N₁) (c * W₂) (c * N₂) α =
      c ^ (1 - α) * Z_twoway W₁ N₁ W₂ N₂ α := by
  have hg : 0 < gamma α := gamma_pos hα
  have hI : I_twoway (c * W₁) (c * N₁) (c * W₂) (c * N₂) α =
      c * I_twoway W₁ N₁ W₂ N₂ α := by
    unfold I_twoway
    rw [signedPow_mul_pos hc, signedPow_mul_pos hc,
        Real.mul_rpow hc.le hN₁.le, Real.mul_rpow hc.le hN₂.le]
    have hcγ : c ^ gamma α / c ^ (gamma α - 1) = c := by
      rw [Real.rpow_sub hc, Real.rpow_one]
      have hcp : c ^ gamma α ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
      field_simp [hcp]
    have hN1p : N₁ ^ (gamma α - 1) ≠ 0 := (Real.rpow_pos_of_pos hN₁ _).ne'
    have hN2p : N₂ ^ (gamma α - 1) ≠ 0 := (Real.rpow_pos_of_pos hN₂ _).ne'
    calc c ^ gamma α * signedPow W₁ (gamma α) / (c ^ (gamma α - 1) * N₁ ^ (gamma α - 1)) +
          c ^ gamma α * signedPow W₂ (gamma α) / (c ^ (gamma α - 1) * N₂ ^ (gamma α - 1))
        = (c ^ gamma α / c ^ (gamma α - 1)) * (signedPow W₁ (gamma α) / N₁ ^ (gamma α - 1)) +
          (c ^ gamma α / c ^ (gamma α - 1)) * (signedPow W₂ (gamma α) / N₂ ^ (gamma α - 1)) := by
            ring
      _ = c * (signedPow W₁ (gamma α) / N₁ ^ (gamma α - 1) +
               signedPow W₂ (gamma α) / N₂ ^ (gamma α - 1)) := by rw [hcγ]; ring
  unfold Z_twoway
  rw [hI, signedPow_mul_pos hc, one_div_gamma]

/-- Section 6.4 (`sec:twoway_empirical`, Ruth pooling threshold): pooling a secondary record
`(W₂, N₂)` onto `(W₁, N₁)` raises the score over `Z_α(W₁, N₁)` iff the secondary rate exceeds
`((1 + N₂/N₁)^α - 1) * (N₁/N₂)` times the primary rate (an instance of Proposition 1). -/
theorem zpool_gt_primary_iff {W₁ N₁ W₂ N₂ α : ℝ}
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) :
    Z_pool W₁ N₁ W₂ N₂ α > Z_alpha W₁ N₁ α ↔
      W₂ / N₂ > (((1 + N₂ / N₁) ^ α - 1) * (N₁ / N₂)) * (W₁ / N₁) := by
  have hpool : Z_pool W₁ N₁ W₂ N₂ α = Z_alpha (W₁ + W₂) (N₁ + N₂) α := rfl
  have hfac : ((1 + N₂ / N₁) ^ α - 1) / (N₂ / N₁) =
      ((1 + N₂ / N₁) ^ α - 1) * (N₁ / N₂) := by
    rw [div_eq_mul_inv, inv_div]
  rw [hpool, ← hfac]
  exact prop_alpha_discrete_iff hN₁ hN₂

/-- Section 3.5 (`sec:twoway_theory`): for non-negative concurrent roles and `γ ≥ 1`, adding
WAR within a season before applying convexity gives at least as much value as separating roles. -/
theorem concurrent_season_superadditive {w₁ w₂ γ : ℝ}
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hγ : 1 ≤ γ) :
    w₁ ^ γ + w₂ ^ γ ≤ (w₁ + w₂) ^ γ :=
  Real.add_rpow_le_rpow_add hw₁ hw₂ hγ

/-- Section 3.5 (`sec:twoway_theory`): strict superadditivity of `(w₁ + w₂)^γ` for
positive concurrent roles and `γ > 1` (`α > 0`). -/
theorem concurrent_season_strict_superadditive {w₁ w₂ γ : ℝ}
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hγ : 1 < γ) :
    w₁ ^ γ + w₂ ^ γ < (w₁ + w₂) ^ γ := by
  set s := w₁ + w₂
  have hs : 0 < s := add_pos hw₁ hw₂
  have hu₁ : w₁ / s < 1 := (div_lt_one hs).mpr (by linarith)
  have hu₂ : w₂ / s < 1 := (div_lt_one hs).mpr (by linarith)
  have h1 : (w₁ / s) ^ γ < w₁ / s := Real.rpow_lt_self_of_lt_one (div_pos hw₁ hs) hu₁ hγ
  have h2 : (w₂ / s) ^ γ < w₂ / s := Real.rpow_lt_self_of_lt_one (div_pos hw₂ hs) hu₂ hγ
  have hsum : (w₁ / s) ^ γ + (w₂ / s) ^ γ < 1 := by
    calc (w₁ / s) ^ γ + (w₂ / s) ^ γ < w₁ / s + w₂ / s := add_lt_add h1 h2
      _ = (w₁ + w₂) / s := by ring
      _ = 1 := div_self hs.ne'
  rw [Real.div_rpow hw₁.le hs.le, Real.div_rpow hw₂.le hs.le, ← add_div,
      div_lt_one (Real.rpow_pos_of_pos hs γ)] at hsum
  exact hsum

/-! ## Section 7: Proposition 5 (`prop:lagrange`) and Remark (`rem:partition`) -/

theorem prop_lagrange_identity {W_pos PA W_pitch BF : ℝ} (hPA : PA ≠ 0) (hBF : BF ≠ 0)
    (hsum : PA + BF ≠ 0) :
    W_pos ^ 2 / PA + W_pitch ^ 2 / BF - (W_pos + W_pitch) ^ 2 / (PA + BF) =
      (PA * BF / (PA + BF)) * (W_pos / PA - W_pitch / BF) ^ 2 := by
  field_simp [hPA, hBF, hsum]
  ring

/-- Exact squared-difference identity of Proposition 5 (`prop:lagrange`, Eq. 13) directly in
terms of `Z_twoway` and `Z_pool` for non-negative coordinates. -/
theorem prop_lagrange_sq_diff {W_pos PA W_pitch BF : ℝ}
    (hWp : 0 ≤ W_pos) (hWq : 0 ≤ W_pitch) (hPA : 0 < PA) (hBF : 0 < BF) :
    Z_twoway W_pos PA W_pitch BF (1 / 2) ^ 2 - Z_pool W_pos PA W_pitch BF (1 / 2) ^ 2 =
      (PA * BF / (PA + BF)) * (W_pos / PA - W_pitch / BF) ^ 2 := by
  have hg : gamma (1 / 2) = 2 := by unfold gamma; norm_num
  have hI : I_twoway W_pos PA W_pitch BF (1 / 2) = W_pos ^ 2 / PA + W_pitch ^ 2 / BF := by
    unfold I_twoway
    rw [hg, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_one]
    rw [signedPow_nonneg hWp (by norm_num), signedPow_nonneg hWq (by norm_num)]
    rw [Real.rpow_two, Real.rpow_two]
  have hInn : 0 ≤ I_twoway W_pos PA W_pitch BF (1 / 2) := by rw [hI]; positivity
  have hZtw_sq : Z_twoway W_pos PA W_pitch BF (1 / 2) ^ 2 = W_pos ^ 2 / PA + W_pitch ^ 2 / BF := by
    unfold Z_twoway
    rw [hg, signedPow_nonneg hInn (by norm_num), ← Real.sqrt_eq_rpow, Real.sq_sqrt hInn, hI]
  have hZpl_sq : Z_pool W_pos PA W_pitch BF (1 / 2) ^ 2 = (W_pos + W_pitch) ^ 2 / (PA + BF) := by
    unfold Z_pool
    rw [← Real.sqrt_eq_rpow, div_pow, Real.sq_sqrt (add_pos hPA hBF).le]
  rw [hZtw_sq, hZpl_sq]
  exact prop_lagrange_identity hPA.ne' hBF.ne' (add_pos hPA hBF).ne'

theorem prop_lagrange_nonneg {W_pos PA W_pitch BF : ℝ}
    (hWp : 0 ≤ W_pos) (hWq : 0 ≤ W_pitch) (hPA : 0 < PA) (hBF : 0 < BF) :
    Z_twoway W_pos PA W_pitch BF (1 / 2) ≥ Z_pool W_pos PA W_pitch BF (1 / 2) ∧
      (Z_twoway W_pos PA W_pitch BF (1 / 2) = Z_pool W_pos PA W_pitch BF (1 / 2) ↔
        W_pos / PA = W_pitch / BF) := by
  have hg : gamma (1 / 2) = 2 := by unfold gamma; norm_num
  have hI : I_twoway W_pos PA W_pitch BF (1 / 2) = W_pos ^ 2 / PA + W_pitch ^ 2 / BF := by
    unfold I_twoway
    rw [hg, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_one]
    rw [signedPow_nonneg hWp (by norm_num), signedPow_nonneg hWq (by norm_num)]
    rw [Real.rpow_two, Real.rpow_two]
  have hInn : 0 ≤ I_twoway W_pos PA W_pitch BF (1 / 2) := by rw [hI]; positivity
  have hZtw : Z_twoway W_pos PA W_pitch BF (1 / 2) = Real.sqrt (W_pos ^ 2 / PA + W_pitch ^ 2 / BF) := by
    unfold Z_twoway
    rw [hg, show (1 : ℝ) / 2 = 1 / 2 by norm_num, signedPow_nonneg hInn (by norm_num), hI, Real.sqrt_eq_rpow]
  have hZpl : Z_pool W_pos PA W_pitch BF (1 / 2) = Real.sqrt ((W_pos + W_pitch) ^ 2 / (PA + BF)) := by
    unfold Z_pool
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (add_nonneg hWp hWq)]
  have hid := prop_lagrange_identity (W_pos := W_pos) (W_pitch := W_pitch)
    hPA.ne' hBF.ne' (add_pos hPA hBF).ne'
  have hle : (W_pos + W_pitch) ^ 2 / (PA + BF) ≤ W_pos ^ 2 / PA + W_pitch ^ 2 / BF := by
    have hrem : 0 ≤ (PA * BF / (PA + BF)) * (W_pos / PA - W_pitch / BF) ^ 2 := by positivity
    linarith
  rw [hZtw, hZpl]
  refine ⟨Real.sqrt_le_sqrt hle, ?_⟩
  rw [Real.sqrt_inj (by positivity) (by positivity)]
  constructor
  · intro heq
    have hrem0 : (PA * BF / (PA + BF)) * (W_pos / PA - W_pitch / BF) ^ 2 = 0 := by linarith
    have hc : 0 < PA * BF / (PA + BF) := by positivity
    rw [mul_eq_zero] at hrem0
    rcases hrem0 with h0 | h0
    · exact absurd h0 hc.ne'
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h0)
  · intro heq
    have hrem0 : (PA * BF / (PA + BF)) * (W_pos / PA - W_pitch / BF) ^ 2 = 0 := by
      simp [heq]
    linarith

theorem prop_lagrange_both_neg {W_pos PA W_pitch BF : ℝ}
    (hWp : W_pos < 0) (hWq : W_pitch < 0) (hPA : 0 < PA) (hBF : 0 < BF) :
    Z_twoway W_pos PA W_pitch BF (1 / 2) ≤ Z_pool W_pos PA W_pitch BF (1 / 2) ∧
      Z_pool W_pos PA W_pitch BF (1 / 2) < 0 := by
  have hg : gamma (1 / 2) = 2 := by unfold gamma; norm_num
  have hI : I_twoway W_pos PA W_pitch BF (1 / 2) = -(W_pos ^ 2 / PA + W_pitch ^ 2 / BF) := by
    unfold I_twoway
    rw [hg, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_one]
    rw [signedPow_neg hWp, signedPow_neg hWq, Real.rpow_two, Real.rpow_two]
    ring
  have hI_neg : I_twoway W_pos PA W_pitch BF (1 / 2) < 0 := by
    rw [hI]
    have hpos : 0 < W_pos ^ 2 / PA + W_pitch ^ 2 / BF := by
      exact add_pos (div_pos (sq_pos_of_neg hWp) hPA) (div_pos (sq_pos_of_neg hWq) hBF)
    linarith
  have hZtw : Z_twoway W_pos PA W_pitch BF (1 / 2) =
      -Real.sqrt (W_pos ^ 2 / PA + W_pitch ^ 2 / BF) := by
    unfold Z_twoway
    rw [hg, signedPow_neg hI_neg, hI, neg_neg, Real.sqrt_eq_rpow]
  have hZpl : Z_pool W_pos PA W_pitch BF (1 / 2) =
      -Real.sqrt ((W_pos + W_pitch) ^ 2 / (PA + BF)) := by
    unfold Z_pool
    rw [← Real.sqrt_eq_rpow]
    have hsum_neg : W_pos + W_pitch < 0 := by linarith
    have hsq : Real.sqrt ((W_pos + W_pitch) ^ 2) = -(W_pos + W_pitch) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_neg hsum_neg]
    rw [Real.sqrt_div (sq_nonneg _), hsq]
    ring
  have hid := prop_lagrange_identity (W_pos := W_pos) (W_pitch := W_pitch)
    hPA.ne' hBF.ne' (add_pos hPA hBF).ne'
  have hle : (W_pos + W_pitch) ^ 2 / (PA + BF) ≤ W_pos ^ 2 / PA + W_pitch ^ 2 / BF := by
    have hrem : 0 ≤ (PA * BF / (PA + BF)) * (W_pos / PA - W_pitch / BF) ^ 2 := by positivity
    linarith
  rw [hZtw, hZpl]
  refine ⟨neg_le_neg (Real.sqrt_le_sqrt hle), ?_⟩
  rw [neg_lt_zero]
  exact Real.sqrt_pos.mpr (div_pos (sq_pos_of_neg (by linarith)) (add_pos hPA hBF))

theorem rem_partition_general_lagrange {ι : Type*} (s : Finset ι)
    (W N : ι → ℝ) (hN : ∀ j ∈ s, 0 < N j) (hS : 0 < ∑ j ∈ s, N j) :
    (∑ j ∈ s, W j ^ 2 / N j) - (∑ j ∈ s, W j) ^ 2 / (∑ j ∈ s, N j) =
      (1 / (2 * ∑ j ∈ s, N j)) *
        ∑ j ∈ s, ∑ k ∈ s, N j * N k * (W j / N j - W k / N k) ^ 2 ∧
    0 ≤ (∑ j ∈ s, W j ^ 2 / N j) - (∑ j ∈ s, W j) ^ 2 / (∑ j ∈ s, N j) := by
  have hNne : ∀ j ∈ s, N j ≠ 0 := fun j hj => (hN j hj).ne'
  have hterm : ∀ j ∈ s, ∀ k ∈ s,
      N j * N k * (W j / N j - W k / N k) ^ 2 =
        N k * (W j ^ 2 / N j) + N j * (W k ^ 2 / N k) - 2 * W j * W k := by
    intro j hj k hk
    have hj0 := hNne j hj
    have hk0 := hNne k hk
    field_simp [hj0, hk0]
    ring
  have hdouble :
      ∑ j ∈ s, ∑ k ∈ s, N j * N k * (W j / N j - W k / N k) ^ 2 =
        2 * (∑ j ∈ s, N j) * (∑ j ∈ s, W j ^ 2 / N j) - 2 * (∑ j ∈ s, W j) ^ 2 := by
    calc ∑ j ∈ s, ∑ k ∈ s, N j * N k * (W j / N j - W k / N k) ^ 2
        = ∑ j ∈ s, ∑ k ∈ s, (N k * (W j ^ 2 / N j) + N j * (W k ^ 2 / N k) - 2 * W j * W k) := by
          refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => hterm j hj k hk
      _ = ∑ j ∈ s, ((∑ k ∈ s, N k * (W j ^ 2 / N j)) + (∑ k ∈ s, N j * (W k ^ 2 / N k)) -
            (∑ k ∈ s, 2 * W j * W k)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      _ = (∑ j ∈ s, (∑ k ∈ s, N k) * (W j ^ 2 / N j)) +
          (∑ j ∈ s, N j * (∑ k ∈ s, W k ^ 2 / N k)) -
          (∑ j ∈ s, 2 * W j * (∑ k ∈ s, W k)) := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      _ = 2 * (∑ j ∈ s, N j) * (∑ j ∈ s, W j ^ 2 / N j) - 2 * (∑ j ∈ s, W j) ^ 2 := by
          simp only [← Finset.sum_mul, ← Finset.mul_sum, pow_two]
          ring
  have heq : (∑ j ∈ s, W j ^ 2 / N j) - (∑ j ∈ s, W j) ^ 2 / (∑ j ∈ s, N j) =
      (1 / (2 * ∑ j ∈ s, N j)) *
        ∑ j ∈ s, ∑ k ∈ s, N j * N k * (W j / N j - W k / N k) ^ 2 := by
    rw [hdouble]
    field_simp [hS.ne']
  refine ⟨heq, ?_⟩
  rw [heq]
  refine mul_nonneg (by positivity) ?_
  refine Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun k hk => ?_
  exact mul_nonneg (mul_nonneg (hN j hj).le (hN k hk).le) (sq_nonneg _)

/-! ## Section 8: Appendix E (`app:radon`, Radon's Inequality and Power-Mean Bound) -/

theorem radon_inequality {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (W N : ι → ℝ) {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1)
    (hW : ∀ j ∈ s, 0 ≤ W j) (hN : ∀ j ∈ s, 0 < N j) :
    (∑ j ∈ s, (Z_alpha (W j) (N j) α) ^ gamma α) ^ (1 / gamma α) ≥
      (∑ j ∈ s, W j) / (∑ j ∈ s, N j) ^ α := by
  have hgpos : 0 < gamma α := gamma_pos h1
  have hg_ge : 1 ≤ gamma α := one_le_gamma h0 h1
  have hS : 0 < ∑ j ∈ s, N j := Finset.sum_pos hN hs
  let S := ∑ j ∈ s, N j
  let p : ι → ℝ := fun j => N j / S
  let r : ι → ℝ := fun j => W j / N j
  have hp_nonneg : ∀ j ∈ s, 0 ≤ p j := fun j hj => div_nonneg (hN j hj).le hS.le
  have hp_sum : ∑ j ∈ s, p j = 1 := by
    dsimp only [p]
    rw [← Finset.sum_div]
    exact div_self hS.ne'
  have hr_mem : ∀ j ∈ s, r j ∈ Ici (0 : ℝ) := fun j hj => div_nonneg (hW j hj) (hN j hj).le
  have hjensen : (∑ j ∈ s, p j • r j) ^ gamma α ≤ ∑ j ∈ s, p j • (r j ^ gamma α) :=
    (convexOn_rpow hg_ge).map_sum_le hp_nonneg hp_sum hr_mem
  have hjensen' : ((∑ j ∈ s, W j) / S) ^ gamma α ≤
      (∑ j ∈ s, (Z_alpha (W j) (N j) α) ^ gamma α) / S := by
    have hlhs : ∑ j ∈ s, p j • r j = (∑ j ∈ s, W j) / S := by
      simp only [p, r, smul_eq_mul]
      have hterm : ∀ j ∈ s, (N j / S) * (W j / N j) = W j / S := by
        intro j hj; field_simp [(hN j hj).ne', hS.ne']
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
    have hrhs : ∑ j ∈ s, p j • (r j ^ gamma α) =
        (∑ j ∈ s, (Z_alpha (W j) (N j) α) ^ gamma α) / S := by
      simp only [p, r, smul_eq_mul, Z_alpha]
      have hterm : ∀ j ∈ s, (N j / S) * (W j / N j) ^ gamma α =
          (W j / N j ^ α) ^ gamma α / S := by
        intro j hj
        rw [Real.div_rpow (hW j hj) (hN j hj).le,
            Real.div_rpow (hW j hj) (Real.rpow_pos_of_pos (hN j hj) _).le,
            ← Real.rpow_mul (hN j hj).le, alpha_mul_gamma h1.ne]
        have hNj : N j ^ (gamma α - 1) = N j ^ gamma α / N j := by
          rw [Real.rpow_sub (hN j hj), Real.rpow_one]
        rw [hNj]
        have h1' : N j ^ gamma α ≠ 0 := (Real.rpow_pos_of_pos (hN j hj) _).ne'
        field_simp [(hN j hj).ne', hS.ne', h1']
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
    rwa [hlhs, hrhs] at hjensen
  have hW_sum_nn : 0 ≤ ∑ j ∈ s, W j := Finset.sum_nonneg hW
  rw [Real.div_rpow hW_sum_nn hS.le] at hjensen'
  have hmul : (∑ j ∈ s, W j) ^ gamma α / S ^ (gamma α - 1) ≤
      ∑ j ∈ s, (Z_alpha (W j) (N j) α) ^ gamma α := by
    have h1' := mul_le_mul_of_nonneg_right hjensen' hS.le
    change ((∑ j ∈ s, W j) ^ gamma α / S ^ gamma α) * S ≤
        ((∑ j ∈ s, (Z_alpha (W j) (N j) α) ^ gamma α) / S) * S at h1'
    rw [div_mul_cancel₀ _ hS.ne'] at h1'
    have hdenom : (∑ j ∈ s, W j) ^ gamma α / S ^ gamma α * S =
        (∑ j ∈ s, W j) ^ gamma α / S ^ (gamma α - 1) := by
      dsimp only [S]
      rw [Real.rpow_sub hS, Real.rpow_one]
      have hS_pow : (∑ j ∈ s, N j) ^ gamma α ≠ 0 := (Real.rpow_pos_of_pos hS _).ne'
      field_simp [hS.ne', hS_pow]
    linarith
  have hrpow := Real.rpow_le_rpow (by positivity) hmul (one_div_pos.mpr hgpos).le
  have hlhs_rpow : ((∑ j ∈ s, W j) ^ gamma α / S ^ (gamma α - 1)) ^ (1 / gamma α) =
      (∑ j ∈ s, W j) / S ^ α := by
    rw [Real.div_rpow (Real.rpow_nonneg hW_sum_nn _) (Real.rpow_pos_of_pos hS _).le]
    rw [← Real.rpow_mul hW_sum_nn, ← Real.rpow_mul hS.le]
    rw [mul_one_div_cancel hgpos.ne', Real.rpow_one, mul_one_div, gamma_sub_one_div_gamma h1.ne]
  rwa [hlhs_rpow] at hrpow

theorem radon_equality_iff {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (W N : ι → ℝ) {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (hW : ∀ j ∈ s, 0 ≤ W j) (hN : ∀ j ∈ s, 0 < N j) :
    (∑ j ∈ s, (Z_alpha (W j) (N j) α) ^ gamma α) ^ (1 / gamma α) =
      (∑ j ∈ s, W j) / (∑ j ∈ s, N j) ^ α ↔
    ∀ j ∈ s, ∀ k ∈ s, W j / N j = W k / N k := by
  have hgpos : 0 < gamma α := gamma_pos h1
  have hg_gt : 1 < gamma α := one_lt_gamma h0 h1
  have hS : 0 < ∑ j ∈ s, N j := Finset.sum_pos hN hs
  let S := ∑ j ∈ s, N j
  let p : ι → ℝ := fun j => N j / S
  let r : ι → ℝ := fun j => W j / N j
  have hp_pos : ∀ j ∈ s, 0 < p j := fun j hj => div_pos (hN j hj) hS
  have hp_sum : ∑ j ∈ s, p j = 1 := by
    dsimp only [p]
    rw [← Finset.sum_div]
    exact div_self hS.ne'
  have hr_mem : ∀ j ∈ s, r j ∈ Ici (0 : ℝ) := fun j hj => div_nonneg (hW j hj) (hN j hj).le
  have hlhs_sum : ∑ j ∈ s, p j • r j = (∑ j ∈ s, W j) / S := by
    simp only [p, r, smul_eq_mul]
    have hterm : ∀ j ∈ s, (N j / S) * (W j / N j) = W j / S := by
      intro j hj; field_simp [(hN j hj).ne', hS.ne']
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  have hrhs_sum : ∑ j ∈ s, p j • (r j ^ gamma α) =
      (∑ j ∈ s, (Z_alpha (W j) (N j) α) ^ gamma α) / S := by
    simp only [p, r, smul_eq_mul, Z_alpha]
    have hterm : ∀ j ∈ s, (N j / S) * (W j / N j) ^ gamma α =
        (W j / N j ^ α) ^ gamma α / S := by
      intro j hj
      rw [Real.div_rpow (hW j hj) (hN j hj).le,
          Real.div_rpow (hW j hj) (Real.rpow_pos_of_pos (hN j hj) _).le,
          ← Real.rpow_mul (hN j hj).le, alpha_mul_gamma h1.ne]
      have hNj : N j ^ (gamma α - 1) = N j ^ gamma α / N j := by
        rw [Real.rpow_sub (hN j hj), Real.rpow_one]
      rw [hNj]
      have h1' : N j ^ gamma α ≠ 0 := (Real.rpow_pos_of_pos (hN j hj) _).ne'
      field_simp [(hN j hj).ne', hS.ne', h1']
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  have hW_sum_nn : 0 ≤ ∑ j ∈ s, W j := Finset.sum_nonneg hW
  have hZ_sum_nn : 0 ≤ ∑ j ∈ s, (Z_alpha (W j) (N j) α) ^ gamma α :=
    Finset.sum_nonneg fun j hj => Real.rpow_nonneg (div_nonneg (hW j hj) (Real.rpow_pos_of_pos (hN j hj) _).le) _
  have hrpow_eq_iff :
      (∑ j ∈ s, (Z_alpha (W j) (N j) α) ^ gamma α) ^ (1 / gamma α) =
        (∑ j ∈ s, W j) / S ^ α ↔
      (∑ j ∈ s, p j • r j) ^ gamma α = ∑ j ∈ s, p j • (r j ^ gamma α) := by
    rw [hlhs_sum, hrhs_sum]
    have hsub : ((∑ j ∈ s, W j) / S ^ α) =
        ((∑ j ∈ s, W j) ^ gamma α / S ^ (gamma α - 1)) ^ (1 / gamma α) := by
      rw [Real.div_rpow (Real.rpow_nonneg hW_sum_nn _) (Real.rpow_pos_of_pos hS _).le]
      rw [← Real.rpow_mul hW_sum_nn, ← Real.rpow_mul hS.le]
      rw [mul_one_div_cancel hgpos.ne', Real.rpow_one, mul_one_div, gamma_sub_one_div_gamma h1.ne]
    rw [hsub, Real.rpow_left_inj hZ_sum_nn (by positivity) (one_div_pos.mpr hgpos).ne']
    have hpow_sub : S ^ (gamma α - 1) = S ^ gamma α / S := by
      rw [Real.rpow_sub hS, Real.rpow_one]
    rw [Real.div_rpow hW_sum_nn hS.le, hpow_sub]
    have hS_pow : S ^ gamma α ≠ 0 := (Real.rpow_pos_of_pos hS _).ne'
    have hSne : S ≠ 0 := hS.ne'
    change (∑ j ∈ s, (Z_alpha (W j) (N j) α) ^ gamma α) =
        (∑ j ∈ s, W j) ^ gamma α / (S ^ gamma α / S) ↔
        (∑ j ∈ s, W j) ^ gamma α / S ^ gamma α =
        (∑ j ∈ s, (Z_alpha (W j) (N j) α) ^ gamma α) / S
    constructor <;> intro h
    · rw [h]; field_simp [hSne, hS_pow]
    · have h' := congrArg (· * S) h
      dsimp only at h'
      rw [div_mul_cancel₀ _ hSne] at h'
      rw [← h']
      field_simp [hSne, hS_pow]
  rw [hrpow_eq_iff, (strictConvexOn_rpow hg_gt).map_sum_eq_iff hp_pos hp_sum hr_mem]
  constructor
  · intro h j hj k hk
    change r j = r k
    rw [h j hj, h k hk]
  · intro h j hj
    have hr_eq : ∀ i ∈ s, r i = r j := fun i hi => h i hi j hj
    calc r j = 1 * r j := (one_mul _).symm
      _ = (∑ i ∈ s, p i) * r j := by rw [hp_sum]
      _ = ∑ i ∈ s, p i * r j := Finset.sum_mul _ _ _
      _ = ∑ i ∈ s, p i • r i := Finset.sum_congr rfl fun i hi => by
          rw [smul_eq_mul, hr_eq i hi]

private lemma twoway_nonneg_eq_radon {W_pos PA W_pitch BF α : ℝ}
    (hWp : 0 ≤ W_pos) (hWq : 0 ≤ W_pitch) (hPA : 0 < PA) (hBF : 0 < BF) (h1 : α < 1) :
    Z_twoway W_pos PA W_pitch BF α =
      (∑ j : Fin 2, (Z_alpha (![W_pos, W_pitch] j) (![PA, BF] j) α) ^ gamma α) ^ (1 / gamma α) := by
  have hg : 0 < gamma α := gamma_pos h1
  have hZ1 : 0 ≤ Z_alpha W_pos PA α := by unfold Z_alpha; positivity
  have hZ2 : 0 ≤ Z_alpha W_pitch BF α := by unfold Z_alpha; positivity
  have hI : I_twoway W_pos PA W_pitch BF α =
      (Z_alpha W_pos PA α) ^ gamma α + (Z_alpha W_pitch BF α) ^ gamma α := by
    unfold I_twoway
    rw [twoway_I_alt_form hPA h1, twoway_I_alt_form hBF h1,
        signedPow_nonneg hZ1 hg, signedPow_nonneg hZ2 hg]
  have hInn : 0 ≤ I_twoway W_pos PA W_pitch BF α := by rw [hI]; positivity
  unfold Z_twoway
  rw [signedPow_nonneg hInn (one_div_pos.mpr hg), hI, Fin.sum_univ_two]
  simp

theorem twoway_ge_zpool_all_alpha {W_pos PA W_pitch BF α : ℝ}
    (hWp : 0 ≤ W_pos) (hWq : 0 ≤ W_pitch) (hPA : 0 < PA) (hBF : 0 < BF)
    (h0 : 0 ≤ α) (h1 : α < 1) :
    Z_twoway W_pos PA W_pitch BF α ≥ Z_pool W_pos PA W_pitch BF α := by
  rw [twoway_nonneg_eq_radon hWp hWq hPA hBF h1]
  have hrad := radon_inequality Finset.univ Finset.univ_nonempty ![W_pos, W_pitch] ![PA, BF] h0 h1
    (fun j _ => by fin_cases j <;> simpa) (fun j _ => by fin_cases j <;> simpa)
  have hpool : (∑ j : Fin 2, ![W_pos, W_pitch] j) / (∑ j : Fin 2, ![PA, BF] j) ^ α =
      Z_pool W_pos PA W_pitch BF α := by
    simp [Z_pool, Fin.sum_univ_two]
  rwa [hpool] at hrad

theorem twoway_eq_zpool_iff {W_pos PA W_pitch BF α : ℝ}
    (hWp : 0 ≤ W_pos) (hWq : 0 ≤ W_pitch) (hPA : 0 < PA) (hBF : 0 < BF)
    (h0 : 0 < α) (h1 : α < 1) :
    Z_twoway W_pos PA W_pitch BF α = Z_pool W_pos PA W_pitch BF α ↔
      W_pos / PA = W_pitch / BF := by
  rw [twoway_nonneg_eq_radon hWp hWq hPA hBF h1]
  have hpool : Z_pool W_pos PA W_pitch BF α =
      (∑ j : Fin 2, ![W_pos, W_pitch] j) / (∑ j : Fin 2, ![PA, BF] j) ^ α := by
    simp [Z_pool, Fin.sum_univ_two]
  rw [hpool, radon_equality_iff Finset.univ Finset.univ_nonempty ![W_pos, W_pitch] ![PA, BF] h0 h1
    (fun j _ => by fin_cases j <;> simpa) (fun j _ => by fin_cases j <;> simpa)]
  constructor
  · intro h
    simpa using h 0 (Finset.mem_univ _) 1 (Finset.mem_univ _)
  · intro h j _ k _
    fin_cases j <;> fin_cases k <;> simp [h]

theorem power_mean_season_bound {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (w : ι → ℝ) {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (hw : ∀ j ∈ s, 0 ≤ w j) :
    (∑ j ∈ s, w j ^ gamma α) ^ (1 / gamma α) ≥ (s.card : ℝ) ^ (1 / gamma α - 1) * (∑ j ∈ s, w j) ∧
    (s.card : ℝ) ^ (1 / gamma α - 1) * (∑ j ∈ s, w j) = (∑ j ∈ s, w j) / (s.card : ℝ) ^ α := by
  have hcard_pos : (0 : ℝ) < s.card := Nat.cast_pos.mpr hs.card_pos
  have hrad := radon_inequality s hs w (fun _ => 1) h0 h1 hw (fun _ _ => zero_lt_one)
  have hlhs : (∑ j ∈ s, (Z_alpha (w j) 1 α) ^ gamma α) ^ (1 / gamma α) =
      (∑ j ∈ s, w j ^ gamma α) ^ (1 / gamma α) := by
    simp [Z_alpha]
  have hrhs : (∑ j ∈ s, w j) / (∑ _ ∈ s, (1 : ℝ)) ^ α = (∑ j ∈ s, w j) / (s.card : ℝ) ^ α := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have heq : (s.card : ℝ) ^ (1 / gamma α - 1) * (∑ j ∈ s, w j) =
      (∑ j ∈ s, w j) / (s.card : ℝ) ^ α := by
    rw [one_div_gamma, show (1 - α) - 1 = -α by ring, Real.rpow_neg hcard_pos.le]
    ring
  rw [hlhs, hrhs] at hrad
  exact ⟨by linarith, heq⟩

theorem power_mean_season_eq_iff {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (w : ι → ℝ) {α : ℝ} (h0 : 0 < α) (h1 : α < 1) (hw : ∀ j ∈ s, 0 ≤ w j) :
    (∑ j ∈ s, w j ^ gamma α) ^ (1 / gamma α) = (∑ j ∈ s, w j) / (s.card : ℝ) ^ α ↔
      ∀ j ∈ s, ∀ k ∈ s, w j = w k := by
  have hrad := radon_equality_iff s hs w (fun _ => 1) h0 h1 hw (fun _ _ => zero_lt_one)
  have hlhs : (∑ j ∈ s, (Z_alpha (w j) 1 α) ^ gamma α) ^ (1 / gamma α) =
      (∑ j ∈ s, w j ^ gamma α) ^ (1 / gamma α) := by
    simp [Z_alpha]
  have hrhs : (∑ j ∈ s, w j) / (∑ _ ∈ s, (1 : ℝ)) ^ α = (∑ j ∈ s, w j) / (s.card : ℝ) ^ α := by
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [hlhs, hrhs] at hrad
  simpa only [div_one] using hrad

/-- Appendix E (`app:radon`): strict monotonicity of the two-coordinate `ℓ_p` norm on
positive inputs: for `0 < Z₁, Z₂` and `0 < p < q`, `‖(Z₁, Z₂)‖_q < ‖(Z₁, Z₂)‖_p`. -/
theorem lp_two_strictAnti {Z₁ Z₂ p q : ℝ}
    (hZ₁ : 0 < Z₁) (hZ₂ : 0 < Z₂) (hp : 0 < p) (hpq : p < q) :
    (Z₁ ^ q + Z₂ ^ q) ^ (1 / q) < (Z₁ ^ p + Z₂ ^ p) ^ (1 / p) := by
  have hq : 0 < q := hp.trans hpq
  set M := (Z₁ ^ q + Z₂ ^ q) ^ (1 / q)
  have hM_pos : 0 < M := by positivity
  have hMq : M ^ q = Z₁ ^ q + Z₂ ^ q := by
    dsimp [M]
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hq.ne', Real.rpow_one]
  have hZ1_lt_M : Z₁ < M := by
    have hpow : Z₁ ^ q < M ^ q := by
      rw [hMq]
      linarith [Real.rpow_pos_of_pos hZ₂ q]
    exact (Real.rpow_lt_rpow_iff hZ₁.le hM_pos.le hq).mp hpow
  have hZ2_lt_M : Z₂ < M := by
    have hpow : Z₂ ^ q < M ^ q := by
      rw [hMq]
      linarith [Real.rpow_pos_of_pos hZ₁ q]
    exact (Real.rpow_lt_rpow_iff hZ₂.le hM_pos.le hq).mp hpow
  have hu1_pos : 0 < Z₁ / M := div_pos hZ₁ hM_pos
  have hu1_lt : Z₁ / M < 1 := (div_lt_one hM_pos).mpr hZ1_lt_M
  have hu2_pos : 0 < Z₂ / M := div_pos hZ₂ hM_pos
  have hu2_lt : Z₂ / M < 1 := (div_lt_one hM_pos).mpr hZ2_lt_M
  have h1 : (Z₁ / M) ^ q < (Z₁ / M) ^ p :=
    Real.rpow_lt_rpow_of_exponent_gt hu1_pos hu1_lt hpq
  have h2 : (Z₂ / M) ^ q < (Z₂ / M) ^ p :=
    Real.rpow_lt_rpow_of_exponent_gt hu2_pos hu2_lt hpq
  have hsum1 : (Z₁ / M) ^ q + (Z₂ / M) ^ q = 1 := by
    rw [Real.div_rpow hZ₁.le hM_pos.le, Real.div_rpow hZ₂.le hM_pos.le, ← add_div, hMq,
        div_self (by positivity)]
  have hsum2 : (Z₁ / M) ^ p + (Z₂ / M) ^ p = (Z₁ ^ p + Z₂ ^ p) / M ^ p := by
    rw [Real.div_rpow hZ₁.le hM_pos.le, Real.div_rpow hZ₂.le hM_pos.le, add_div]
  have hMp_pos : 0 < M ^ p := Real.rpow_pos_of_pos hM_pos p
  have hMp_lt : M ^ p < Z₁ ^ p + Z₂ ^ p := by
    have hlt : 1 < (Z₁ ^ p + Z₂ ^ p) / M ^ p := by linarith
    exact (one_lt_div hMp_pos).mp hlt
  have hrpow := Real.rpow_lt_rpow (by positivity) hMp_lt (one_div_pos.mpr hp)
  rwa [← Real.rpow_mul hM_pos.le, mul_one_div_cancel hp.ne', Real.rpow_one] at hrpow

/-- Appendix E (`app:radon`): for `α < 1/2` (so `0 < γ < 2`, including `α ∈ [0, 1/2)`)
and positive coordinates, Euclidean quadrature is strictly smaller than the `ℓ_γ` combination `Z_{α,2D}`. -/
theorem quadrature_lt_twoway_below_half {W₁ N₁ W₂ N₂ α : ℝ}
    (hhalf : α < 1 / 2)
    (hW₁ : 0 < W₁) (hW₂ : 0 < W₂) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) :
    Real.sqrt (Z_alpha W₁ N₁ α ^ 2 + Z_alpha W₂ N₂ α ^ 2) < Z_twoway W₁ N₁ W₂ N₂ α := by
  have h1 : α < 1 := by linarith
  have hg_pos : 0 < gamma α := gamma_pos h1
  have hg_lt_two : gamma α < 2 := by
    unfold gamma
    rw [div_lt_iff₀ (sub_pos.mpr h1)]
    linarith
  have hZ₁ : 0 < Z_alpha W₁ N₁ α := by unfold Z_alpha; positivity
  have hZ₂ : 0 < Z_alpha W₂ N₂ α := by unfold Z_alpha; positivity
  have hsqrt : Real.sqrt (Z_alpha W₁ N₁ α ^ 2 + Z_alpha W₂ N₂ α ^ 2) =
      (Z_alpha W₁ N₁ α ^ (2 : ℝ) + Z_alpha W₂ N₂ α ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_two, Real.rpow_two]
  have htw : Z_twoway W₁ N₁ W₂ N₂ α =
      (Z_alpha W₁ N₁ α ^ gamma α + Z_alpha W₂ N₂ α ^ gamma α) ^ (1 / gamma α) := by
    rw [twoway_nonneg_eq_radon hW₁.le hW₂.le hN₁ hN₂ h1, Fin.sum_univ_two]
    simp
  rw [hsqrt, htw]
  exact lp_two_strictAnti hZ₁ hZ₂ hg_pos hg_lt_two

/-- Appendix E (`app:radon`): when rates match (`W₁/N₁ = W₂/N₂ > 0`) and `α ∈ [0, 1/2)`,
Euclidean quadrature scores strictly *below* pooled exposure `Z_pool`. -/
theorem quadrature_lt_zpool_equal_rates {W₁ N₁ W₂ N₂ α : ℝ}
    (h0 : 0 ≤ α) (hhalf : α < 1 / 2)
    (hW₁ : 0 < W₁) (hW₂ : 0 < W₂) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (hrate : W₁ / N₁ = W₂ / N₂) :
    Real.sqrt (Z_alpha W₁ N₁ α ^ 2 + Z_alpha W₂ N₂ α ^ 2) < Z_pool W₁ N₁ W₂ N₂ α := by
  have hlt := quadrature_lt_twoway_below_half hhalf hW₁ hW₂ hN₁ hN₂
  rcases eq_or_lt_of_le h0 with rfl | hpos
  · have htw0 : Z_twoway W₁ N₁ W₂ N₂ 0 = Z_pool W₁ N₁ W₂ N₂ 0 := by
      rw [twoway_alpha_zero]
      simp [Z_pool]
    rwa [htw0] at hlt
  · have heq := (twoway_eq_zpool_iff hW₁.le hW₂.le hN₁ hN₂ hpos (by linarith)).mpr hrate
    rwa [heq] at hlt

/-- Appendix E (`app:radon`): at `α = 0`, Euclidean quadrature is strictly smaller than
total WAR `W₁ + W₂` whenever both coordinates are positive. -/
theorem quadrature_lt_total_war_alpha_zero {W₁ W₂ : ℝ} (hW₁ : 0 < W₁) (hW₂ : 0 < W₂) :
    Real.sqrt (W₁ ^ 2 + W₂ ^ 2) < W₁ + W₂ := by
  have hsq : W₁ ^ 2 + W₂ ^ 2 < (W₁ + W₂) ^ 2 := by nlinarith
  have hlt := Real.sqrt_lt_sqrt (by positivity) hsq
  rwa [Real.sqrt_sq (add_pos hW₁ hW₂).le] at hlt

/-! ## Section 9: Proposition 6 (`prop:null`, Threshold Against a Null Rate) -/

theorem prop_null_hasDerivAt {W : ℝ → ℝ} {r_marg N r₀ α : ℝ}
    (hW : HasDerivAt W r_marg N) (hN : 0 < N) :
    HasDerivAt (fun n => Z_null (W n) n r₀ α)
      (N ^ (-α) * ((r_marg - r₀) - α * (W N / N - r₀))) N := by
  unfold Z_null
  have hnum : HasDerivAt (fun n => W n - r₀ * n) (r_marg - r₀) N := by
    simpa using hW.sub ((hasDerivAt_const N r₀).mul (hasDerivAt_id N))
  have hpow : HasDerivAt (fun n : ℝ => n ^ α) (α * N ^ (α - 1)) N := by
    simpa using Real.hasDerivAt_rpow_const (Or.inl hN.ne')
  have hdiv := hnum.div hpow (Real.rpow_pos_of_pos hN α).ne'
  convert hdiv using 1
  have hNne : N ≠ 0 := hN.ne'
  have hp1 : N ^ α ≠ 0 := (Real.rpow_pos_of_pos hN α).ne'
  have hpow_sub : N ^ (α - 1) = N ^ α / N := by rw [Real.rpow_sub hN, Real.rpow_one]
  have hpow_neg : N ^ (-α) = (N ^ α)⁻¹ := Real.rpow_neg hN.le α
  rw [hpow_sub, hpow_neg]
  field_simp [hNne, hp1]

theorem prop_null_iff {r_marg r_bar r₀ N α : ℝ} (hN : 0 < N) :
    N ^ (-α) * ((r_marg - r₀) - α * (r_bar - r₀)) > 0 ↔
      r_marg > (1 - α) * r₀ + α * r_bar := by
  have hpos : 0 < N ^ (-α) := Real.rpow_pos_of_pos hN (-α)
  rw [gt_iff_lt, gt_iff_lt, mul_pos_iff_of_pos_left hpos]
  constructor <;> intro h <;> linarith

theorem prop_null_alpha_eff {r_bar r₀ α : ℝ} (hr : r_bar ≠ 0) :
    ((1 - α) * r₀ + α * r_bar) / r_bar = α + (1 - α) * (r₀ / r_bar) := by
  field_simp [hr]
  ring

/-! ## Section 10: Remark (`rem:interp`, Measure-Theoretic Gaussian KL Divergence) -/

/-- Exact KL divergence between two normal distributions `N(m₁, v)` and `N(m₂, v)`
with common nonzero variance `v` via `InformationTheory.klDiv` and `gaussianReal`. -/
theorem klDiv_gaussianReal_same_var (m₁ m₂ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    InformationTheory.klDiv (gaussianReal m₁ v) (gaussianReal m₂ v) =
      ENNReal.ofReal ((m₁ - m₂) ^ 2 / (2 * (v : ℝ))) := by
  let μ : Measure ℝ := gaussianReal m₁ v
  let ν : Measure ℝ := gaussianReal m₂ v
  have hv_pos : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hμ_vol : μ ≪ volume := gaussianReal_absolutelyContinuous m₁ hv
  have hvol_ν : volume ≪ ν := gaussianReal_absolutelyContinuous' m₂ hv
  have hμν : μ ≪ ν := hμ_vol.trans hvol_ν
  have h_rn_right :
      μ.rnDeriv (volume.withDensity (gaussianPDF m₂ v)) =ᵐ[volume]
        fun x => (gaussianPDF m₂ v x)⁻¹ * μ.rnDeriv volume x :=
    Measure.rnDeriv_withDensity_right μ volume (measurable_gaussianPDF m₂ v).aemeasurable
      (ae_of_all _ fun x => (gaussianPDF_pos m₂ hv x).ne')
      (ae_of_all _ fun _ => gaussianPDF_ne_top)
  have h_rn_left : μ.rnDeriv volume =ᵐ[volume] gaussianPDF m₁ v :=
    rnDeriv_gaussianReal m₁ v
  have h_rn : μ.rnDeriv ν =ᵐ[μ] fun x => (gaussianPDF m₂ v x)⁻¹ * gaussianPDF m₁ v x := by
    refine hμ_vol.ae_le ?_
    rw [show ν = volume.withDensity (gaussianPDF m₂ v) from gaussianReal_of_var_ne_zero m₂ hv]
    filter_upwards [h_rn_right, h_rn_left] with x hx1 hx2
    rw [hx1, hx2]
  have h_llr :
      llr μ ν =ᵐ[μ]
        fun x => ((m₁ - m₂) / (v : ℝ)) * x - (m₁ ^ 2 - m₂ ^ 2) / (2 * (v : ℝ)) := by
    filter_upwards [h_rn] with x hx
    change Real.log (μ.rnDeriv ν x).toReal = _
    rw [hx]
    have hpdf2_pos : 0 < gaussianPDFReal m₂ v x := gaussianPDFReal_pos m₂ v x hv
    have hpdf2_ne_top : (gaussianPDF m₂ v x)⁻¹ ≠ ⊤ := by
      rw [ENNReal.inv_ne_top]
      exact (gaussianPDF_pos m₂ hv x).ne'
    have htoReal :
        ((gaussianPDF m₂ v x)⁻¹ * gaussianPDF m₁ v x).toReal =
          gaussianPDFReal m₁ v x / gaussianPDFReal m₂ v x := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_inv, toReal_gaussianPDF, toReal_gaussianPDF,
          inv_mul_eq_div]
    rw [htoReal]
    have hnorm_ne : (√(2 * π * (v : ℝ)))⁻¹ ≠ 0 := inv_ne_zero (by positivity)
    have hratio :
        gaussianPDFReal m₁ v x / gaussianPDFReal m₂ v x =
          Real.exp (-(x - m₁) ^ 2 / (2 * (v : ℝ)) - -(x - m₂) ^ 2 / (2 * (v : ℝ))) := by
      rw [gaussianPDFReal_def, gaussianPDFReal_def, mul_div_mul_left _ _ hnorm_ne,
          ← Real.exp_sub]
    rw [hratio, Real.log_exp]
    field_simp [hv_pos.ne']
    ring
  have hid : Integrable (fun x : ℝ => x) μ := (memLp_id_gaussianReal (μ := m₁) (v := v) 1).integrable le_rfl
  have h_aff_int :
      Integrable (fun x => ((m₁ - m₂) / (v : ℝ)) * x - (m₁ ^ 2 - m₂ ^ 2) / (2 * (v : ℝ))) μ :=
    (hid.const_mul _).sub (integrable_const _)
  have h_int : Integrable (llr μ ν) μ := h_aff_int.congr h_llr.symm
  have h_integral :
      ∫ x, llr μ ν x ∂μ = (m₁ - m₂) ^ 2 / (2 * (v : ℝ)) := by
    rw [integral_congr_ae h_llr, integral_sub (hid.const_mul _) (integrable_const _),
        integral_const_mul, integral_const, integral_id_gaussianReal]
    have hμ_univ : μ.real univ = 1 := by simp [Measure.real]
    rw [hμ_univ, smul_eq_mul, one_mul]
    field_simp [hv_pos.ne']
    ring
  rw [InformationTheory.klDiv_of_ac_of_integrable hμν h_int, h_integral]
  have hμ_univ : μ.real univ = 1 := by simp [Measure.real]
  have hν_univ : ν.real univ = 1 := by simp [Measure.real]
  rw [hμ_univ, hν_univ]
  ring_nf

/-- Remark (`rem:interp`): for `P = N(W/N, σ²/N)` and `P₀ = N(0, σ²/N)`,
`D_KL(P ‖ P₀) = W² / (2σ²N)` genuinely as `InformationTheory.klDiv` on `gaussianReal`,
and `Z_{1/2} = sgn(W) * σ * √(2 * D_KL(P ‖ P₀))`. -/
theorem kl_gaussian_zwar {W N σ : ℝ} (hN : 0 < N) (hσ : 0 < σ) :
    let v : ℝ≥0 := ⟨σ ^ 2 / N, by positivity⟩
    InformationTheory.klDiv (gaussianReal (W / N) v) (gaussianReal 0 v) =
      ENNReal.ofReal (W ^ 2 / (2 * σ ^ 2 * N)) ∧
    Real.sign W * σ * Real.sqrt
        (2 * (InformationTheory.klDiv (gaussianReal (W / N) v) (gaussianReal 0 v)).toReal) =
      Z_alpha W N (1 / 2) := by
  intro v
  have hv_pos : (0 : ℝ) < (v : ℝ) := by dsimp [v]; positivity
  have hv_ne : v ≠ 0 := NNReal.coe_ne_zero.mp hv_pos.ne'
  have hkl : InformationTheory.klDiv (gaussianReal (W / N) v) (gaussianReal 0 v) =
      ENNReal.ofReal (W ^ 2 / (2 * σ ^ 2 * N)) := by
    rw [klDiv_gaussianReal_same_var (W / N) 0 v hv_ne]
    congr 1
    dsimp [v]
    field_simp [hN.ne', hσ.ne']
    ring
  refine ⟨hkl, ?_⟩
  rw [hkl, ENNReal.toReal_ofReal (by positivity)]
  have h2D : 2 * (W ^ 2 / (2 * σ ^ 2 * N)) = W ^ 2 / (σ ^ 2 * N) := by
    field_simp [hσ.ne', hN.ne']
  rw [h2D, Real.sqrt_div (sq_nonneg W), Real.sqrt_sq_eq_abs, Real.sqrt_mul (sq_nonneg σ),
      Real.sqrt_sq hσ.le, Real.sqrt_eq_rpow]
  have h1 : σ * (|W| / (σ * N ^ (1 / 2 : ℝ))) = |W| / N ^ (1 / 2 : ℝ) := by
    field_simp [hσ.ne']
  calc Real.sign W * σ * (|W| / (σ * N ^ (1 / 2 : ℝ)))
      = Real.sign W * (σ * (|W| / (σ * N ^ (1 / 2 : ℝ)))) := by ring
    _ = Real.sign W * (|W| / N ^ (1 / 2 : ℝ)) := by rw [h1]
    _ = (Real.sign W * |W|) / N ^ (1 / 2 : ℝ) := by ring
    _ = W / N ^ (1 / 2 : ℝ) := by rw [real_sign_mul_abs]
    _ = Z_alpha W N (1 / 2) := rfl

/-- Appendix B (`app:twoway`): with `σ² = 1` and `α = 1/2`, the per-coordinate
contribution `I_{1/2,k}` equals `sgn(W_k) * 2 * D_KL(N(W_k/N_k, 1/N_k) ‖ N(0, 1/N_k))`. -/
theorem kl_I_twoway_coord_eq {W N : ℝ} (hN : 0 < N) :
    let v : ℝ≥0 := ⟨1 / N, by positivity⟩
    signedPow W (gamma (1 / 2)) / N ^ (gamma (1 / 2) - 1) =
      Real.sign W * 2 *
        (InformationTheory.klDiv (gaussianReal (W / N) v) (gaussianReal 0 v)).toReal := by
  intro v
  have hv_pos : (0 : ℝ) < (v : ℝ) := by dsimp [v]; positivity
  have hv_ne : v ≠ 0 := NNReal.coe_ne_zero.mp hv_pos.ne'
  have hkl : (InformationTheory.klDiv (gaussianReal (W / N) v) (gaussianReal 0 v)).toReal =
      W ^ 2 / (2 * N) := by
    rw [klDiv_gaussianReal_same_var (W / N) 0 v hv_ne, ENNReal.toReal_ofReal (by positivity)]
    dsimp [v]
    field_simp [hN.ne']
    ring
  have hg : gamma (1 / 2 : ℝ) = 2 := by unfold gamma; norm_num
  rw [hkl, hg, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
  unfold signedPow
  rw [Real.rpow_two, sq_abs]
  field_simp [hN.ne']

/-! ## Section 11: Definition 1 Continuity, Monotonicity, and Regularity Trichotomy (Appendix B) -/

theorem signedPow_continuous {p : ℝ} (hp : 0 < p) :
    Continuous (fun x : ℝ => signedPow x p) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hev : (fun t => signedPow t p) =ᶠ[𝓝 x] fun t => -((-t) ^ p) :=
      Filter.eventually_of_mem (Iio_mem_nhds hx) fun t ht => signedPow_neg ht
    refine ContinuousAt.congr_of_eventuallyEq ?_ hev
    exact ((continuous_neg.continuousAt.rpow_const
      (Or.inl (neg_pos.mpr hx).ne')).neg)
  · have hbound : ∀ t : ℝ, ‖signedPow t p‖ ≤ |t| ^ p := by
      intro t
      unfold signedPow
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) p)]
      have hs : |Real.sign t| ≤ 1 := by
        rcases lt_trichotomy t 0 with ht | rfl | ht
        · simp [Real.sign_of_neg ht]
        · simp [Real.sign_zero]
        · simp [Real.sign_of_pos ht]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (abs_nonneg t) p) hs
    have htend : Tendsto (fun t : ℝ => |t| ^ p) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun t : ℝ => |t| ^ p) :=
        continuous_abs.rpow_const (fun _ => Or.inr hp.le)
      simpa [Real.zero_rpow hp.ne'] using (hc.continuousAt (x := 0)).tendsto
    have hzero : Tendsto (fun t : ℝ => signedPow t p) (𝓝 0) (𝓝 0) :=
      squeeze_zero_norm hbound htend
    simpa [ContinuousAt, signedPow_zero_left hp] using hzero
  · have hev : (fun t => signedPow t p) =ᶠ[𝓝 x] fun t => t ^ p :=
      Filter.eventually_of_mem (Ioi_mem_nhds hx) fun t ht => signedPow_nonneg ht.le hp
    refine ContinuousAt.congr_of_eventuallyEq ?_ hev
    exact continuous_id.continuousAt.rpow_const (Or.inl hx.ne')

theorem Z_twoway_continuous {PA BF α : ℝ} (h1 : α < 1) :
    Continuous (fun w : ℝ × ℝ => Z_twoway w.1 PA w.2 BF α) := by
  unfold Z_twoway I_twoway
  have hg : 0 < gamma α := gamma_pos h1
  have hinv : 0 < 1 / gamma α := one_div_pos.mpr hg
  have hI : Continuous (fun w : ℝ × ℝ =>
      signedPow w.1 (gamma α) / PA ^ (gamma α - 1) +
        signedPow w.2 (gamma α) / BF ^ (gamma α - 1)) := by
    refine ((signedPow_continuous hg).comp continuous_fst).div_const _ |>.add
      (((signedPow_continuous hg).comp continuous_snd).div_const _)
  exact (signedPow_continuous hinv).comp hI

theorem signedPow_strictMono {p : ℝ} (hp : 0 < p) : StrictMono (fun x : ℝ => signedPow x p) := by
  intro a b hab
  dsimp only
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rcases lt_trichotomy b 0 with hb | rfl | hb
    · rw [signedPow_neg ha, signedPow_neg hb, neg_lt_neg_iff]
      exact Real.rpow_lt_rpow (by linarith) (by linarith) hp
    · rw [signedPow_neg ha, signedPow_zero_left hp, neg_lt_zero]
      exact Real.rpow_pos_of_pos (by linarith) p
    · rw [signedPow_neg ha, signedPow_nonneg hb.le hp]
      have h1 : 0 < (-a) ^ p := Real.rpow_pos_of_pos (by linarith) p
      have h2 : 0 < b ^ p := Real.rpow_pos_of_pos hb p
      linarith
  · rw [signedPow_zero_left hp, signedPow_nonneg hab.le hp]
    exact Real.rpow_pos_of_pos hab p
  · rw [signedPow_nonneg ha.le hp, signedPow_nonneg (ha.trans hab).le hp]
    exact Real.rpow_lt_rpow ha.le hab hp

theorem Z_twoway_strictMono_left {PA BF α : ℝ} (hPA : 0 < PA) (hα : α < 1) (W_pitch : ℝ) :
    StrictMono (fun W_pos => Z_twoway W_pos PA W_pitch BF α) := by
  intro a b hab
  have hg : 0 < gamma α := gamma_pos hα
  have hinv : 0 < 1 / gamma α := one_div_pos.mpr hg
  apply signedPow_strictMono hinv
  unfold I_twoway
  gcongr
  exact signedPow_strictMono hg hab

theorem Z_twoway_strictMono_right {PA BF α : ℝ} (hBF : 0 < BF) (hα : α < 1) (W_pos : ℝ) :
    StrictMono (fun W_pitch => Z_twoway W_pos PA W_pitch BF α) := by
  intro a b hab
  have hg : 0 < gamma α := gamma_pos hα
  have hinv : 0 < 1 / gamma α := one_div_pos.mpr hg
  apply signedPow_strictMono hinv
  unfold I_twoway
  gcongr
  exact signedPow_strictMono hg hab

theorem Z_twoway_neg_secondary_strictMono_exposure {W₁ N₁ W₂ N₂ N₂' α : ℝ}
    (h0 : 0 < α) (h1 : α < 1) (hW₂ : W₂ < 0) (hN₂ : 0 < N₂) (hNlt : N₂ < N₂') :
    Z_twoway W₁ N₁ W₂ N₂ α < Z_twoway W₁ N₁ W₂ N₂' α := by
  have hg : 0 < gamma α := gamma_pos h1
  have hg_sub : 0 < gamma α - 1 := by linarith [one_lt_gamma h0 h1]
  have hinv : 0 < 1 / gamma α := one_div_pos.mpr hg
  apply signedPow_strictMono hinv
  unfold I_twoway
  rw [add_lt_add_iff_left, signedPow_neg hW₂, neg_div, neg_div, neg_lt_neg_iff]
  have hnum : 0 < (-W₂) ^ gamma α := Real.rpow_pos_of_pos (neg_pos.mpr hW₂) _
  have hden1 : 0 < N₂ ^ (gamma α - 1) := Real.rpow_pos_of_pos hN₂ _
  have hden2 : N₂ ^ (gamma α - 1) < N₂' ^ (gamma α - 1) :=
    Real.rpow_lt_rpow hN₂.le hNlt hg_sub
  exact div_lt_div_of_pos_left hnum hden1 hden2

/-- `signedPow t p` is `C¹` on `ℝ` for every `p > 1`, with derivative `p * |x|^(p - 1)`. -/
theorem signedPow_hasDerivAt {p : ℝ} (hp : 1 < p) (x : ℝ) :
    HasDerivAt (fun t : ℝ => signedPow t p) (p * |x| ^ (p - 1)) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hev : (fun t => signedPow t p) =ᶠ[𝓝 x] fun t => -((-t) ^ p) :=
      Filter.eventually_of_mem (Iio_mem_nhds hx) fun t ht => signedPow_neg ht
    have hcomp : HasDerivAt (fun t : ℝ => -((-t) ^ p)) (-(p * (-x) ^ (p - 1) * (-1))) x := by
      have hd1 : HasDerivAt (fun t : ℝ => -t) (-1) x := by simpa using (hasDerivAt_id x).neg
      have hd2 : HasDerivAt (fun u : ℝ => u ^ p) (p * (-x) ^ (p - 1)) (-x) :=
        Real.hasDerivAt_rpow_const (Or.inr hp.le)
      exact (hd2.comp x hd1).neg
    have heq : -(p * (-x) ^ (p - 1) * (-1)) = p * |x| ^ (p - 1) := by
      rw [abs_of_neg hx]; ring
    rw [heq] at hcomp
    exact hcomp.congr_of_eventuallyEq hev
  · rw [hasDerivAt_iff_tendsto_slope_zero]
    have hp_pos : 0 < p := by linarith
    have hp1_pos : 0 < p - 1 := sub_pos.mpr hp
    have hev : (fun t : ℝ => t⁻¹ • (signedPow (0 + t) p - signedPow 0 p)) =ᶠ[𝓝[≠] 0]
        fun t => |t| ^ (p - 1) := by
      refine eventually_nhdsWithin_of_forall fun t ht => ?_
      rw [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
      dsimp only
      rw [zero_add, signedPow_zero_left hp_pos, sub_zero, smul_eq_mul]
      rcases lt_or_gt_of_ne ht with ht_neg | ht_pos
      · rw [signedPow_neg ht_neg, abs_of_neg ht_neg]
        have hmt : 0 < -t := neg_pos.mpr ht_neg
        calc t⁻¹ * -((-t) ^ p)
            = (-t)⁻¹ * (-t) ^ p := by ring
          _ = (-t) ^ (-1 : ℝ) * (-t) ^ p := by rw [← Real.rpow_neg_one (-t)]
          _ = (-t) ^ (p - 1) := by rw [← Real.rpow_add hmt, add_comm, ← sub_eq_add_neg]
      · rw [signedPow_nonneg ht_pos.le hp_pos, abs_of_pos ht_pos]
        calc t⁻¹ * t ^ p
            = t ^ (-1 : ℝ) * t ^ p := by rw [← Real.rpow_neg_one t]
          _ = t ^ (p - 1) := by rw [← Real.rpow_add ht_pos, add_comm, ← sub_eq_add_neg]
    have htend : Tendsto (fun t : ℝ => |t| ^ (p - 1)) (𝓝[≠] 0) (𝓝 (p * |0| ^ (p - 1))) := by
      have hc : Continuous (fun t : ℝ => |t| ^ (p - 1)) :=
        continuous_abs.rpow_const (fun _ => Or.inr hp1_pos.le)
      have h0 : p * |0| ^ (p - 1) = 0 := by simp [Real.zero_rpow hp1_pos.ne']
      simpa [h0, Real.zero_rpow hp1_pos.ne'] using
        (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    exact htend.congr' hev.symm
  · have hev : (fun t => signedPow t p) =ᶠ[𝓝 x] fun t => t ^ p :=
      Filter.eventually_of_mem (Ioi_mem_nhds hx) fun t ht => signedPow_nonneg ht.le (by linarith)
    have hd : HasDerivAt (fun t : ℝ => t ^ p) (p * |x| ^ (p - 1)) x := by
      simpa [abs_of_pos hx] using Real.hasDerivAt_rpow_const (p := p) (Or.inl hx.ne')
    exact hd.congr_of_eventuallyEq hev

theorem signedPow_contDiff_one {p : ℝ} (hp : 1 < p) :
    ContDiff ℝ 1 (fun t : ℝ => signedPow t p) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (signedPow_hasDerivAt hp x).differentiableAt, ?_⟩
  have hderiv : deriv (fun t : ℝ => signedPow t p) = fun x => p * |x| ^ (p - 1) := by
    ext x; exact (signedPow_hasDerivAt hp x).deriv
  rw [hderiv]
  exact continuous_const.mul (continuous_abs.rpow_const (fun _ => Or.inr (sub_nonneg.mpr hp.le)))

/-- Appendix B regularity trichotomy (part 1): for `1 < p ≤ 2` (i.e., `α ∈ (0, 1/2]`),
the derivative `x ↦ p * |x|^(p - 1)` is NOT differentiable at `x = 0`
(jump discontinuity in the second derivative at `p = 2` / `α = 1/2`; divergence as `x → 0`
for `1 < p < 2` / `α < 1/2`). -/
theorem signedPow_deriv_not_differentiableAt_zero_of_le_two {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ¬ DifferentiableAt ℝ (fun x : ℝ => p * |x| ^ (p - 1)) 0 := by
  intro hd
  have htend := hd.hasDerivAt.tendsto_slope
  set y := deriv (fun x : ℝ => p * |x| ^ (p - 1)) 0
  have hp1_pos : (0 : ℝ) < p - 1 := sub_pos.mpr hp1
  have hsl_pos : ∀ t : ℝ, 0 < t →
      slope (fun x : ℝ => p * |x| ^ (p - 1)) 0 t = p * t ^ (p - 2) := by
    intro t ht
    rw [slope, sub_zero, vsub_eq_sub, abs_zero, Real.zero_rpow hp1_pos.ne', mul_zero, sub_zero,
        smul_eq_mul, abs_of_pos ht]
    calc t⁻¹ * (p * t ^ (p - 1))
        = p * (t ^ (-1 : ℝ) * t ^ (p - 1)) := by rw [← Real.rpow_neg_one t]; ring
      _ = p * t ^ (p - 2) := by
          rw [← Real.rpow_add ht, show (-1 : ℝ) + (p - 1) = p - 2 by ring]
  have hsl_neg : ∀ t : ℝ, t < 0 →
      slope (fun x : ℝ => p * |x| ^ (p - 1)) 0 t = -p * (-t) ^ (p - 2) := by
    intro t ht
    have hmt : 0 < -t := neg_pos.mpr ht
    rw [slope, sub_zero, vsub_eq_sub, abs_zero, Real.zero_rpow hp1_pos.ne', mul_zero, sub_zero,
        smul_eq_mul, abs_of_neg ht]
    calc t⁻¹ * (p * (-t) ^ (p - 1))
        = -p * ((-t) ^ (-1 : ℝ) * (-t) ^ (p - 1)) := by
            rw [show t⁻¹ = -(-t)⁻¹ by rw [inv_neg, neg_neg], ← Real.rpow_neg_one (-t)]; ring
      _ = -p * (-t) ^ (p - 2) := by
          rw [← Real.rpow_add hmt, show (-1 : ℝ) + (p - 1) = p - 2 by ring]
  rcases lt_or_eq_of_le hp2 with hlt | rfl
  · have hgt_tend : Tendsto (fun t : ℝ => t ^ (-(2 - p))) (𝓝[>] 0) (𝓝 (y / p)) := by
      have hp_ne : p ≠ 0 := (by linarith : (0 : ℝ) < p).ne'
      have hscale : Tendsto (fun t : ℝ => p⁻¹ * slope (fun x : ℝ => p * |x| ^ (p - 1)) 0 t)
          (𝓝[≠] 0) (𝓝 (p⁻¹ * y)) := (htend.const_mul p⁻¹)
      have hgt : Tendsto (fun t : ℝ => p⁻¹ * slope (fun x : ℝ => p * |x| ^ (p - 1)) 0 t)
          (𝓝[>] 0) (𝓝 (p⁻¹ * y)) :=
        hscale.mono_left (nhdsWithin_mono 0 fun t ht => (lt_of_lt_of_le ht le_rfl).ne')
      have hev : (fun t : ℝ => p⁻¹ * slope (fun x : ℝ => p * |x| ^ (p - 1)) 0 t) =ᶠ[𝓝[>] 0]
          fun t => t ^ (-(2 - p)) := by
        refine eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => ?_
        dsimp only
        rw [hsl_pos t ht, show p⁻¹ * (p * t ^ (p - 2)) = t ^ (p - 2) by field_simp [hp_ne]]
        congr 1; ring
      simpa [div_eq_inv_mul] using hgt.congr' hev
    exact not_tendsto_nhds_of_tendsto_atTop
      (tendsto_rpow_neg_nhdsGT_zero (by linarith : -(2 - p) < 0)) (y / p) hgt_tend
  · have hpos_lim : y = 2 := by
      have hgt := htend.mono_left (nhdsWithin_mono 0 fun t (ht : 0 < t) => ht.ne')
      have hev : slope (fun x : ℝ => 2 * |x| ^ (2 - 1 : ℝ)) 0 =ᶠ[𝓝[>] 0] fun _ => (2 : ℝ) := by
        refine eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => ?_
        rw [hsl_pos t ht, sub_self, Real.rpow_zero, mul_one]
      have h2 : Tendsto (fun _ : ℝ => (2 : ℝ)) (𝓝[>] 0) (𝓝 y) := hgt.congr' hev
      exact tendsto_nhds_unique h2 tendsto_const_nhds
    have hneg_lim : y = -2 := by
      have hlt_w := htend.mono_left (nhdsWithin_mono 0 fun t (ht : t < 0) => ht.ne)
      have hev : slope (fun x : ℝ => 2 * |x| ^ (2 - 1 : ℝ)) 0 =ᶠ[𝓝[<] 0] fun _ => (-2 : ℝ) := by
        refine eventually_nhdsWithin_of_forall fun t (ht : t < 0) => ?_
        rw [hsl_neg t ht, sub_self, Real.rpow_zero, mul_one]
      have hm2 : Tendsto (fun _ : ℝ => (-2 : ℝ)) (𝓝[<] 0) (𝓝 y) := hlt_w.congr' hev
      exact tendsto_nhds_unique hm2 tendsto_const_nhds
    linarith

/-- Appendix B regularity trichotomy (part 2): for `p > 2` (i.e., `α ∈ (1/2, 1)`),
the derivative `x ↦ p * |x|^(p - 1)` IS everywhere continuously differentiable (`C²` overall)
with second derivative `p * (p - 1) * signedPow x (p - 2)`, which equals `0` at `x = 0`. -/
theorem signedPow_deriv_hasDerivAt_of_two_lt {p : ℝ} (hp : 2 < p) (x : ℝ) :
    HasDerivAt (fun t : ℝ => p * |t| ^ (p - 1)) (p * (p - 1) * signedPow x (p - 2)) x := by
  have hp_pos : (0 : ℝ) < p := by linarith
  have hp1_pos : (0 : ℝ) < p - 1 := by linarith
  have hp2_pos : (0 : ℝ) < p - 2 := by linarith
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hev : (fun t : ℝ => p * |t| ^ (p - 1)) =ᶠ[𝓝 x] fun t => p * (-t) ^ (p - 1) :=
      Filter.eventually_of_mem (Iio_mem_nhds hx) fun t ht => by dsimp only; rw [abs_of_neg ht]
    have hd1 : HasDerivAt (fun t : ℝ => -t) (-1) x := by simpa using (hasDerivAt_id x).neg
    have hd2 : HasDerivAt (fun u : ℝ => u ^ (p - 1)) ((p - 1) * (-x) ^ (p - 1 - 1)) (-x) :=
      Real.hasDerivAt_rpow_const (Or.inl (neg_pos.mpr hx).ne')
    have hcomp := (hd2.comp x hd1).const_mul p
    have heq : p * ((p - 1) * (-x) ^ (p - 1 - 1) * (-1)) =
        p * (p - 1) * signedPow x (p - 2) := by
      rw [signedPow_neg hx, show p - 1 - 1 = p - 2 by ring]
      ring
    rw [heq] at hcomp
    exact hcomp.congr_of_eventuallyEq hev
  · rw [hasDerivAt_iff_tendsto_slope_zero, signedPow_zero_left hp2_pos, mul_zero]
    have hnorm : ∀ t : ℝ, t ≠ 0 →
        ‖t⁻¹ • (p * |0 + t| ^ (p - 1) - p * |0| ^ (p - 1))‖ ≤ p * |t| ^ (p - 2) := by
      intro t ht
      rw [zero_add, abs_zero, Real.zero_rpow hp1_pos.ne', mul_zero, sub_zero, smul_eq_mul,
          Real.norm_eq_abs, abs_mul, abs_inv, abs_mul, abs_of_pos hp_pos,
          abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _)]
      have hpos : 0 < |t| := abs_pos.mpr ht
      have hpow : |t|⁻¹ * (p * |t| ^ (p - 1)) = p * |t| ^ (p - 2) := by
        calc |t|⁻¹ * (p * |t| ^ (p - 1))
            = p * (|t| ^ (p - 1) / |t| ^ (1 : ℝ)) := by rw [Real.rpow_one]; ring
          _ = p * |t| ^ (p - 2) := by rw [← Real.rpow_sub hpos, show p - 1 - 1 = p - 2 by ring]
      exact hpow.le
    have htend : Tendsto (fun t : ℝ => p * |t| ^ (p - 2)) (𝓝[≠] 0) (𝓝 0) := by
      have hc : Continuous (fun t : ℝ => p * |t| ^ (p - 2)) :=
        continuous_const.mul (continuous_abs.rpow_const (fun _ => Or.inr hp2_pos.le))
      simpa [Real.zero_rpow hp2_pos.ne'] using
        (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htend
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_
    refine eventually_nhdsWithin_of_forall fun t ht => ?_
    exact hnorm t (by simpa using ht)
  · have hev : (fun t : ℝ => p * |t| ^ (p - 1)) =ᶠ[𝓝 x] fun t => p * t ^ (p - 1) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hx) fun t ht => by dsimp only; rw [abs_of_pos ht]
    have hd : HasDerivAt (fun t : ℝ => t ^ (p - 1)) ((p - 1) * x ^ (p - 1 - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hx.ne')
    have hcomp := hd.const_mul p
    have heq : p * ((p - 1) * x ^ (p - 1 - 1)) = p * (p - 1) * signedPow x (p - 2) := by
      rw [signedPow_nonneg hx.le hp2_pos, show p - 1 - 1 = p - 2 by ring]
      ring
    rw [heq] at hcomp
    exact hcomp.congr_of_eventuallyEq hev

theorem signedPow_contDiff_two_of_two_lt {p : ℝ} (hp : 2 < p) :
    ContDiff ℝ 2 (fun t : ℝ => signedPow t p) := by
  have hp1 : 1 < p := by linarith
  have hp2 : 0 < p - 2 := by linarith
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  simp only [WithTop.one_ne_top, IsEmpty.forall_iff, true_and]
  refine ⟨fun x => (signedPow_hasDerivAt hp1 x).differentiableAt, ?_⟩
  have hderiv : deriv (fun t : ℝ => signedPow t p) = fun x => p * |x| ^ (p - 1) := by
    ext x; exact (signedPow_hasDerivAt hp1 x).deriv
  rw [hderiv, contDiff_one_iff_deriv]
  refine ⟨fun x => (signedPow_deriv_hasDerivAt_of_two_lt hp x).differentiableAt, ?_⟩
  have hderiv2 : deriv (fun x : ℝ => p * |x| ^ (p - 1)) =
      fun x => p * (p - 1) * signedPow x (p - 2) := by
    ext x; exact (signedPow_deriv_hasDerivAt_of_two_lt hp x).deriv
  rw [hderiv2]
  exact continuous_const.mul (signedPow_continuous hp2)

private lemma signedPow_hasDerivAt_of_ne_zero {u p : ℝ} (hu : u ≠ 0) (hp : 0 < p) :
    HasDerivAt (fun t : ℝ => signedPow t p) (p * |u| ^ (p - 1)) u := by
  rcases lt_or_gt_of_ne hu with hneg | hpos
  · have hev : (fun t => signedPow t p) =ᶠ[𝓝 u] fun t => -((-t) ^ p) :=
      Filter.eventually_of_mem (Iio_mem_nhds hneg) fun t ht => signedPow_neg ht
    have hd1 : HasDerivAt (fun t : ℝ => -t) (-1) u := by simpa using (hasDerivAt_id u).neg
    have hd2 : HasDerivAt (fun t : ℝ => t ^ p) (p * (-u) ^ (p - 1)) (-u) :=
      Real.hasDerivAt_rpow_const (Or.inl (neg_pos.mpr hneg).ne')
    have hc := (hd2.comp u hd1).neg
    have heq : -(p * (-u) ^ (p - 1) * (-1)) = p * |u| ^ (p - 1) := by
      rw [abs_of_neg hneg]; ring
    rw [heq] at hc
    exact hc.congr_of_eventuallyEq hev
  · have hev : (fun t => signedPow t p) =ᶠ[𝓝 u] fun t => t ^ p :=
      Filter.eventually_of_mem (Ioi_mem_nhds hpos) fun t ht => signedPow_nonneg ht.le hp
    have hd : HasDerivAt (fun t : ℝ => t ^ p) (p * |u| ^ (p - 1)) u := by
      refine (Real.hasDerivAt_rpow_const (p := p) (Or.inl hpos.ne')).congr_deriv ?_
      rw [abs_of_pos hpos]
    exact hd.congr_of_eventuallyEq hev

/-- Partial derivative of `Z_{α,2D}` with respect to `W_pos` away from `I_twoway = 0`:
`∂Z_{α,2D}/∂W_pos = (|W_pos| / PA)^(γ - 1) * |Z_{α,2D}|^(1 - γ)`. -/
theorem Z_twoway_hasDerivAt_W1 {W_pos PA W_pitch BF α : ℝ}
    (h0 : 0 < α) (h1 : α < 1) (hPA : 0 < PA)
    (hI : I_twoway W_pos PA W_pitch BF α ≠ 0) :
    HasDerivAt (fun w => Z_twoway w PA W_pitch BF α)
      ((|W_pos| / PA) ^ (gamma α - 1) * |Z_twoway W_pos PA W_pitch BF α| ^ (1 - gamma α))
      W_pos := by
  have hg1 : 1 < gamma α := one_lt_gamma h0 h1
  have hg_pos : 0 < gamma α := by linarith
  let I := I_twoway W_pos PA W_pitch BF α
  have hI_deriv : HasDerivAt (fun w => I_twoway w PA W_pitch BF α)
      (gamma α * |W_pos| ^ (gamma α - 1) / PA ^ (gamma α - 1)) W_pos := by
    unfold I_twoway
    exact ((signedPow_hasDerivAt hg1 W_pos).div_const _).add_const _
  have hpow_outer :
      HasDerivAt (fun u : ℝ => signedPow u (1 / gamma α))
        ((1 / gamma α) * |I| ^ (1 / gamma α - 1)) I :=
    signedPow_hasDerivAt_of_ne_zero hI (one_div_pos.mpr hg_pos)
  have hcomp := hpow_outer.comp W_pos hI_deriv
  change HasDerivAt (fun w => Z_twoway w PA W_pitch BF α) _ W_pos at hcomp
  convert hcomp using 1
  have habs_Z : |Z_twoway W_pos PA W_pitch BF α| = |I| ^ (1 / gamma α) := by
    unfold Z_twoway
    change |Real.sign I * |I| ^ (1 / gamma α)| = |I| ^ (1 / gamma α)
    have hIabs : 0 ≤ |I| := abs_nonneg I
    have hs : |Real.sign I| = 1 := by
      rcases lt_or_gt_of_ne hI with hIneg | hIpos
      · rw [Real.sign_of_neg hIneg]; norm_num
      · rw [Real.sign_of_pos hIpos]; norm_num
    rw [abs_mul, hs, one_mul, abs_of_nonneg (Real.rpow_nonneg hIabs _)]
  rw [habs_Z, ← Real.rpow_mul (abs_nonneg I), Real.div_rpow (abs_nonneg W_pos) hPA.le]
  have hexp : (1 / gamma α) * (1 - gamma α) = 1 / gamma α - 1 := by
    field_simp [hg_pos.ne']
  rw [hexp]
  field_simp [hg_pos.ne']

/-- Appendix B (`app:twoway`): symmetric partial derivative of `Z_{α,2D}` with respect
to `W_pitch` away from the cancellation locus `I_twoway = 0`. -/
theorem Z_twoway_hasDerivAt_W2 {W_pos PA W_pitch BF α : ℝ}
    (h0 : 0 < α) (h1 : α < 1) (hBF : 0 < BF)
    (hI : I_twoway W_pos PA W_pitch BF α ≠ 0) :
    HasDerivAt (fun w => Z_twoway W_pos PA w BF α)
      ((|W_pitch| / BF) ^ (gamma α - 1) * |Z_twoway W_pos PA W_pitch BF α| ^ (1 - gamma α))
      W_pitch := by
  have hcomm_I : I_twoway W_pitch BF W_pos PA α = I_twoway W_pos PA W_pitch BF α := by
    unfold I_twoway; exact add_comm _ _
  have hI' : I_twoway W_pitch BF W_pos PA α ≠ 0 := by rwa [hcomm_I]
  have hd := Z_twoway_hasDerivAt_W1 h0 h1 hBF hI'
  have hcomm_fun : (fun w => Z_twoway W_pos PA w BF α) = (fun w => Z_twoway w BF W_pos PA α) := by
    ext w; unfold Z_twoway I_twoway; rw [add_comm]
  rw [hcomm_fun]
  simpa only [show Z_twoway W_pitch BF W_pos PA α = Z_twoway W_pos PA W_pitch BF α by
    unfold Z_twoway I_twoway; rw [add_comm]] using hd

/-- Helper for Appendix B: `signedPow · p` is smooth (`C^n` for any `n`) away from `0`. -/
theorem signedPow_contDiffAt_of_ne_zero {p x : ℝ} {n : WithTop ℕ∞} (hx : x ≠ 0) :
    ContDiffAt ℝ n (fun u : ℝ => signedPow u p) x := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hev : (fun u : ℝ => signedPow u p) =ᶠ[𝓝 x] fun u => -((-u) ^ p) :=
      Filter.eventually_of_mem (Iio_mem_nhds hneg) fun u hu => signedPow_neg hu
    have hcd : ContDiffAt ℝ n (fun u : ℝ => -((-u) ^ p)) x :=
      ((Real.contDiffAt_rpow_const_of_ne (neg_pos.mpr hneg).ne').comp x contDiffAt_id.neg).neg
    exact hcd.congr_of_eventuallyEq hev
  · have hev : (fun u : ℝ => signedPow u p) =ᶠ[𝓝 x] fun u => u ^ p := by
      refine Filter.eventually_of_mem (Ioi_mem_nhds hpos) fun u hu => ?_
      dsimp only
      unfold signedPow
      rw [Real.sign_of_pos hu, one_mul, abs_of_pos hu]
    exact (Real.contDiffAt_rpow_const_of_ne hpos.ne').congr_of_eventuallyEq hev

/-- Appendix B (`app:twoway`): for `α ∈ (0, 1)`, `Z_{α,2D}` is jointly `C^1` on `ℝ²`
away from the cancellation locus `I_twoway = 0`. -/
theorem Z_twoway_contDiffAt_one {W_pos PA W_pitch BF α : ℝ}
    (h0 : 0 < α) (h1 : α < 1) (hI : I_twoway W_pos PA W_pitch BF α ≠ 0) :
    ContDiffAt ℝ 1 (fun w : ℝ × ℝ => Z_twoway w.1 PA w.2 BF α) (W_pos, W_pitch) := by
  have hg1 : 1 < gamma α := one_lt_gamma h0 h1
  have hI_cd : ContDiff ℝ 1 (fun w : ℝ × ℝ => I_twoway w.1 PA w.2 BF α) := by
    unfold I_twoway
    exact (((signedPow_contDiff_one hg1).comp contDiff_fst).div_const _).add
      (((signedPow_contDiff_one hg1).comp contDiff_snd).div_const _)
  exact (signedPow_contDiffAt_of_ne_zero hI).comp (W_pos, W_pitch) hI_cd.contDiffAt

/-- Appendix B (`app:twoway`): explicit joint Fréchet derivative of `Z_{α,2D}` on `ℝ²`
away from the cancellation locus `I_twoway = 0`. -/
theorem Z_twoway_hasFDerivAt {W_pos PA W_pitch BF α : ℝ}
    (h0 : 0 < α) (h1 : α < 1) (hPA : 0 < PA) (hBF : 0 < BF)
    (hI : I_twoway W_pos PA W_pitch BF α ≠ 0) :
    HasFDerivAt (fun w : ℝ × ℝ => Z_twoway w.1 PA w.2 BF α)
      (((|W_pos| / PA) ^ (gamma α - 1) * |Z_twoway W_pos PA W_pitch BF α| ^ (1 - gamma α)) •
        ContinuousLinearMap.fst ℝ ℝ ℝ +
       ((|W_pitch| / BF) ^ (gamma α - 1) * |Z_twoway W_pos PA W_pitch BF α| ^ (1 - gamma α)) •
        ContinuousLinearMap.snd ℝ ℝ ℝ)
      (W_pos, W_pitch) := by
  have hg1 : 1 < gamma α := one_lt_gamma h0 h1
  have hg_pos : 0 < gamma α := by linarith
  let I := I_twoway W_pos PA W_pitch BF α
  have hI1 : HasFDerivAt (fun w : ℝ × ℝ => signedPow w.1 (gamma α) / PA ^ (gamma α - 1))
      ((gamma α * |W_pos| ^ (gamma α - 1) / PA ^ (gamma α - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ)
      (W_pos, W_pitch) := by
    simpa [Function.comp_def] using
      ((signedPow_hasDerivAt hg1 W_pos).div_const (PA ^ (gamma α - 1))).comp_hasFDerivAt
        (W_pos, W_pitch) (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (W_pos, W_pitch)))
  have hI2 : HasFDerivAt (fun w : ℝ × ℝ => signedPow w.2 (gamma α) / BF ^ (gamma α - 1))
      ((gamma α * |W_pitch| ^ (gamma α - 1) / BF ^ (gamma α - 1)) • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (W_pos, W_pitch) := by
    simpa [Function.comp_def] using
      ((signedPow_hasDerivAt hg1 W_pitch).div_const (BF ^ (gamma α - 1))).comp_hasFDerivAt
        (W_pos, W_pitch) (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (W_pos, W_pitch)))
  have hI_fd : HasFDerivAt (fun w : ℝ × ℝ => I_twoway w.1 PA w.2 BF α)
      ((gamma α * |W_pos| ^ (gamma α - 1) / PA ^ (gamma α - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
       (gamma α * |W_pitch| ^ (gamma α - 1) / BF ^ (gamma α - 1)) • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (W_pos, W_pitch) := hI1.add hI2
  have houter : HasDerivAt (fun u : ℝ => signedPow u (1 / gamma α))
      ((1 / gamma α) * |I| ^ (1 / gamma α - 1)) I :=
    signedPow_hasDerivAt_of_ne_zero hI (one_div_pos.mpr hg_pos)
  have hcomp := houter.comp_hasFDerivAt (W_pos, W_pitch) hI_fd
  change HasFDerivAt (fun w : ℝ × ℝ => Z_twoway w.1 PA w.2 BF α) _ (W_pos, W_pitch) at hcomp
  convert hcomp using 1
  have habs_Z : |Z_twoway W_pos PA W_pitch BF α| = |I| ^ (1 / gamma α) := by
    unfold Z_twoway
    change |Real.sign I * |I| ^ (1 / gamma α)| = |I| ^ (1 / gamma α)
    have hIabs : 0 ≤ |I| := abs_nonneg I
    have hs : |Real.sign I| = 1 := by
      rcases lt_or_gt_of_ne hI with hIneg | hIpos
      · rw [Real.sign_of_neg hIneg]; norm_num
      · rw [Real.sign_of_pos hIpos]; norm_num
    rw [abs_mul, hs, one_mul, abs_of_nonneg (Real.rpow_nonneg hIabs _)]
  have hexp : (1 / gamma α) * (1 - gamma α) = 1 / gamma α - 1 := by field_simp [hg_pos.ne']
  rw [habs_Z, ← Real.rpow_mul (abs_nonneg I), hexp,
      Real.div_rpow (abs_nonneg W_pos) hPA.le, Real.div_rpow (abs_nonneg W_pitch) hBF.le]
  ext <;> simp <;> field_simp [hg_pos.ne']

/-- Appendix B (`app:twoway`): for `α ∈ (1/2, 1)` (where `γ > 2`), `Z_{α,2D}` is jointly
`C^2` on `ℝ²` away from the cancellation locus `I_twoway = 0`. -/
theorem Z_twoway_contDiffAt_two {W_pos PA W_pitch BF α : ℝ}
    (hhalf : 1 / 2 < α) (h1 : α < 1) (hI : I_twoway W_pos PA W_pitch BF α ≠ 0) :
    ContDiffAt ℝ 2 (fun w : ℝ × ℝ => Z_twoway w.1 PA w.2 BF α) (W_pos, W_pitch) := by
  have hg2 : 2 < gamma α := by
    unfold gamma
    rw [lt_div_iff₀ (sub_pos.mpr h1)]
    linarith
  have hI_cd : ContDiff ℝ 2 (fun w : ℝ × ℝ => I_twoway w.1 PA w.2 BF α) := by
    unfold I_twoway
    exact (((signedPow_contDiff_two_of_two_lt hg2).comp contDiff_fst).div_const _).add
      (((signedPow_contDiff_two_of_two_lt hg2).comp contDiff_snd).div_const _)
  exact (signedPow_contDiffAt_of_ne_zero hI).comp (W_pos, W_pitch) hI_cd.contDiffAt

/-- Appendix B (`app:twoway`): at `α = 0`, `Z_{0,2D}` is linear and `C^∞` everywhere. -/
theorem Z_twoway_alpha_zero_contDiff (PA BF : ℝ) :
    ContDiff ℝ ⊤ (fun w : ℝ × ℝ => Z_twoway w.1 PA w.2 BF 0) := by
  have heq : (fun w : ℝ × ℝ => Z_twoway w.1 PA w.2 BF 0) = fun w => w.1 + w.2 := by
    ext w; exact twoway_alpha_zero w.1 PA w.2 BF
  rw [heq]
  exact contDiff_fst.add contDiff_snd

/-- Appendix B (`app:twoway`): for `α ∈ (0, 1/2]` and `W_pitch ≠ 0` (so `I_twoway ≠ 0`),
the first partial derivative of `Z_{α,2D}` in `W_pos` is NOT differentiable at `W_pos = 0`,
and therefore `Z_{α,2D}` is NOT `C^2` at `(0, W_pitch)`. -/
theorem Z_twoway_not_twice_diff_at_W1_zero {PA W_pitch BF α : ℝ}
    (h0 : 0 < α) (hhalf : α ≤ 1 / 2) (hPA : 0 < PA) (hBF : 0 < BF) (hW₂ : W_pitch ≠ 0) :
    ¬ DifferentiableAt ℝ (deriv (fun w => Z_twoway w PA W_pitch BF α)) 0 ∧
    ¬ ContDiffAt ℝ 2 (fun w : ℝ × ℝ => Z_twoway w.1 PA w.2 BF α) (0, W_pitch) := by
  have h1 : α < 1 := by linarith
  have hg1 : 1 < gamma α := one_lt_gamma h0 h1
  have hg_pos : 0 < gamma α := by linarith
  have hg2 : gamma α ≤ 2 := by
    unfold gamma
    rw [div_le_iff₀ (sub_pos.mpr h1)]
    linarith
  let g : ℝ → ℝ := fun w => Z_twoway w PA W_pitch BF α
  have hI0 : I_twoway 0 PA W_pitch BF α ≠ 0 := by
    unfold I_twoway signedPow
    rw [Real.sign_zero, zero_mul, zero_div, zero_add]
    have hBFpow : BF ^ (gamma α - 1) ≠ 0 := (Real.rpow_pos_of_pos hBF _).ne'
    have hs : Real.sign W_pitch ≠ 0 := by
      rcases lt_or_gt_of_ne hW₂ with hneg | hpos
      · rw [Real.sign_of_neg hneg]; norm_num
      · rw [Real.sign_of_pos hpos]; norm_num
    have habs : |W_pitch| ^ gamma α ≠ 0 := (Real.rpow_pos_of_pos (abs_pos.mpr hW₂) _).ne'
    exact div_ne_zero (mul_ne_zero hs habs) hBFpow
  have hI_cont : Continuous (fun w : ℝ => I_twoway w PA W_pitch BF α) := by
    unfold I_twoway
    exact ((signedPow_continuous hg_pos).div_const _).add continuous_const
  have hev_I_ne : ∀ᶠ w in 𝓝 (0 : ℝ), I_twoway w PA W_pitch BF α ≠ 0 :=
    hI_cont.continuousAt.eventually_ne hI0
  have hg_deriv : ∀ᶠ w in 𝓝 (0 : ℝ),
      deriv g w = (|w| / PA) ^ (gamma α - 1) * |g w| ^ (1 - gamma α) := by
    filter_upwards [hev_I_ne] with w hw
    exact (Z_twoway_hasDerivAt_W1 h0 h1 hPA hw).deriv
  have hg0_ne : g 0 ≠ 0 := by
    dsimp [g]; unfold Z_twoway signedPow
    have hs : Real.sign (I_twoway 0 PA W_pitch BF α) ≠ 0 := by
      rcases lt_or_gt_of_ne hI0 with hneg | hpos
      · rw [Real.sign_of_neg hneg]; norm_num
      · rw [Real.sign_of_pos hpos]; norm_num
    exact mul_ne_zero hs (Real.rpow_pos_of_pos (abs_pos.mpr hI0) _).ne'
  have hg_diff0 : DifferentiableAt ℝ g 0 := (Z_twoway_hasDerivAt_W1 h0 h1 hPA hI0).differentiableAt
  let A : ℝ → ℝ := fun w => PA ^ (1 - gamma α) * |g w| ^ (1 - gamma α)
  have hA0_ne : A 0 ≠ 0 := by
    dsimp [A]
    exact mul_ne_zero (Real.rpow_pos_of_pos hPA _).ne'
      (Real.rpow_pos_of_pos (abs_pos.mpr hg0_ne) _).ne'
  have hA_diff : DifferentiableAt ℝ A 0 := by
    have hpow_abs : DifferentiableAt ℝ (fun w => |g w| ^ (1 - gamma α)) 0 := by
      rcases lt_or_gt_of_ne hg0_ne with hneg | hpos
      · have hev : (fun w => |g w| ^ (1 - gamma α)) =ᶠ[𝓝 (0 : ℝ)]
            fun w => (-g w) ^ (1 - gamma α) := by
          filter_upwards [hg_diff0.continuousAt.eventually (Iio_mem_nhds hneg)] with w hw
          rw [abs_of_neg hw]
        have hd : HasDerivAt (fun w => (-g w) ^ (1 - gamma α)) _ 0 :=
          (hg_diff0.hasDerivAt.neg).rpow_const (Or.inl (neg_pos.mpr hneg).ne')
        exact hd.differentiableAt.congr_of_eventuallyEq hev
      · have hev : (fun w => |g w| ^ (1 - gamma α)) =ᶠ[𝓝 (0 : ℝ)]
            fun w => (g w) ^ (1 - gamma α) := by
          filter_upwards [hg_diff0.continuousAt.eventually (Ioi_mem_nhds hpos)] with w hw
          rw [abs_of_pos hw]
        have hd : HasDerivAt (fun w => (g w) ^ (1 - gamma α)) _ 0 :=
          hg_diff0.hasDerivAt.rpow_const (Or.inl hpos.ne')
        exact hd.differentiableAt.congr_of_eventuallyEq hev
    exact hpow_abs.const_mul (PA ^ (1 - gamma α))
  have hnot : ¬ DifferentiableAt ℝ (deriv g) 0 := by
    intro hdiff
    have hquot : DifferentiableAt ℝ (fun w => gamma α * (deriv g w / A w)) 0 :=
      (hdiff.div hA_diff hA0_ne).const_mul (gamma α)
    have hev_eq : (fun w => gamma α * (deriv g w / A w)) =ᶠ[𝓝 (0 : ℝ)]
        fun w => gamma α * |w| ^ (gamma α - 1) := by
      filter_upwards [hg_deriv, hev_I_ne] with w hdg hIw
      have hgw_ne : g w ≠ 0 := by
        dsimp [g]; unfold Z_twoway signedPow
        rcases lt_or_gt_of_ne hIw with hneg | hpos
        · exact mul_ne_zero (by rw [Real.sign_of_neg hneg]; norm_num)
            (Real.rpow_pos_of_pos (abs_pos.mpr hneg.ne) _).ne'
        · exact mul_ne_zero (by rw [Real.sign_of_pos hpos]; norm_num)
            (Real.rpow_pos_of_pos (abs_pos.mpr hpos.ne') _).ne'
      have hAw_ne : A w ≠ 0 := by
        dsimp [A]
        exact mul_ne_zero (Real.rpow_pos_of_pos hPA _).ne'
          (Real.rpow_pos_of_pos (abs_pos.mpr hgw_ne) _).ne'
      have hPA_inv : (PA ^ (gamma α - 1))⁻¹ = PA ^ (1 - gamma α) := by
        rw [← Real.rpow_neg hPA.le]; congr 1; ring
      have hdg' : deriv g w = |w| ^ (gamma α - 1) * A w := by
        rw [hdg, Real.div_rpow (abs_nonneg w) hPA.le, div_eq_mul_inv, hPA_inv]
        dsimp [A]; ring
      rw [hdg', mul_div_cancel_right₀ _ hAw_ne]
    exact signedPow_deriv_not_differentiableAt_zero_of_le_two hg1 hg2
      (hquot.congr_of_eventuallyEq hev_eq.symm)
  refine ⟨hnot, fun hcd => ?_⟩
  have hg2_cd : ContDiffAt ℝ 2 g 0 := hcd.comp 0 (contDiff_prodMk_left W_pitch).contDiffAt
  have hfderiv : DifferentiableAt ℝ (fderiv ℝ g) 0 := hg2_cd.fderiv_right_succ.differentiableAt_one
  have hderiv_diff : DifferentiableAt ℝ (deriv g) 0 := by
    simpa only [← fderiv_deriv] using hfderiv.clm_apply (differentiableAt_const (1 : ℝ))
  exact hnot hderiv_diff

/-- Appendix B (`app:twoway`): symmetric non-`C^2` statement at `W_pitch = 0` when
`W_pos ≠ 0` and `α ∈ (0, 1/2]`. -/
theorem Z_twoway_not_twice_diff_at_W2_zero {W_pos PA BF α : ℝ}
    (h0 : 0 < α) (hhalf : α ≤ 1 / 2) (hPA : 0 < PA) (hBF : 0 < BF) (hW₁ : W_pos ≠ 0) :
    ¬ DifferentiableAt ℝ (deriv (fun w => Z_twoway W_pos PA w BF α)) 0 ∧
    ¬ ContDiffAt ℝ 2 (fun w : ℝ × ℝ => Z_twoway w.1 PA w.2 BF α) (W_pos, 0) := by
  obtain ⟨h1, h2⟩ := Z_twoway_not_twice_diff_at_W1_zero h0 hhalf hBF hPA hW₁
  have hcomm_fun : (fun w => Z_twoway W_pos PA w BF α) = (fun w => Z_twoway w BF W_pos PA α) := by
    ext w; unfold Z_twoway I_twoway; rw [add_comm]
  refine ⟨?_, fun hcd => h2 ?_⟩
  · simpa only [hcomm_fun] using h1
  · have hswap : (fun w : ℝ × ℝ => Z_twoway w.1 BF w.2 PA α) =
        (fun w : ℝ × ℝ => Z_twoway w.2 PA w.1 BF α) := by
      ext w; unfold Z_twoway I_twoway; rw [add_comm]
    rw [hswap]
    exact hcd.comp (0, W_pos) (contDiff_snd.prodMk contDiff_fst).contDiffAt

/-- Appendix B (`app:twoway`): for `α ∈ (0, 1)`, `Z_{α,2D}` is not Fréchet differentiable
at `(0, 0)`. -/
theorem Z_twoway_not_differentiableAt_origin {PA BF α : ℝ}
    (h0 : 0 < α) (h1 : α < 1) (hPA : 0 < PA) (hBF : 0 < BF) :
    ¬ DifferentiableAt ℝ (fun w : ℝ × ℝ => Z_twoway w.1 PA w.2 BF α) (0, 0) := by
  intro hdiff
  set f : ℝ × ℝ → ℝ := fun w => Z_twoway w.1 PA w.2 BF α
  obtain ⟨L, hL⟩ := hdiff
  have hL1 : L (1, 0) = 1 / PA ^ α := by
    have hpath : HasDerivAt (fun t : ℝ => f (t, 0)) (L (1, 0)) 0 := by
      have hp : HasDerivAt (fun t : ℝ => (t, (0 : ℝ))) (1, 0) 0 :=
        (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 (0 : ℝ))
      simpa [Function.comp_def] using hL.comp_hasDerivAt_of_eq 0 hp rfl
    have heq : (fun t : ℝ => f (t, 0)) = fun t : ℝ => (1 / PA ^ α) * t := by
      ext t; dsimp [f]; rw [twoway_single_role_right hPA h1]; unfold Z_alpha; ring
    rw [heq] at hpath
    have hpath2 : HasDerivAt (fun t : ℝ => (1 / PA ^ α) * t) (1 / PA ^ α) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (1 / PA ^ α)
    exact hpath.unique hpath2
  have hL2 : L (0, 1) = 1 / BF ^ α := by
    have hpath : HasDerivAt (fun t : ℝ => f (0, t)) (L (0, 1)) 0 := by
      have hp : HasDerivAt (fun t : ℝ => ((0 : ℝ), t)) (0, 1) 0 :=
        (hasDerivAt_const 0 (0 : ℝ)).prodMk (hasDerivAt_id 0)
      simpa [Function.comp_def] using hL.comp_hasDerivAt_of_eq 0 hp rfl
    have heq : (fun t : ℝ => f (0, t)) = fun t : ℝ => (1 / BF ^ α) * t := by
      ext t; dsimp [f]; rw [twoway_single_role_left hBF h1]; unfold Z_alpha; ring
    rw [heq] at hpath
    have hpath2 : HasDerivAt (fun t : ℝ => (1 / BF ^ α) * t) (1 / BF ^ α) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (1 / BF ^ α)
    exact hpath.unique hpath2
  have hdiag : HasDerivAt (fun t : ℝ => f (t * PA, t * BF)) (L (PA, BF)) 0 := by
    have hp : HasDerivAt (fun t : ℝ => (t * PA, t * BF)) (PA, BF) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const PA).prodMk ((hasDerivAt_id (0 : ℝ)).mul_const BF)
    simpa [Function.comp_def] using hL.comp_hasDerivAt_of_eq 0 hp (by simp)
  have hdiag_eq : (fun t : ℝ => f (t * PA, t * BF)) = fun t : ℝ => (PA + BF) ^ (1 - α) * t := by
    ext t
    dsimp [f]
    have hg : 0 < gamma α := gamma_pos h1
    have hI : I_twoway (t * PA) PA (t * BF) BF α = signedPow t (gamma α) * (PA + BF) := by
      unfold I_twoway
      rw [mul_comm t PA, mul_comm t BF, signedPow_mul_pos hPA, signedPow_mul_pos hBF]
      have hPA_div : PA ^ gamma α / PA ^ (gamma α - 1) = PA := by
        rw [Real.rpow_sub hPA, Real.rpow_one]
        field_simp [(Real.rpow_pos_of_pos hPA _).ne']
      have hBF_div : BF ^ gamma α / BF ^ (gamma α - 1) = BF := by
        rw [Real.rpow_sub hBF, Real.rpow_one]
        field_simp [(Real.rpow_pos_of_pos hBF _).ne']
      calc PA ^ gamma α * signedPow t (gamma α) / PA ^ (gamma α - 1) +
            BF ^ gamma α * signedPow t (gamma α) / BF ^ (gamma α - 1)
          = (PA ^ gamma α / PA ^ (gamma α - 1)) * signedPow t (gamma α) +
            (BF ^ gamma α / BF ^ (gamma α - 1)) * signedPow t (gamma α) := by ring
        _ = signedPow t (gamma α) * (PA + BF) := by rw [hPA_div, hBF_div]; ring
    unfold Z_twoway
    rw [hI, mul_comm (signedPow t (gamma α)) (PA + BF), signedPow_mul_pos (add_pos hPA hBF),
        one_div_gamma]
    have hsp : signedPow (signedPow t (gamma α)) (1 - α) = t := by
      rw [← one_div_gamma]
      rcases lt_trichotomy t 0 with ht | rfl | ht
      · rw [signedPow_neg ht]
        have hneg : -((-t) ^ gamma α) < 0 := by linarith [Real.rpow_pos_of_pos (neg_pos.mpr ht) (gamma α)]
        rw [signedPow_neg hneg, neg_neg, ← Real.rpow_mul (neg_pos.mpr ht).le,
            mul_one_div_cancel hg.ne', Real.rpow_one]
        ring
      · rw [signedPow_zero_left hg, signedPow_zero_left (one_div_pos.mpr hg)]
      · rw [signedPow_nonneg ht.le hg, signedPow_nonneg (Real.rpow_nonneg ht.le _) (one_div_pos.mpr hg),
            ← Real.rpow_mul ht.le, mul_one_div_cancel hg.ne', Real.rpow_one]
    rw [hsp]
  rw [hdiag_eq] at hdiag
  have hdiag2 : HasDerivAt (fun t : ℝ => (PA + BF) ^ (1 - α) * t) ((PA + BF) ^ (1 - α)) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul ((PA + BF) ^ (1 - α))
  have hL_sum : L (PA, BF) = PA ^ (1 - α) + BF ^ (1 - α) := by
    have hvec : (PA, BF) = PA • (1, 0) + BF • (0, 1) := by ext <;> simp
    rw [hvec, map_add, map_smul, map_smul, hL1, hL2, smul_eq_mul, smul_eq_mul]
    have hP : PA * (1 / PA ^ α) = PA ^ (1 - α) := by
      rw [Real.rpow_sub hPA, Real.rpow_one]; ring
    have hB : BF * (1 / BF ^ α) = BF ^ (1 - α) := by
      rw [Real.rpow_sub hBF, Real.rpow_one]; ring
    rw [hP, hB]
  have heq_pows : (PA + BF) ^ (1 - α) = PA ^ (1 - α) + BF ^ (1 - α) := by
    rw [← hL_sum]; exact hdiag2.unique hdiag
  have h1α_pos : 0 < 1 - α := sub_pos.mpr h1
  have h1α_lt : 1 - α < 1 := by linarith
  have hS : 0 < PA + BF := add_pos hPA hBF
  have hr1 : (PA / (PA + BF)) < (PA / (PA + BF)) ^ (1 - α) := by
    have h := Real.rpow_lt_rpow_of_exponent_gt (div_pos hPA hS) ((div_lt_one hS).mpr (by linarith)) h1α_lt
    rwa [Real.rpow_one] at h
  have hr2 : (BF / (PA + BF)) < (BF / (PA + BF)) ^ (1 - α) := by
    have h := Real.rpow_lt_rpow_of_exponent_gt (div_pos hBF hS) ((div_lt_one hS).mpr (by linarith)) h1α_lt
    rwa [Real.rpow_one] at h
  rw [Real.div_rpow hPA.le hS.le] at hr1
  rw [Real.div_rpow hBF.le hS.le] at hr2
  have hsum : 1 < (PA ^ (1 - α) + BF ^ (1 - α)) / (PA + BF) ^ (1 - α) := by
    calc 1 = PA / (PA + BF) + BF / (PA + BF) := by field_simp [hS.ne']
      _ < PA ^ (1 - α) / (PA + BF) ^ (1 - α) + BF ^ (1 - α) / (PA + BF) ^ (1 - α) :=
          add_lt_add hr1 hr2
      _ = (PA ^ (1 - α) + BF ^ (1 - α)) / (PA + BF) ^ (1 - α) := by ring
  rw [← heq_pows, div_self (Real.rpow_pos_of_pos hS _).ne'] at hsum
  linarith

/-- Appendix B (`app:twoway`): for `α ∈ (0, 1)`, `Z_{α,2D}` is NOT differentiable anywhere
on the cancellation locus `I_twoway = 0`. -/
theorem Z_twoway_not_differentiableAt_cancellation {W_pos PA W_pitch BF α : ℝ}
    (h0 : 0 < α) (h1 : α < 1) (hPA : 0 < PA) (hBF : 0 < BF)
    (hI : I_twoway W_pos PA W_pitch BF α = 0) :
    ¬ DifferentiableAt ℝ (fun w : ℝ × ℝ => Z_twoway w.1 PA w.2 BF α) (W_pos, W_pitch) := by
  have hg1 : 1 < gamma α := one_lt_gamma h0 h1
  have hg_pos : 0 < gamma α := by linarith
  by_cases hW₁ : W_pos = 0
  · subst hW₁
    have hW₂ : W_pitch = 0 := by
      unfold I_twoway signedPow at hI
      rw [Real.sign_zero, zero_mul, zero_div, zero_add] at hI
      by_contra hne
      have hBFpow : BF ^ (gamma α - 1) ≠ 0 := (Real.rpow_pos_of_pos hBF _).ne'
      have hs : Real.sign W_pitch ≠ 0 := by
        rcases lt_or_gt_of_ne hne with hneg | hpos
        · rw [Real.sign_of_neg hneg]; norm_num
        · rw [Real.sign_of_pos hpos]; norm_num
      have hnonzero : Real.sign W_pitch * |W_pitch| ^ gamma α / BF ^ (gamma α - 1) ≠ 0 :=
        div_ne_zero (mul_ne_zero hs (Real.rpow_pos_of_pos (abs_pos.mpr hne) _).ne') hBFpow
      exact hnonzero hI
    subst hW₂
    exact Z_twoway_not_differentiableAt_origin h0 h1 hPA hBF
  · intro hdiff
    let f : ℝ → ℝ := fun t => Z_twoway (W_pos + t) PA W_pitch BF α
    let I : ℝ → ℝ := fun t => I_twoway (W_pos + t) PA W_pitch BF α
    have hf_diff : DifferentiableAt ℝ f 0 := by
      have hp : DifferentiableAt ℝ (fun t : ℝ => (W_pos + t, W_pitch)) 0 :=
        ((differentiableAt_const W_pos).add differentiableAt_id).prodMk (differentiableAt_const W_pitch)
      have hdiff' : DifferentiableAt ℝ (fun w : ℝ × ℝ => Z_twoway w.1 PA w.2 BF α)
          ((fun t : ℝ => (W_pos + t, W_pitch)) 0) := by
        simpa using hdiff
      exact hdiff'.comp 0 hp
    have hf_tend := hf_diff.hasDerivAt.tendsto_slope
    have hf_gt : Tendsto (slope f 0) (𝓝[>] 0) (𝓝 (deriv f 0)) :=
      hf_tend.mono_left (nhdsWithin_mono 0 fun _ ht => (lt_of_lt_of_le ht le_rfl).ne')
    let c : ℝ := gamma α * |W_pos| ^ (gamma α - 1) / PA ^ (gamma α - 1)
    have hc_pos : 0 < c := by
      dsimp [c]
      exact div_pos (mul_pos hg_pos (Real.rpow_pos_of_pos (abs_pos.mpr hW₁) _))
        (Real.rpow_pos_of_pos hPA _)
    have hI_deriv : HasDerivAt I c 0 := by
      have hd1 : HasDerivAt (fun t : ℝ => W_pos + t) 1 0 := by
        simpa using (hasDerivAt_const (0 : ℝ) W_pos).add (hasDerivAt_id (0 : ℝ))
      have hd2 : HasDerivAt (fun w => I_twoway w PA W_pitch BF α) c (W_pos + 0) := by
        rw [add_zero]; unfold I_twoway; exact ((signedPow_hasDerivAt hg1 W_pos).div_const _).add_const _
      simpa [I] using hd2.comp 0 hd1
    have hI_slope : Tendsto (fun t : ℝ => I t / t) (𝓝[>] 0) (𝓝 c) := by
      have h0_eq : I 0 = 0 := by dsimp [I]; rw [add_zero]; exact hI
      have hts := hI_deriv.tendsto_slope_zero.mono_left
        (nhdsWithin_mono 0 fun _ ht => (lt_of_lt_of_le ht le_rfl).ne')
      refine hts.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      rw [zero_add, h0_eq, sub_zero, smul_eq_mul, div_eq_inv_mul]
    have hev_I_half : ∀ᶠ t in 𝓝[>] (0 : ℝ), c / 2 < I t / t :=
      hI_slope.eventually (Ioi_mem_nhds (by linarith))
    have hslope_atTop : Tendsto (slope f 0) (𝓝[>] 0) atTop := by
      have ht_atTop : Tendsto (fun t : ℝ => (c / 2) ^ (1 - α) * t ^ (-α)) (𝓝[>] 0) atTop :=
        (tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.mpr h0)).const_mul_atTop (by positivity)
      refine tendsto_atTop_mono' (𝓝[>] 0) ?_ ht_atTop
      filter_upwards [self_mem_nhdsWithin, hev_I_half] with t (ht : 0 < t) hIt
      have hI_pos : 0 < I t := by
        have hmul := mul_lt_mul_of_pos_right hIt ht
        rw [div_mul_cancel₀ _ ht.ne'] at hmul
        have hpos : 0 < (c / 2) * t := mul_pos (half_pos hc_pos) ht
        linarith
      have hf0 : f 0 = 0 := by
        dsimp [f]; unfold Z_twoway; rw [add_zero, hI, signedPow_zero_left (one_div_pos.mpr hg_pos)]
      have hft : f t = (I t) ^ (1 - α) := by
        dsimp [f, I]; unfold Z_twoway
        rw [signedPow_nonneg hI_pos.le (one_div_pos.mpr hg_pos), one_div_gamma]
      have hsl : slope f 0 t = (I t / t) ^ (1 - α) * t ^ (-α) := by
        rw [slope, sub_zero, vsub_eq_sub, hf0, sub_zero, smul_eq_mul, hft]
        have hI_split : I t = (I t / t) * t := (div_mul_cancel₀ _ ht.ne').symm
        conv_lhs => rw [hI_split, Real.mul_rpow (by linarith) ht.le]
        calc t⁻¹ * ((I t / t) ^ (1 - α) * t ^ (1 - α))
            = (I t / t) ^ (1 - α) * (t ^ (-1 : ℝ) * t ^ (1 - α)) := by
              rw [← Real.rpow_neg_one t]; ring
          _ = (I t / t) ^ (1 - α) * t ^ (-α) := by
              rw [← Real.rpow_add ht, show (-1 : ℝ) + (1 - α) = -α by ring]
      rw [hsl]
      have hpow_le : (c / 2) ^ (1 - α) ≤ (I t / t) ^ (1 - α) :=
        Real.rpow_le_rpow (by linarith) hIt.le (sub_pos.mpr h1).le
      exact mul_le_mul_of_nonneg_right hpow_le (Real.rpow_pos_of_pos ht _).le
    exact not_tendsto_nhds_of_tendsto_atTop hslope_atTop (deriv f 0) hf_gt

theorem Z_twoway_half_opposite_sign {W₁ N₁ W₂ N₂ : ℝ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (h1 : 0 ≤ W₁) (h2 : W₂ < 0) :
    let Z₁ := Z_alpha W₁ N₁ (1 / 2)
    let Z₂ := Z_alpha W₂ N₂ (1 / 2)
    Z_twoway W₁ N₁ W₂ N₂ (1 / 2) =
      Real.sign (Z₁ ^ 2 - Z₂ ^ 2) * Real.sqrt |Z₁ ^ 2 - Z₂ ^ 2| := by
  intro Z₁ Z₂
  have hg : gamma (1 / 2 : ℝ) = 2 := by unfold gamma; norm_num
  have hI : I_twoway W₁ N₁ W₂ N₂ (1 / 2) = Z₁ ^ 2 - Z₂ ^ 2 := by
    unfold I_twoway
    rw [twoway_I_alt_form hN₁ (by norm_num), twoway_I_alt_form hN₂ (by norm_num), hg]
    have hZ1_nn : 0 ≤ Z₁ := by dsimp [Z₁, Z_alpha]; positivity
    have hZ2_neg : Z₂ < 0 := by
      dsimp [Z₂, Z_alpha]
      exact div_neg_of_neg_of_pos h2 (Real.rpow_pos_of_pos hN₂ _)
    rw [signedPow_nonneg hZ1_nn (by norm_num), signedPow_neg hZ2_neg, Real.rpow_two, Real.rpow_two]
    ring
  unfold Z_twoway signedPow
  rw [hg, hI, ← Real.sqrt_eq_rpow]

/-- Sec. 3.5 & Appendix B (`app:twoway`): unconditional signed-Euclidean form of `Z_{1/2, 2D}`
on `ℝ²`, `sgn(I_{1/2}) √|I_{1/2}|` with `I_{1/2} = |Z₁| Z₁ + |Z₂| Z₂`. -/
theorem Z_twoway_half_signed_euclidean {W₁ N₁ W₂ N₂ : ℝ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) :
    let Z₁ := Z_alpha W₁ N₁ (1 / 2)
    let Z₂ := Z_alpha W₂ N₂ (1 / 2)
    let I := |Z₁| * Z₁ + |Z₂| * Z₂
    Z_twoway W₁ N₁ W₂ N₂ (1 / 2) = Real.sign I * Real.sqrt |I| := by
  intro Z₁ Z₂ I
  have hg : gamma (1 / 2 : ℝ) = 2 := by unfold gamma; norm_num
  have hsp2 : ∀ x : ℝ, signedPow x 2 = |x| * x := by
    intro x
    unfold signedPow
    rw [Real.rpow_two]
    calc Real.sign x * |x| ^ 2
        = (Real.sign x * |x|) * |x| := by ring
      _ = x * |x| := by rw [real_sign_mul_abs]
      _ = |x| * x := mul_comm x |x|
  have hI : I_twoway W₁ N₁ W₂ N₂ (1 / 2) = I := by
    unfold I_twoway
    rw [twoway_I_alt_form hN₁ (by norm_num), twoway_I_alt_form hN₂ (by norm_num), hg]
    rw [hsp2 Z₁, hsp2 Z₂]
  unfold Z_twoway signedPow
  rw [hg, hI, ← Real.sqrt_eq_rpow]

theorem Z_twoway_half_both_neg {W₁ N₁ W₂ N₂ : ℝ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (h1 : W₁ ≤ 0) (h2 : W₂ ≤ 0) :
    Z_twoway W₁ N₁ W₂ N₂ (1 / 2) =
      -Real.sqrt (Z_alpha W₁ N₁ (1 / 2) ^ 2 + Z_alpha W₂ N₂ (1 / 2) ^ 2) := by
  rw [Z_twoway_half_signed_euclidean hN₁ hN₂]
  set Z₁ := Z_alpha W₁ N₁ (1 / 2)
  set Z₂ := Z_alpha W₂ N₂ (1 / 2)
  have hZ1 : Z₁ ≤ 0 := div_nonpos_of_nonpos_of_nonneg h1 (Real.rpow_pos_of_pos hN₁ _).le
  have hZ2 : Z₂ ≤ 0 := div_nonpos_of_nonpos_of_nonneg h2 (Real.rpow_pos_of_pos hN₂ _).le
  have hI : |Z₁| * Z₁ + |Z₂| * Z₂ = -(Z₁ ^ 2 + Z₂ ^ 2) := by
    rw [abs_of_nonpos hZ1, abs_of_nonpos hZ2]; ring
  rw [hI, abs_neg, abs_of_nonneg (by positivity)]
  rcases eq_or_lt_of_le (add_nonneg (sq_nonneg Z₁) (sq_nonneg Z₂)) with h0 | hpos
  · rw [← h0]; simp [Real.sign_zero]
  · rw [Real.sign_of_neg (neg_lt_zero.mpr hpos)]; ring

/-- Appendix B: under opposite signs, `Z_twoway` and `Z_pool` cannot be ordered in general. -/
theorem twoway_zpool_opposite_sign_incomparable :
    (∃ W₁ N₁ W₂ N₂ : ℝ, 0 < W₁ ∧ 0 < N₁ ∧ W₂ < 0 ∧ 0 < N₂ ∧
      Z_twoway W₁ N₁ W₂ N₂ (1 / 2) > Z_pool W₁ N₁ W₂ N₂ (1 / 2)) ∧
    (∃ W₁ N₁ W₂ N₂ : ℝ, 0 < W₁ ∧ 0 < N₁ ∧ W₂ < 0 ∧ 0 < N₂ ∧
      Z_twoway W₁ N₁ W₂ N₂ (1 / 2) < Z_pool W₁ N₁ W₂ N₂ (1 / 2)) := by
  constructor
  · refine ⟨10, 100, -2, 10000, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    have hg : gamma (1 / 2 : ℝ) = 2 := by unfold gamma; norm_num
    have hI : I_twoway 10 100 (-2) 10000 (1 / 2) = 1 - 1 / 2500 := by
      unfold I_twoway
      rw [hg, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_one]
      rw [signedPow_nonneg (by norm_num) (by norm_num), signedPow_neg (by norm_num)]
      norm_num
    have hZ1 : Z_twoway 10 100 (-2) 10000 (1 / 2) = Real.sqrt (1 - 1 / 2500) := by
      unfold Z_twoway
      rw [hI, hg, signedPow_nonneg (by norm_num) (by norm_num), ← Real.sqrt_eq_rpow]
    have hP : Z_pool 10 100 (-2) 10000 (1 / 2) = 8 / Real.sqrt 10100 := by
      unfold Z_pool; rw [← Real.sqrt_eq_rpow]; norm_num
    rw [gt_iff_lt, hZ1, hP]
    have h1 : (8 / Real.sqrt 10100) ^ 2 < 1 - 1 / 2500 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    have hlt := Real.sqrt_lt_sqrt (sq_nonneg _) h1
    rwa [Real.sqrt_sq (by positivity)] at hlt
  · refine ⟨10, 100, -1, 1, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    have hg : gamma (1 / 2 : ℝ) = 2 := by unfold gamma; norm_num
    have hI : I_twoway 10 100 (-1) 1 (1 / 2) = 0 := by
      unfold I_twoway
      rw [hg, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_one]
      rw [signedPow_nonneg (by norm_num) (by norm_num), signedPow_neg (by norm_num)]
      norm_num
    have hZ : Z_twoway 10 100 (-1) 1 (1 / 2) = 0 := by
      unfold Z_twoway
      rw [hI, hg, signedPow_zero_left (by norm_num)]
    have hP : 0 < Z_pool 10 100 (-1) 1 (1 / 2) := by
      unfold Z_pool
      exact div_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)
    linarith

/-! ## Section 12: Section 3.3 OLS σ² Estimation & Remark 5 Ordered-Pair Identity -/

theorem ols_constant_rate_rss_eq_lagrange {ι : Type*} (s : Finset ι)
    (W N : ι → ℝ) (hN : ∀ j ∈ s, 0 < N j) (hS : ∑ j ∈ s, N j ≠ 0) :
    let r_hat := (∑ j ∈ s, W j) / (∑ j ∈ s, N j)
    ∑ j ∈ s, (W j / Real.sqrt (N j) - r_hat * Real.sqrt (N j)) ^ 2 =
      (∑ j ∈ s, W j ^ 2 / N j) - (∑ j ∈ s, W j) ^ 2 / (∑ j ∈ s, N j) := by
  intro r_hat
  have hterm : ∀ j ∈ s,
      (W j / Real.sqrt (N j) - r_hat * Real.sqrt (N j)) ^ 2 =
        W j ^ 2 / N j - 2 * r_hat * W j + r_hat ^ 2 * N j := by
    intro j hj
    have hNj := hN j hj
    have hsne : Real.sqrt (N j) ≠ 0 := (Real.sqrt_pos.mpr hNj).ne'
    have hsq : Real.sqrt (N j) ^ 2 = N j := Real.sq_sqrt hNj.le
    calc (W j / Real.sqrt (N j) - r_hat * Real.sqrt (N j)) ^ 2
        = W j ^ 2 / Real.sqrt (N j) ^ 2 - 2 * r_hat * W j * (Real.sqrt (N j) / Real.sqrt (N j)) +
            r_hat ^ 2 * Real.sqrt (N j) ^ 2 := by ring
      _ = W j ^ 2 / N j - 2 * r_hat * W j + r_hat ^ 2 * N j := by
            rw [hsq, div_self hsne, mul_one]
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  dsimp [r_hat]
  field_simp [hS]
  ring

theorem ols_constant_rate_minimizer {ι : Type*} (s : Finset ι)
    (W N : ι → ℝ) (hN : ∀ j ∈ s, 0 < N j) (hS : ∑ j ∈ s, N j ≠ 0) (r : ℝ) :
    let r_hat := (∑ j ∈ s, W j) / (∑ j ∈ s, N j)
    ∑ j ∈ s, (W j / Real.sqrt (N j) - r * Real.sqrt (N j)) ^ 2 =
      ∑ j ∈ s, (W j / Real.sqrt (N j) - r_hat * Real.sqrt (N j)) ^ 2 +
        (r - r_hat) ^ 2 * (∑ j ∈ s, N j) := by
  intro r_hat
  have hterm : ∀ j ∈ s,
      (W j / Real.sqrt (N j) - r * Real.sqrt (N j)) ^ 2 =
        (W j / Real.sqrt (N j) - r_hat * Real.sqrt (N j)) ^ 2 +
          2 * (r_hat - r) * (W j - r_hat * N j) +
          (r - r_hat) ^ 2 * N j := by
    intro j hj
    have hNj := hN j hj
    have hsne : Real.sqrt (N j) ≠ 0 := (Real.sqrt_pos.mpr hNj).ne'
    have hsq : Real.sqrt (N j) ^ 2 = N j := Real.sq_sqrt hNj.le
    calc (W j / Real.sqrt (N j) - r * Real.sqrt (N j)) ^ 2
        = (W j / Real.sqrt (N j) - r_hat * Real.sqrt (N j) + (r_hat - r) * Real.sqrt (N j)) ^ 2 := by
            ring
      _ = (W j / Real.sqrt (N j) - r_hat * Real.sqrt (N j)) ^ 2 +
            2 * (r_hat - r) * (W j * (Real.sqrt (N j) / Real.sqrt (N j)) - r_hat * Real.sqrt (N j) ^ 2) +
            (r - r_hat) ^ 2 * Real.sqrt (N j) ^ 2 := by ring
      _ = (W j / Real.sqrt (N j) - r_hat * Real.sqrt (N j)) ^ 2 +
            2 * (r_hat - r) * (W j - r_hat * N j) +
            (r - r_hat) ^ 2 * N j := by rw [div_self hsne, mul_one, hsq]
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcross : ∑ j ∈ s, (W j - r_hat * N j) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    dsimp [r_hat]
    field_simp [hS]
    ring
  rw [hcross, mul_zero, add_zero]

/-- Exact ordered-pair form of Remark 5 (`rem:partition`, Eq. 14). -/
theorem rem_partition_ordered_pairs {ι : Type*} [LinearOrder ι] (s : Finset ι)
    (W N : ι → ℝ) (hN : ∀ j ∈ s, 0 < N j) (hS : 0 < ∑ j ∈ s, N j) :
    (∑ j ∈ s, W j ^ 2 / N j) - (∑ j ∈ s, W j) ^ 2 / (∑ j ∈ s, N j) =
      (1 / ∑ j ∈ s, N j) *
        ∑ j ∈ s, ∑ k ∈ s with j < k, N j * N k * (W j / N j - W k / N k) ^ 2 := by
  let f : ι → ι → ℝ := fun j k => N j * N k * (W j / N j - W k / N k) ^ 2
  have hsymm : ∀ j k, f j k = f k j := by
    intro j k; dsimp [f]; ring
  have hdiag : ∀ j, f j j = 0 := by
    intro j; dsimp [f]; ring
  have hsplit : ∑ j ∈ s, ∑ k ∈ s, f j k = 2 * ∑ j ∈ s, ∑ k ∈ s with j < k, f j k := by
    have hrow : ∀ j ∈ s,
        ∑ k ∈ s, f j k = (∑ k ∈ s with j < k, f j k) + (∑ k ∈ s with k < j, f j k) := by
      intro j hj
      have hpart1 : ∑ k ∈ s, f j k =
          (∑ k ∈ s with j < k, f j k) + (∑ k ∈ s with ¬ (j < k), f j k) := by
        rw [Finset.sum_filter_add_sum_filter_not]
      have hpart2 : ∑ k ∈ s with ¬ (j < k), f j k =
          (∑ k ∈ s with ¬ (j < k) ∧ k = j, f j k) +
          (∑ k ∈ s with ¬ (j < k) ∧ k ≠ j, f j k) := by
        rw [← Finset.sum_filter_add_sum_filter_not (s.filter fun k => ¬ (j < k)) (fun k => k = j)]
        simp [Finset.filter_filter]
      have hdiag_sum : ∑ k ∈ s with ¬ (j < k) ∧ k = j, f j k = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        rw [Finset.mem_filter] at hk
        rw [hk.2.2, hdiag]
      have hlt_eq : (s.filter fun k => ¬ (j < k) ∧ k ≠ j) = s.filter fun k => k < j := by
        ext k; simp only [Finset.mem_filter, not_lt]
        exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, lt_of_le_of_ne h2 h3⟩,
               fun ⟨h1, h2⟩ => ⟨h1, h2.le, h2.ne⟩⟩
      rw [hpart1, hpart2, hdiag_sum, zero_add, hlt_eq]
    rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib]
    have hswap :
        (∑ j ∈ s, ∑ k ∈ s with k < j, f j k) =
          ∑ k ∈ s, ∑ j ∈ s with k < j, f k j := by
      simp only [Finset.sum_filter]
      calc ∑ j ∈ s, ∑ k ∈ s, (if k < j then f j k else 0)
          = ∑ k ∈ s, ∑ j ∈ s, (if k < j then f j k else 0) := Finset.sum_comm
        _ = ∑ k ∈ s, ∑ j ∈ s, (if k < j then f k j else 0) := by
            refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
            split_ifs <;> simp [hsymm]
    rw [hswap]
    ring
  have hlag := (rem_partition_general_lagrange s W N hN hS).1
  change (∑ j ∈ s, W j ^ 2 / N j) - (∑ j ∈ s, W j) ^ 2 / (∑ j ∈ s, N j) =
    (1 / (2 * ∑ j ∈ s, N j)) * ∑ j ∈ s, ∑ k ∈ s, f j k at hlag
  rw [hlag, hsplit]
  dsimp only [f]
  field_simp [hS.ne']

section OLS_Variance

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem ols_season_homoscedastic {m : ℕ} (W : Fin m → Ω → ℝ) (N : Fin m → ℝ) {σ : ℝ}
    (hN : ∀ j, 0 < N j) (hvar : ∀ j, variance (W j) μ = N j * σ ^ 2) (j : Fin m) :
    variance (fun ω => W j ω / Real.sqrt (N j)) μ = σ ^ 2 := by
  have heq : (fun ω => W j ω / Real.sqrt (N j)) = fun ω => (Real.sqrt (N j))⁻¹ * W j ω := by
    ext ω; rw [div_eq_inv_mul]
  rw [heq, variance_const_mul, hvar j]
  have hspos : 0 < Real.sqrt (N j) := Real.sqrt_pos.mpr (hN j)
  have hsq : Real.sqrt (N j) ^ 2 = N j := Real.sq_sqrt (hN j).le
  rw [inv_pow, hsq]
  field_simp [(hN j).ne']

theorem ols_rss_unbiased {m : ℕ} (hm : 0 < m) (W : Fin m → Ω → ℝ) (N : Fin m → ℝ) {r σ : ℝ}
    (hN : ∀ j, 0 < N j)
    (hL2 : ∀ j, MemLp (W j) 2 μ)
    (hmean : ∀ j, ∫ ω, W j ω ∂μ = r * N j)
    (hvar : ∀ j, variance (W j) μ = N j * σ ^ 2)
    (huncorr : ∀ j k, j ≠ k → cov[W j, W k; μ] = 0) :
    ∫ ω, (∑ j : Fin m, (W j ω / Real.sqrt (N j) -
        ((∑ i : Fin m, W i ω) / (∑ i : Fin m, N i)) * Real.sqrt (N j)) ^ 2) ∂μ =
      ((m : ℝ) - 1) * σ ^ 2 := by
  let N_tot : ℝ := ∑ i : Fin m, N i
  have hN_tot_pos : 0 < N_tot := Finset.sum_pos (fun j _ => hN j)
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hpt : ∀ ω : Ω,
      ∑ j : Fin m, (W j ω / Real.sqrt (N j) -
        ((∑ i : Fin m, W i ω) / N_tot) * Real.sqrt (N j)) ^ 2 =
      (∑ j : Fin m, W j ω ^ 2 / N j) - (∑ i : Fin m, W i ω) ^ 2 / N_tot := by
    intro ω
    exact ols_constant_rate_rss_eq_lagrange Finset.univ (fun j => W j ω) N
      (fun j _ => hN j) hN_tot_pos.ne'
  change ∫ ω, (∑ j : Fin m, (W j ω / Real.sqrt (N j) -
      ((∑ i : Fin m, W i ω) / N_tot) * Real.sqrt (N j)) ^ 2) ∂μ = ((m : ℝ) - 1) * σ ^ 2
  simp_rw [hpt]
  have hint_sq : ∀ j, Integrable (fun ω => W j ω ^ 2) μ := fun j => by
    have hmul := (hL2 j).integrable_mul (hL2 j)
    simpa [pow_two] using hmul
  have hint_term : ∀ j, Integrable (fun ω => W j ω ^ 2 / N j) μ :=
    fun j => (hint_sq j).div_const (N j)
  have hW_sum_L2 : MemLp (fun ω => ∑ i : Fin m, W i ω) 2 μ :=
    memLp_finset_sum Finset.univ (fun i _ => hL2 i)
  have hint_sum_sq : Integrable (fun ω => (∑ i : Fin m, W i ω) ^ 2 / N_tot) μ := by
    have hmul := hW_sum_L2.integrable_mul hW_sum_L2
    have hsq : Integrable (fun ω => (∑ i : Fin m, W i ω) ^ 2) μ := by
      simpa [pow_two] using hmul
    exact hsq.div_const N_tot
  rw [integral_sub (integrable_finset_sum _ fun j _ => hint_term j) hint_sum_sq,
      integral_finset_sum _ fun j _ => hint_term j]
  have hE_term : ∀ j : Fin m, ∫ ω, W j ω ^ 2 / N j ∂μ = σ ^ 2 + r ^ 2 * N j := by
    intro j
    rw [integral_div, show ∫ ω, W j ω ^ 2 ∂μ = μ[W j ^ 2] from rfl]
    have hv := variance_eq_sub (hL2 j)
    have hsq : μ[W j ^ 2] = N j * σ ^ 2 + (r * N j) ^ 2 := by
      rw [hvar j, show μ[W j] = r * N j from hmean j] at hv
      linarith
    rw [hsq]
    field_simp [(hN j).ne']
  have hE_sum : ∫ ω, (∑ i : Fin m, W i ω) ∂μ = r * N_tot := by
    rw [integral_finset_sum _ fun i _ => (hL2 i).integrable one_le_two]
    simp_rw [hmean, ← Finset.mul_sum]
    rfl
  have hV_sum : variance (fun ω => ∑ i : Fin m, W i ω) μ = N_tot * σ ^ 2 := by
    rw [variance_fun_sum hL2]
    have hinner : ∀ i : Fin m, ∑ k : Fin m, cov[W i, W k; μ] = N i * σ ^ 2 := by
      intro i
      rw [Finset.sum_eq_single i]
      · rw [covariance_self (hL2 i).aemeasurable, hvar i]
      · intro k _ hki; exact huncorr i k hki.symm
      · intro hi; exact absurd (Finset.mem_univ i) hi
    simp_rw [hinner, ← Finset.sum_mul]
    rfl
  have hE_tot_term :
      ∫ ω, (∑ i : Fin m, W i ω) ^ 2 / N_tot ∂μ = σ ^ 2 + r ^ 2 * N_tot := by
    rw [integral_div]
    have hv := variance_eq_sub hW_sum_L2
    change variance (fun ω => ∑ i : Fin m, W i ω) μ =
        (∫ ω, (∑ i : Fin m, W i ω) ^ 2 ∂μ) - (∫ ω, (∑ i : Fin m, W i ω) ∂μ) ^ 2 at hv
    have hsq : ∫ ω, (∑ i : Fin m, W i ω) ^ 2 ∂μ = N_tot * σ ^ 2 + (r * N_tot) ^ 2 := by
      rw [hV_sum, hE_sum] at hv
      linarith
    rw [hsq]
    field_simp [hN_tot_pos.ne']
  simp_rw [hE_term, hE_tot_term, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
           Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  change (m : ℝ) * σ ^ 2 + r ^ 2 * N_tot - (σ ^ 2 + r ^ 2 * N_tot) = ((m : ℝ) - 1) * σ ^ 2
  ring

end OLS_Variance

/-! ## Section 13: Appendix H Variance, Delta-Method, and Rounding Scaling -/

section AppendixH_Uncertainty

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem zpool_var_eq_sigma_sq (W₁ W₂ : Ω → ℝ) {PA BF σ : ℝ}
    (h1 : MemLp W₁ 2 μ) (h2 : MemLp W₂ 2 μ)
    (huncorr : cov[W₁, W₂; μ] = 0)
    (hv1 : variance W₁ μ = PA * σ ^ 2) (hv2 : variance W₂ μ = BF * σ ^ 2)
    (hsum : 0 < PA + BF) :
    variance (fun ω => Z_pool (W₁ ω) PA (W₂ ω) BF (1 / 2)) μ = σ ^ 2 := by
  have heq : (fun ω => Z_pool (W₁ ω) PA (W₂ ω) BF (1 / 2)) =
      fun ω => (Real.sqrt (PA + BF))⁻¹ * (W₁ ω + W₂ ω) := by
    ext ω; unfold Z_pool; rw [← Real.sqrt_eq_rpow, div_eq_inv_mul]
  rw [heq, variance_const_mul, variance_fun_add h1 h2, huncorr, hv1, hv2]
  have hsq : Real.sqrt (PA + BF) ^ 2 = PA + BF := Real.sq_sqrt hsum.le
  rw [inv_pow, hsq]
  field_simp [hsum.ne']
  ring

theorem unweighted_sum_var_eq_two_sigma_sq (W₁ W₂ : Ω → ℝ) {PA BF σ : ℝ}
    (h1 : MemLp W₁ 2 μ) (h2 : MemLp W₂ 2 μ)
    (huncorr : cov[W₁, W₂; μ] = 0)
    (hv1 : variance W₁ μ = PA * σ ^ 2) (hv2 : variance W₂ μ = BF * σ ^ 2)
    (hPA : 0 < PA) (hBF : 0 < BF) :
    variance (fun ω => Z_alpha (W₁ ω) PA (1 / 2) + Z_alpha (W₂ ω) BF (1 / 2)) μ = 2 * σ ^ 2 := by
  let X₁ : Ω → ℝ := fun ω => (Real.sqrt PA)⁻¹ * W₁ ω
  let X₂ : Ω → ℝ := fun ω => (Real.sqrt BF)⁻¹ * W₂ ω
  have hX1 : MemLp X₁ 2 μ := h1.const_mul _
  have hX2 : MemLp X₂ 2 μ := h2.const_mul _
  have heq : (fun ω => Z_alpha (W₁ ω) PA (1 / 2) + Z_alpha (W₂ ω) BF (1 / 2)) =
      fun ω => X₁ ω + X₂ ω := by
    ext ω; unfold Z_alpha
    dsimp only [X₁, X₂]
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, div_eq_inv_mul, div_eq_inv_mul]
  rw [heq, variance_fun_add hX1 hX2]
  have hcov : cov[X₁, X₂; μ] = 0 := by
    dsimp [X₁, X₂]
    rw [covariance_const_mul_left, covariance_const_mul_right, huncorr, mul_zero, mul_zero]
  have hvX1 : variance X₁ μ = σ ^ 2 := by
    dsimp [X₁]; rw [variance_const_mul, hv1, inv_pow, Real.sq_sqrt hPA.le]
    field_simp [hPA.ne']
  have hvX2 : variance X₂ μ = σ ^ 2 := by
    dsimp [X₂]; rw [variance_const_mul, hv2, inv_pow, Real.sq_sqrt hBF.le]
    field_simp [hBF.ne']
  rw [hcov, hvX1, hvX2]
  ring

theorem diff_two_players_sd (Z₁ Z₂ : Ω → ℝ) {σ : ℝ}
    (h1 : MemLp Z₁ 2 μ) (h2 : MemLp Z₂ 2 μ)
    (huncorr : cov[Z₁, Z₂; μ] = 0)
    (hv1 : variance Z₁ μ = σ ^ 2) (hv2 : variance Z₂ μ = σ ^ 2)
    (hσ : 0 ≤ σ) :
    variance (fun ω => Z₁ ω - Z₂ ω) μ = 2 * σ ^ 2 ∧
      Real.sqrt (variance (fun ω => Z₁ ω - Z₂ ω) μ) = Real.sqrt 2 * σ := by
  have hvar : variance (fun ω => Z₁ ω - Z₂ ω) μ = 2 * σ ^ 2 := by
    rw [variance_fun_sub h1 h2, huncorr, hv1, hv2]
    ring
  refine ⟨hvar, ?_⟩
  rw [hvar, Real.sqrt_mul (by norm_num), Real.sqrt_sq hσ]

/-- Appendix H (`app:uncert`): Baseball-Reference's leverage multiplier `(1 + L)/2`
applied to `WAA` with deterministic replacement runs `R_rep` scales variance by `((1 + L)/2)²`. -/
theorem app_h_leverage_variance_scaling (X : Ω → ℝ) (L R_rep : ℝ) (hX : MemLp X 2 μ) :
    variance (fun ω => ((1 + L) / 2) * X ω + R_rep) μ = ((1 + L) / 2) ^ 2 * variance X μ := by
  rw [variance_add_const (hX.aestronglyMeasurable.const_mul _) R_rep, variance_const_mul]

/-- Appendix H (`app:uncert`): ratio of standard deviations between two leverage groups
`L₁, L₂ > -1` equals `(1 + L₁)/(1 + L₂)`. -/
theorem app_h_leverage_sd_ratio (X : Ω → ℝ) {L₁ L₂ R₁ R₂ : ℝ}
    (hX : MemLp X 2 μ) (hV : 0 < variance X μ) (hL₁ : -1 < L₁) (hL₂ : -1 < L₂) :
    Real.sqrt (variance (fun ω => ((1 + L₁) / 2) * X ω + R₁) μ) /
      Real.sqrt (variance (fun ω => ((1 + L₂) / 2) * X ω + R₂) μ) =
    (1 + L₁) / (1 + L₂) := by
  rw [app_h_leverage_variance_scaling X L₁ R₁ hX, app_h_leverage_variance_scaling X L₂ R₂ hX]
  have h1 : 0 < (1 + L₁) / 2 := by linarith
  have h2 : 0 < (1 + L₂) / 2 := by linarith
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq h1.le, Real.sqrt_sq h2.le]
  have hsd : Real.sqrt (variance X μ) ≠ 0 := (Real.sqrt_pos.mpr hV).ne'
  field_simp [hsd]

end AppendixH_Uncertainty

/-- Appendix H: first-order gradient and unit-norm gradient squared of the Euclidean
quadrature `√(z₁² + z₂²)` away from `(0, 0)` (delta-method variance `‖∇‖² σ² = σ²`). -/
theorem delta_method_quadrature_grad_norm_sq {z₁ z₂ : ℝ} (hne : z₁ ≠ 0 ∨ z₂ ≠ 0) :
    0 < z₁ ^ 2 + z₂ ^ 2 ∧
    HasFDerivAt (fun p : ℝ × ℝ => Real.sqrt (p.1 ^ 2 + p.2 ^ 2))
      ((z₁ / Real.sqrt (z₁ ^ 2 + z₂ ^ 2)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
       (z₂ / Real.sqrt (z₁ ^ 2 + z₂ ^ 2)) • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (z₁, z₂) ∧
    (z₁ / Real.sqrt (z₁ ^ 2 + z₂ ^ 2)) ^ 2 + (z₂ / Real.sqrt (z₁ ^ 2 + z₂ ^ 2)) ^ 2 = 1 := by
  have hss_pos : 0 < z₁ ^ 2 + z₂ ^ 2 := by
    rcases hne with h1 | h2
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h1) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h2)
  have hf : HasFDerivAt (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2)
      ((2 * z₁) • ContinuousLinearMap.fst ℝ ℝ ℝ +
       (2 * z₂) • ContinuousLinearMap.snd ℝ ℝ ℝ) (z₁, z₂) := by
    have hf1 := ((hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (z₁, z₂))).pow 2)
    have hf2 := ((hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (z₁, z₂))).pow 2)
    convert hf1.add hf2 using 1
    simp [Nat.cast_ofNat, mul_comm]
  have hsqrt := hf.sqrt hss_pos.ne'
  have hsne : Real.sqrt (z₁ ^ 2 + z₂ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hss_pos).ne'
  refine ⟨hss_pos, ?_, ?_⟩
  · convert hsqrt using 1
    ext <;> simp <;> field_simp [hsne]
  · have hsq : Real.sqrt (z₁ ^ 2 + z₂ ^ 2) ^ 2 = z₁ ^ 2 + z₂ ^ 2 := Real.sq_sqrt hss_pos.le
    rw [div_pow, div_pow, hsq]
    field_simp [hss_pos.ne']

/-- Appendix H (`app:uncert`): for both coordinates negative (away from `(0, 0)`),
`-√(z₁² + z₂²)` also has unit-norm gradient (`‖∇‖² = 1`). -/
theorem delta_method_quadrature_both_neg_grad_norm_sq {z₁ z₂ : ℝ} (hne : z₁ ≠ 0 ∨ z₂ ≠ 0) :
    HasFDerivAt (fun p : ℝ × ℝ => -Real.sqrt (p.1 ^ 2 + p.2 ^ 2))
      ((-(z₁ / Real.sqrt (z₁ ^ 2 + z₂ ^ 2))) • ContinuousLinearMap.fst ℝ ℝ ℝ +
       (-(z₂ / Real.sqrt (z₁ ^ 2 + z₂ ^ 2))) • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (z₁, z₂) ∧
    (-(z₁ / Real.sqrt (z₁ ^ 2 + z₂ ^ 2))) ^ 2 +
      (-(z₂ / Real.sqrt (z₁ ^ 2 + z₂ ^ 2))) ^ 2 = 1 := by
  obtain ⟨_, hfd, hnorm⟩ := delta_method_quadrature_grad_norm_sq hne
  refine ⟨?_, ?_⟩
  · convert hfd.neg using 1
    ext <;> simp
  · simpa [neg_sq] using hnorm

/-- Appendix H (`app:uncert`): for opposite-sign coordinates away from the cancellation
locus `z₁² = z₂²` (with both `z₁, z₂ ≠ 0`), the delta-method variance multiplier `(z₁² + z₂²)/|z₁² - z₂²|`
is strictly greater than `1` (explaining why `Var(Z_{2D}) ≈ σ²` requires same signs or one dominant
coordinate). -/
theorem delta_method_quadrature_opp_sign_grad_norm_gt {z₁ z₂ : ℝ}
    (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) (hne : z₁ ^ 2 ≠ z₂ ^ 2) :
    1 < (z₁ / Real.sqrt |z₁ ^ 2 - z₂ ^ 2|) ^ 2 + (-z₂ / Real.sqrt |z₁ ^ 2 - z₂ ^ 2|) ^ 2 := by
  have hdiff_pos : 0 < |z₁ ^ 2 - z₂ ^ 2| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hsq : Real.sqrt |z₁ ^ 2 - z₂ ^ 2| ^ 2 = |z₁ ^ 2 - z₂ ^ 2| := Real.sq_sqrt hdiff_pos.le
  rw [div_pow, div_pow, hsq, neg_sq, ← add_div, one_lt_div hdiff_pos]
  have hz1_pos : 0 < z₁ ^ 2 := sq_pos_of_ne_zero hz₁
  have hz2_pos : 0 < z₂ ^ 2 := sq_pos_of_ne_zero hz₂
  rcases abs_cases (z₁ ^ 2 - z₂ ^ 2) with ⟨h1, _⟩ | ⟨h1, _⟩
  · rw [h1]; linarith
  · rw [h1]; linarith

/-- Section 6 & Appendix H: exact rounding shift `Z_α(W + ΔW, N) - Z_α(W, N) = ΔW / N^α` and
magnitude `|ΔZ_α| = |ΔW| / N^α`. -/
theorem app_h_rounding_shift {W ΔW N α : ℝ} (hN : 0 < N) :
    Z_alpha (W + ΔW) N α - Z_alpha W N α = ΔW / N ^ α ∧
    |Z_alpha (W + ΔW) N α - Z_alpha W N α| = |ΔW| / N ^ α := by
  unfold Z_alpha
  have hsub : (W + ΔW) / N ^ α - W / N ^ α = ΔW / N ^ α := by rw [add_div, add_sub_cancel_left]
  refine ⟨hsub, ?_⟩
  rw [hsub, abs_div, abs_of_pos (Real.rpow_pos_of_pos hN α)]

/-- Appendix H: relative rounding perturbation `ΔZ_α / Z_α = ΔW / W` is independent of `α`. -/
theorem rounding_relative_change_alpha_invariant {W ΔW N α : ℝ}
    (hW : W ≠ 0) (hN : 0 < N) :
    (Z_alpha (W + ΔW) N α - Z_alpha W N α) / Z_alpha W N α = ΔW / W := by
  unfold Z_alpha
  have hpow : N ^ α ≠ 0 := (Real.rpow_pos_of_pos hN α).ne'
  field_simp [hW, hpow]
  ring

/-- Appendix H: `Z_{1/5} / Z_{1/2} = N^{0.3}` linking the rounding tolerances. -/
theorem z_ratio_02_05 {W N : ℝ} (hW : W ≠ 0) (hN : 0 < N) :
    Z_alpha W N (1 / 5) / Z_alpha W N (1 / 2) = N ^ ((3 : ℝ) / 10) := by
  unfold Z_alpha
  have h1 : N ^ (1 / 5 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hN _).ne'
  have h2 : N ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hN _).ne'
  calc (W / N ^ (1 / 5 : ℝ)) / (W / N ^ (1 / 2 : ℝ))
      = N ^ (1 / 2 : ℝ) / N ^ (1 / 5 : ℝ) := by field_simp [hW, h1, h2]
    _ = N ^ ((1 / 2 : ℝ) - (1 / 5 : ℝ)) := (Real.rpow_sub hN _ _).symm
    _ = N ^ ((3 : ℝ) / 10) := by norm_num

/-! ## Section 14: Additional Corollaries (Sections 3.2, 3.4, 5.5, Appendix C) -/

/-- Two-equation target scaling corollary (Section 5.5 & script 18):
if `log r_f = k₀ + k_r log r + k_N log N` and `log N_f = n₀ + n_r log r + n_N log N`,
then `log (r_f * N_f) = (k₀ + n₀) + (k_r + n_r) log Z_{α*}` with `α* = 1 - (k_N + n_N) / (k_r + n_r)`. -/
theorem prop_target_two_equation {W N r_f N_f k₀ k_r k_N n₀ n_r n_N : ℝ}
    (hW : 0 < W) (hN : 0 < N) (hrf : 0 < r_f) (hNf : 0 < N_f) (hkr : k_r + n_r ≠ 0)
    (hr_eq : Real.log r_f = k₀ + k_r * Real.log (W / N) + k_N * Real.log N)
    (hN_eq : Real.log N_f = n₀ + n_r * Real.log (W / N) + n_N * Real.log N) :
    let α_star := 1 - (k_N + n_N) / (k_r + n_r)
    Real.log (r_f * N_f) = (k₀ + n₀) + (k_r + n_r) * Real.log (Z_alpha W N α_star) := by
  intro α_star
  have hZ_pos : 0 < Z_alpha W N α_star := by unfold Z_alpha; positivity
  have hlogZ : Real.log (Z_alpha W N α_star) = Real.log W - α_star * Real.log N := by
    unfold Z_alpha
    rw [Real.log_div hW.ne' (Real.rpow_pos_of_pos hN _).ne', Real.log_rpow hN]
  rw [Real.log_mul hrf.ne' hNf.ne', hr_eq, hN_eq, hlogZ, Real.log_div hW.ne' hN.ne']
  dsimp [α_star]
  field_simp [hkr]
  ring

/-- Section 3.4: for equal season-form scores `W₁ / S₁^α = W₂ / S₂^α` with season exposures
`E₁, E₂ > 0`, the event-form ratio is `Z_α(W₁, E₁ S₁) / Z_α(W₂, E₂ S₂) = (E₂ / E₁)^α`. -/
theorem prop_gamma_season_vs_event_ratio {W₁ S₁ E₁ W₂ S₂ E₂ α : ℝ}
    (hS₁ : 0 < S₁) (hE₁ : 0 < E₁) (hS₂ : 0 < S₂) (hE₂ : 0 < E₂) (hW₂ : W₂ ≠ 0)
    (hS_eq : W₁ / S₁ ^ α = W₂ / S₂ ^ α) :
    Z_alpha W₁ (E₁ * S₁) α / Z_alpha W₂ (E₂ * S₂) α = (E₂ / E₁) ^ α := by
  unfold Z_alpha
  rw [Real.mul_rpow hE₁.le hS₁.le, Real.mul_rpow hE₂.le hS₂.le, Real.div_rpow hE₂.le hE₁.le]
  have hS1p : S₁ ^ α ≠ 0 := (Real.rpow_pos_of_pos hS₁ α).ne'
  have hS2p : S₂ ^ α ≠ 0 := (Real.rpow_pos_of_pos hS₂ α).ne'
  have hE1p : E₁ ^ α ≠ 0 := (Real.rpow_pos_of_pos hE₁ α).ne'
  have hE2p : E₂ ^ α ≠ 0 := (Real.rpow_pos_of_pos hE₂ α).ne'
  have hW1_eq : W₁ = (W₂ / S₂ ^ α) * S₁ ^ α := (div_eq_iff hS1p).mp hS_eq
  rw [hW1_eq]
  field_simp [hS1p, hS2p, hE1p, hE2p, hW₂]

/-- Appendix C: when `W - r₀ N < 0` and `N > 1`, dividing a negative numerator by `N^α`
reverses monotonicity, making `Z_{α,r₀}` strictly increasing in `α`. -/
theorem prop_null_neg_numerator_strictMono_alpha {W N r₀ α₁ α₂ : ℝ}
    (hneg : W - r₀ * N < 0) (hN : 1 < N) (hα : α₁ < α₂) :
    Z_null W N r₀ α₁ < Z_null W N r₀ α₂ := by
  unfold Z_null
  have hpow : N ^ α₁ < N ^ α₂ := Real.rpow_lt_rpow_of_exponent_lt hN hα
  have hNpos : 0 < N := by linarith
  have hp1 : 0 < N ^ α₁ := Real.rpow_pos_of_pos hNpos α₁
  have hp2 : 0 < N ^ α₂ := Real.rpow_pos_of_pos hNpos α₂
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hinv : (N ^ α₂)⁻¹ < (N ^ α₁)⁻¹ := inv_strictAnti₀ hp1 hpow
  nlinarith [hneg, hinv]

/-! ## Section 15: Comprehensive Extensions and Strengthenings -/

/-! ### 15.1 Floored Exposure, Exponent Monotonicity, and Empirical Bayes Rate (`eq:family`, Sec. 1 & 3) -/

/-- The floored α-family `Z_α = W / max(N, 1)^α` as defined in Eq. (4) (`eq:family`). -/
def Z_alpha_floored (W N α : ℝ) : ℝ := Z_alpha W (max N 1) α

/-- Empirical Bayes shrunken rate `r̂_EB = (W + N₀ r₀) / (N + N₀)` (Sec. 1, Eq. 3). -/
def r_EB (W N N₀ r₀ : ℝ) : ℝ := (W + N₀ * r₀) / (N + N₀)

theorem z_alpha_floored_of_le_one {W N α : ℝ} (hN : N ≤ 1) :
    Z_alpha_floored W N α = W := by
  unfold Z_alpha_floored Z_alpha
  rw [max_eq_right hN, Real.one_rpow, div_one]

theorem z_alpha_floored_of_one_le {W N α : ℝ} (hN : 1 ≤ N) :
    Z_alpha_floored W N α = Z_alpha W N α := by
  unfold Z_alpha_floored
  rw [max_eq_left hN]

/-- For `W > 0` and `N > 1`, `Z_α` is strictly decreasing in `α`. -/
theorem z_alpha_strictAnti_alpha_of_pos {W N : ℝ} (hW : 0 < W) (hN : 1 < N) :
    StrictAnti (fun α => Z_alpha W N α) := by
  intro α₁ α₂ hα
  unfold Z_alpha
  have hNpos : 0 < N := by linarith
  have hp1 : 0 < N ^ α₁ := Real.rpow_pos_of_pos hNpos α₁
  have hpow : N ^ α₁ < N ^ α₂ := Real.rpow_lt_rpow_of_exponent_lt hN hα
  exact div_lt_div_of_pos_left hW hp1 hpow

/-- For `W < 0` and `N > 1`, `Z_α` is strictly increasing in `α`. -/
theorem z_alpha_strictMono_alpha_of_neg {W N : ℝ} (hW : W < 0) (hN : 1 < N) :
    StrictMono (fun α => Z_alpha W N α) := by
  intro α₁ α₂ hα
  unfold Z_alpha
  dsimp only
  have hNpos : 0 < N := by linarith
  have hp1 : 0 < N ^ α₁ := Real.rpow_pos_of_pos hNpos α₁
  have hp2 : 0 < N ^ α₂ := Real.rpow_pos_of_pos hNpos α₂
  have hpow : N ^ α₁ < N ^ α₂ := Real.rpow_lt_rpow_of_exponent_lt hN hα
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_lt_mul_of_neg_left (inv_strictAnti₀ hp1 hpow) hW

/-- Eq. (3) (`sec:intro`): `r̂_EB` is a convex combination of raw rate `W/N` and prior `r₀`. -/
theorem r_EB_eq_convex_comb {W N N₀ r₀ : ℝ} (hN : 0 < N) (hN₀ : 0 ≤ N₀) :
    r_EB W N N₀ r₀ = (N / (N + N₀)) * (W / N) + (N₀ / (N + N₀)) * r₀ ∧
      N / (N + N₀) + N₀ / (N + N₀) = 1 := by
  have hsum : N + N₀ ≠ 0 := (by linarith : 0 < N + N₀).ne'
  unfold r_EB
  refine ⟨?_, ?_⟩
  · field_simp [hN.ne', hsum]
  · field_simp [hsum]

/-- Eq. (3) (`sec:intro`): for `N, N₀ > 0`, `r̂_EB` lies strictly between `r₀` and `W/N`
when they differ (`r₀ < W/N`). -/
theorem r_EB_strict_between {W N N₀ r₀ : ℝ} (hN : 0 < N) (hN₀ : 0 < N₀) (hlt : r₀ < W / N) :
    r₀ < r_EB W N N₀ r₀ ∧ r_EB W N N₀ r₀ < W / N := by
  have hsum : 0 < N + N₀ := by linarith
  unfold r_EB
  have h1 : r₀ * (N + N₀) < W + N₀ * r₀ := by
    have := (lt_div_iff₀ hN).mp hlt
    linarith
  have h2 : (W + N₀ * r₀) * N < W * (N + N₀) := by
    have := (lt_div_iff₀ hN).mp hlt
    nlinarith
  refine ⟨(lt_div_iff₀ hsum).mpr h1, ?_⟩
  rw [div_lt_div_iff₀ hsum hN]
  exact h2

/-- Eq. (3) (`sec:intro`): symmetric shrinkage bound when `W/N < r₀`. -/
theorem r_EB_strict_between_rev {W N N₀ r₀ : ℝ} (hN : 0 < N) (hN₀ : 0 < N₀) (hlt : W / N < r₀) :
    W / N < r_EB W N N₀ r₀ ∧ r_EB W N N₀ r₀ < r₀ := by
  have hsum : 0 < N + N₀ := by linarith
  unfold r_EB
  have h1 : W * (N + N₀) < (W + N₀ * r₀) * N := by
    have := (div_lt_iff₀ hN).mp hlt
    nlinarith
  have h2 : W + N₀ * r₀ < r₀ * (N + N₀) := by
    have := (div_lt_iff₀ hN).mp hlt
    linarith
  refine ⟨?_, (div_lt_iff₀ hsum).mpr h2⟩
  rw [div_lt_div_iff₀ hN hsum]
  exact h1

/-- Sec. 1 (`sec:intro`): for full careers (`N → ∞`), `r̂_EB` converges to the raw rate. -/
theorem r_EB_tendsto_rate {W : ℝ → ℝ} {N₀ r₀ r : ℝ} (hN₀ : 0 ≤ N₀)
    (hr : Tendsto (fun N => W N / N) atTop (𝓝 r)) :
    Tendsto (fun N => r_EB (W N) N N₀ r₀) atTop (𝓝 r) := by
  have h_eq : ∀ᶠ N : ℝ in atTop,
      r_EB (W N) N N₀ r₀ = (N / (N + N₀)) * (W N / N) + (N₀ * r₀) / (N + N₀) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
    have hsum : N + N₀ ≠ 0 := (by linarith : 0 < N + N₀).ne'
    unfold r_EB
    field_simp [hN.ne', hsum]
  have h_w1 : Tendsto (fun N : ℝ => N / (N + N₀)) atTop (𝓝 1) := by
    have h_inv : Tendsto (fun N : ℝ => (1 : ℝ) + N₀ / N) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
    have h_rec := h_inv.inv₀ (by norm_num : (1 + 0 : ℝ) ≠ 0)
    simp only [add_zero, inv_one] at h_rec
    refine h_rec.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
    have hsum : N + N₀ ≠ 0 := (by linarith : 0 < N + N₀).ne'
    field_simp [hN.ne', hsum]
  have h_w2 : Tendsto (fun N : ℝ => (N₀ * r₀) / (N + N₀)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_id.atTop_add tendsto_const_nhds)
  have h_lim := (h_w1.mul hr).add h_w2
  rw [one_mul, add_zero] at h_lim
  exact h_lim.congr' (EventuallyEq.symm h_eq)

/-! ### 15.2 Proposition 1 Strict Bounds & Remark 2 Running Maximum (`prop:alpha`, `rem:envelope`) -/

/-- Proposition 1 (`prop:alpha`): for `α ∈ (0, 1)` and `ΔN/N > 0`, the discrete threshold
factor lies strictly between `0` and `α`. -/
theorem prop_alpha_discrete_pos_lt_continuous {α x : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hx : 0 < x) :
    0 < ((1 + x) ^ α - 1) / x ∧ ((1 + x) ^ α - 1) / x < α := by
  have h1x : 1 < 1 + x := by linarith
  have hpow_gt : 1 < (1 + x) ^ α := Real.one_lt_rpow h1x hα0
  refine ⟨div_pos (sub_pos.mpr hpow_gt) hx, ?_⟩
  let f : ℝ → ℝ := fun t => (1 + t) ^ α
  let f' : ℝ → ℝ := fun t => α * (1 + t) ^ (α - 1)
  have hf_cont : ContinuousOn f (Icc 0 x) := by
    intro t ht
    have hpos : 0 < 1 + t := by linarith [ht.1]
    exact ((continuousAt_const.add continuousAt_id).rpow_const (Or.inl hpos.ne')).continuousWithinAt
  have hf_deriv : ∀ t ∈ Ioo 0 x, HasDerivAt f (f' t) t := by
    intro t ht
    have hpos : 0 < 1 + t := by linarith [ht.1]
    have hd := (hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)
    simpa [f, f'] using hd.rpow_const (Or.inl hpos.ne')
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f f' hx hf_cont hf_deriv
  have h1 : f 0 = 1 := by simp [f]
  have h2 : f x = (1 + x) ^ α := rfl
  rw [h2, h1, sub_zero] at hslope
  rw [← hslope]
  have hc1 : 1 < 1 + c := by linarith [hc.1]
  have hpow_lt : (1 + c) ^ (α - 1) < 1 := by
    simpa using Real.rpow_lt_one_of_one_lt_of_neg hc1 (sub_neg.mpr hα1)
  calc f' c = α * (1 + c) ^ (α - 1) := rfl
    _ < α * 1 := mul_lt_mul_of_pos_left hpow_lt hα0
    _ = α := mul_one α

/-- Proposition 1 (`prop:alpha`, Eq. 6): right-hand limit (`ΔN/N > 0`) Taylor remainder. -/
theorem prop_alpha_taylor_isBigO_nhdsGT (α : ℝ) :
    (fun x : ℝ => ((1 + x) ^ α - 1) / x - (α - α * (1 - α) / 2 * x))
      =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ 2) :=
  (prop_alpha_taylor_isBigO α).mono (nhdsWithin_mono 0 fun _ ht => (lt_of_lt_of_le ht le_rfl).ne')

/-- Remark 2 (`rem:envelope`): running maximum over qualifying season-end checkpoints dominates
every checkpoint score (in particular the career-end score). -/
theorem rem_envelope_ge_terminal {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (W N : ι → ℝ) (α : ℝ) {i : ι} (hi : i ∈ s) :
    Z_alpha (W i) (N i) α ≤ s.sup' hs (fun j => Z_alpha (W j) (N j) α) :=
  Finset.le_sup' (fun j => Z_alpha (W j) (N j) α) hi

/-- Remark 2 (`rem:envelope`): unlike `Z_α`, the running maximum `Z_α^*` depends on
season order and rewards early peaks (two 2-season careers with identical totals `(10, 200)`
but reversed order have identical terminal `Z_α` yet strictly different `Z_α^*` for `α > 0`). -/
theorem rem_envelope_order_dependent {α : ℝ} (hα : 0 < α) :
    let early_max := max (Z_alpha 10 100 α) (Z_alpha 10 200 α)
    let late_max := max (Z_alpha 0 100 α) (Z_alpha 10 200 α)
    Z_alpha (10 + 0) (100 + 100) α = Z_alpha (0 + 10) (100 + 100) α ∧
      late_max < early_max := by
  intro early_max late_max
  refine ⟨by norm_num, ?_⟩
  have hZ0 : Z_alpha 0 100 α = 0 := by simp [Z_alpha]
  have hZ10_200_pos : 0 < Z_alpha 10 200 α := by unfold Z_alpha; positivity
  have hpow : (100 : ℝ) ^ α < (200 : ℝ) ^ α :=
    Real.rpow_lt_rpow (by norm_num) (by norm_num) hα
  have hZ_lt : Z_alpha 10 200 α < Z_alpha 10 100 α := by
    unfold Z_alpha
    exact div_lt_div_of_pos_left (by norm_num) (Real.rpow_pos_of_pos (by norm_num) α) hpow
  have hlate : late_max = Z_alpha 10 200 α := by
    dsimp [late_max]
    rw [hZ0]
    exact max_eq_right hZ10_200_pos.le
  have hearly : early_max = Z_alpha 10 100 α := by
    dsimp [early_max]
    exact max_eq_left hZ_lt.le
  rw [hlate, hearly]
  exact hZ_lt

/-! ### 15.3 Proposition 2 Forecast Independence & Clipped Correlation Unimodality (Sec. 3.2) -/

section TargetScalingProb

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- Section 3.2 (`sec:target`): under conditional independence of future rate `r_f` and
future exposure `N_f`, `log E[r_f N_f] = κ log W + (β - κ) log N + log(c₁ c₂)`. -/
theorem prop_target_forecast_indep_expectation (r_f N_f : Ω → ℝ)
    {W N c₁ c₂ κ β : ℝ} (hW : 0 < W) (hN : 0 < N) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hindep : IndepFun r_f N_f μ)
    (hr_meas : AEStronglyMeasurable r_f μ) (hN_meas : AEStronglyMeasurable N_f μ)
    (hr_mean : ∫ ω, r_f ω ∂μ = c₁ * (W / N) ^ κ)
    (hN_mean : ∫ ω, N_f ω ∂μ = c₂ * N ^ β) :
    ∫ ω, r_f ω * N_f ω ∂μ = c₁ * (W / N) ^ κ * (c₂ * N ^ β) ∧
      Real.log (∫ ω, r_f ω * N_f ω ∂μ) =
        κ * Real.log W + (β - κ) * Real.log N + Real.log (c₁ * c₂) := by
  have hint : ∫ ω, r_f ω * N_f ω ∂μ = c₁ * (W / N) ^ κ * (c₂ * N ^ β) := by
    rw [hindep.integral_fun_mul_eq_mul_integral hr_meas hN_meas]
    change (∫ ω, r_f ω ∂μ) * (∫ ω, N_f ω ∂μ) = _
    rw [hr_mean, hN_mean]
  refine ⟨hint, ?_⟩
  rw [hint]
  exact prop_target_forecast_log hW hN hc₁ hc₂

end TargetScalingProb

section TargetClippedMax

open scoped RealInnerProductSpace

private lemma noncollinear_quad_pos {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X Z : E} (hnc : 0 < ‖X‖ ^ 2 * ‖Z‖ ^ 2 - ⟪X, Z⟫ ^ 2) (α : ℝ) :
    0 < ‖X‖ ^ 2 - 2 * α * ⟪X, Z⟫ + α ^ 2 * ‖Z‖ ^ 2 := by
  have hZpos : 0 < ‖Z‖ ^ 2 := by
    have hmul : 0 < ‖X‖ ^ 2 * ‖Z‖ ^ 2 := by linarith [sq_nonneg ⟪X, Z⟫]
    rcases (mul_pos_iff.mp hmul) with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact h2
    · exact absurd h2 (not_lt.mpr (sq_nonneg _))
  have hid : ‖Z‖ ^ 2 * (‖X‖ ^ 2 - 2 * α * ⟪X, Z⟫ + α ^ 2 * ‖Z‖ ^ 2) =
      (α * ‖Z‖ ^ 2 - ⟪X, Z⟫) ^ 2 + (‖X‖ ^ 2 * ‖Z‖ ^ 2 - ⟪X, Z⟫ ^ 2) := by ring
  have hrhs : 0 < (α * ‖Z‖ ^ 2 - ⟪X, Z⟫) ^ 2 + (‖X‖ ^ 2 * ‖Z‖ ^ 2 - ⟪X, Z⟫ ^ 2) := by
    linarith [sq_nonneg (α * ‖Z‖ ^ 2 - ⟪X, Z⟫)]
  have hmul_pos : 0 < ‖Z‖ ^ 2 * (‖X‖ ^ 2 - 2 * α * ⟪X, Z⟫ + α ^ 2 * ‖Z‖ ^ 2) := by
    rw [hid]; exact hrhs
  exact (mul_pos_iff_of_pos_left hZpos).mp hmul_pos

/-- Section 3.2 (`sec:target`): for non-collinear centered log-`W` and log-`N` vectors
`X, Z` and target direction `κ • (X - α* • Z)` (`κ > 0`), the cosine correlation
`⟪X - α • Z, T⟫ / (‖X - α • Z‖ * ‖T‖)` is strictly unimodal about `α*` (strictly increasing on
`(-∞, α*]`, strictly decreasing on `[α*, ∞)`), attains `1` uniquely at `α*`, and on `[0, 1]`
is uniquely maximized at the clipped exponent `max 0 (min 1 α*)`. -/
theorem prop_target_corr_unimodal_clipped_max {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {X Z : E}
    (hnc : 0 < ‖X‖ ^ 2 * ‖Z‖ ^ 2 - ⟪X, Z⟫ ^ 2) {κ α_star : ℝ} (hκ : 0 < κ) :
    let T : E := κ • (X - α_star • Z)
    let corr : ℝ → ℝ := fun α => ⟪X - α • Z, T⟫ / (‖X - α • Z‖ * ‖T‖)
    StrictMonoOn corr (Iic α_star) ∧
    StrictAntiOn corr (Ici α_star) ∧
    corr α_star = 1 ∧
    (∀ α : ℝ, α ≠ α_star → corr α < 1) ∧
    (let α_clip := max (0 : ℝ) (min (1 : ℝ) α_star)
     α_clip ∈ Icc (0 : ℝ) 1 ∧ ∀ α ∈ Icc (0 : ℝ) 1, α ≠ α_clip → corr α < corr α_clip) := by
  intro T corr
  set A : ℝ := ‖X‖ ^ 2
  set B : ℝ := ⟪X, Z⟫
  set C : ℝ := ‖Z‖ ^ 2
  set D : ℝ := A * C - B ^ 2
  have hD : 0 < D := hnc
  have hv_pos : ∀ α : ℝ, 0 < A - 2 * α * B + α ^ 2 * C := fun α => noncollinear_quad_pos hnc α
  have hZX : ⟪Z, X⟫ = B := real_inner_comm X Z
  have hnorm_sq : ∀ α : ℝ, ‖X - α • Z‖ ^ 2 = A - 2 * α * B + α ^ 2 * C := by
    intro α
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    change ‖X‖ ^ 2 - 2 * (α * ⟪X, Z⟫) + α ^ 2 * ‖Z‖ ^ 2 = A - 2 * α * B + α ^ 2 * C
    simp only [A, B, C]
    ring
  have hnorm_pos : ∀ α : ℝ, 0 < ‖X - α • Z‖ := fun α => by
    have hsq := hnorm_sq α
    have hpos := hv_pos α
    rw [← hsq] at hpos
    exact (sq_pos_iff.mp hpos |> abs_pos.mpr |> fun h => by rwa [abs_of_nonneg (norm_nonneg _)] at h)
  have hTnorm : 0 < ‖T‖ := by
    dsimp [T]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hκ]
    exact mul_pos hκ (hnorm_pos α_star)
  have hinner_eq : ∀ α : ℝ, ⟪X - α • Z, T⟫ = κ * (A - (α + α_star) * B + α * α_star * C) := by
    intro α
    dsimp [T]
    rw [real_inner_smul_right, inner_sub_left, inner_sub_right, inner_sub_right,
        real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
        real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    rw [show ⟪Z, X⟫ = B from hZX, show ⟪X, Z⟫ = B from rfl]
    simp only [A, C]
    ring
  let g : ℝ → ℝ := fun α => (A - (α + α_star) * B + α * α_star * C) / Real.sqrt (A - 2 * α * B + α ^ 2 * C)
  have hcorr_eq : ∀ α : ℝ, corr α = (κ / ‖T‖) * g α := by
    intro α
    dsimp [corr, g]
    rw [hinner_eq α, ← Real.sqrt_sq (norm_nonneg (X - α • Z)), hnorm_sq α]
    ring
  have hg_deriv : ∀ α : ℝ, HasDerivAt g
      ((α_star - α) * D / ((A - 2 * α * B + α ^ 2 * C) * Real.sqrt (A - 2 * α * B + α ^ 2 * C))) α := by
    intro α
    let u : ℝ → ℝ := fun t => A - (t + α_star) * B + t * α_star * C
    let v : ℝ → ℝ := fun t => A - 2 * t * B + t ^ 2 * C
    have hu : HasDerivAt u (-B + α_star * C) α := by
      have h1 : HasDerivAt (fun t : ℝ => A - (t + α_star) * B) (-B) α := by
        have ht := ((hasDerivAt_id α).add_const α_star).mul_const B
        simpa using (hasDerivAt_const α A).sub ht
      have h2 : HasDerivAt (fun t : ℝ => t * α_star * C) (α_star * C) α := by
        simpa [mul_assoc] using (hasDerivAt_id α).mul_const (α_star * C)
      convert h1.add h2 using 1
    have hv : HasDerivAt v (-2 * B + 2 * α * C) α := by
      have h1 : HasDerivAt (fun t : ℝ => A - 2 * t * B) (-2 * B) α := by
        have ht : HasDerivAt (fun t : ℝ => 2 * t * B) (2 * B) α := by
          convert ((hasDerivAt_id α).const_mul 2).mul_const B using 1
          ring
        simpa using (hasDerivAt_const α A).sub ht
      have h2 : HasDerivAt (fun t : ℝ => t ^ 2 * C) (2 * α * C) α := by
        have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * α) α := by
          simpa using (hasDerivAt_id α).pow 2
        simpa using hsq.mul_const C
      convert h1.add h2 using 1
    have hv_ne : v α ≠ 0 := (hv_pos α).ne'
    have hsqrt_v : HasDerivAt (fun t : ℝ => Real.sqrt (v t))
        ((-2 * B + 2 * α * C) / (2 * Real.sqrt (v α))) α := hv.sqrt hv_ne
    have hs_ne : Real.sqrt (v α) ≠ 0 := (Real.sqrt_pos.mpr (hv_pos α)).ne'
    have hdiv := hu.div hsqrt_v hs_ne
    have hderiv_eq :
        ((-B + α_star * C) * Real.sqrt (v α) - u α * ((-2 * B + 2 * α * C) / (2 * Real.sqrt (v α)))) /
          Real.sqrt (v α) ^ 2 =
        (α_star - α) * D / ((A - 2 * α * B + α ^ 2 * C) * Real.sqrt (A - 2 * α * B + α ^ 2 * C)) := by
      have hsq2 : Real.sqrt (v α) ^ 2 = v α := Real.sq_sqrt (hv_pos α).le
      have hmul :
          ((-B + α_star * C) * Real.sqrt (v α) - u α * ((-2 * B + 2 * α * C) / (2 * Real.sqrt (v α)))) /
            Real.sqrt (v α) ^ 2 =
          (((-B + α_star * C) * Real.sqrt (v α) ^ 2 - u α * (-B + α * C)) /
            (Real.sqrt (v α) ^ 2 * Real.sqrt (v α))) := by
        field_simp [hs_ne]
      rw [hmul, hsq2]
      dsimp [u, v, D]
      have hid : (-B + α_star * C) * (A - 2 * α * B + α ^ 2 * C) -
          (A - (α + α_star) * B + α * α_star * C) * (-B + α * C) =
          (α_star - α) * (A * C - B ^ 2) := by ring
      rw [hid]
    rw [← hderiv_eq]
    exact hdiv
  have hg_cont : Continuous g := continuous_iff_continuousAt.mpr fun α => (hg_deriv α).continuousAt
  have hg_mono : StrictMonoOn g (Iic α_star) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos
      (f' := fun α =>
        (α_star - α) * D / ((A - 2 * α * B + α ^ 2 * C) * Real.sqrt (A - 2 * α * B + α ^ 2 * C)))
      (convex_Iic α_star) hg_cont.continuousOn ?_ ?_
    · intro α hα
      rw [interior_Iic] at hα
      exact (hg_deriv α).hasDerivWithinAt
    · intro α hα
      rw [interior_Iic] at hα
      have hdiff : 0 < α_star - α := sub_pos.mpr hα
      exact div_pos (mul_pos hdiff hD) (mul_pos (hv_pos α) (Real.sqrt_pos.mpr (hv_pos α)))
  have hg_anti : StrictAntiOn g (Ici α_star) := by
    refine strictAntiOn_of_hasDerivWithinAt_neg
      (f' := fun α =>
        (α_star - α) * D / ((A - 2 * α * B + α ^ 2 * C) * Real.sqrt (A - 2 * α * B + α ^ 2 * C)))
      (convex_Ici α_star) hg_cont.continuousOn ?_ ?_
    · intro α hα
      rw [interior_Ici] at hα
      exact (hg_deriv α).hasDerivWithinAt
    · intro α hα
      rw [interior_Ici] at hα
      have hdiff : α_star - α < 0 := sub_neg.mpr hα
      exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hdiff hD)
        (mul_pos (hv_pos α) (Real.sqrt_pos.mpr (hv_pos α)))
  have hcorr_mono : StrictMonoOn corr (Iic α_star) := by
    intro a ha b hb hab
    rw [hcorr_eq a, hcorr_eq b]
    exact mul_lt_mul_of_pos_left (hg_mono ha hb hab) (div_pos hκ hTnorm)
  have hcorr_anti : StrictAntiOn corr (Ici α_star) := by
    intro a ha b hb hab
    rw [hcorr_eq a, hcorr_eq b]
    exact mul_lt_mul_of_pos_left (hg_anti ha hb hab) (div_pos hκ hTnorm)
  have h_at_star : corr α_star = 1 := by
    dsimp [corr, T]
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, abs_of_pos hκ]
    have hn : ‖X - α_star • Z‖ ≠ 0 := (hnorm_pos α_star).ne'
    field_simp [hκ.ne', hn]
  have h_lt_star : ∀ α : ℝ, α ≠ α_star → corr α < 1 := by
    intro α hne
    rw [← h_at_star]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hcorr_mono hlt.le Set.right_mem_Iic hlt
    · exact hcorr_anti Set.left_mem_Ici hgt.le hgt
  refine ⟨hcorr_mono, hcorr_anti, h_at_star, h_lt_star, ?_⟩
  intro α_clip
  have hclip_mem : α_clip ∈ Icc (0 : ℝ) 1 := ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  refine ⟨hclip_mem, fun α hα hne => ?_⟩
  rcases le_total α_star 0 with hle0 | hge0
  · have hclip0 : α_clip = 0 := by
      dsimp [α_clip]
      have hmin : min (1 : ℝ) α_star = α_star := min_eq_right (by linarith)
      rw [hmin, max_eq_left hle0]
    rw [hclip0] at hne ⊢
    have hα_pos : 0 < α := lt_of_le_of_ne hα.1 hne.symm
    exact hcorr_anti hle0 (hle0.trans hα.1) hα_pos
  · rcases le_total α_star 1 with hle1 | hge1
    · have hclip_star : α_clip = α_star := by
        dsimp [α_clip]
        rw [min_eq_right hle1, max_eq_right hge0]
      rw [hclip_star] at hne ⊢
      rw [h_at_star]
      exact h_lt_star α hne
    · have hclip1 : α_clip = 1 := by
        dsimp [α_clip]
        rw [min_eq_left hge1]
        norm_num
      rw [hclip1] at hne ⊢
      have hα_lt1 : α < 1 := lt_of_le_of_ne hα.2 hne
      exact hcorr_mono (hα.2.trans hge1) hge1 hα_lt1

end TargetClippedMax

/-! ### 15.4 Proposition 3 Discrete `N`, Noise Boundary, & OLS Varying-Rate Bias (Sec. 3.3) -/

section FrequentistExt

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Proposition 3(b) (`prop:frequentist`): homoscedasticity over integer exposure counts
`N ≥ 1` already forces `α = 1/2`. -/
theorem prop_frequentist_part_b_nat {σ α : ℝ} (hσ : 0 < σ) :
    (∀ N₁ N₂ : ℕ, 1 ≤ N₁ → 1 ≤ N₂ →
      σ * (N₁ : ℝ) ^ ((1 / 2 : ℝ) - α) = σ * (N₂ : ℝ) ^ ((1 / 2 : ℝ) - α)) ↔ α = 1 / 2 := by
  constructor
  · intro h
    have heq := h 2 1 (by omega) (by omega)
    simp only [Nat.cast_ofNat, Nat.cast_one, Real.one_rpow, mul_one] at heq
    rw [← mul_one σ, mul_assoc, one_mul, mul_left_cancel_iff_of_pos hσ] at heq
    by_contra hne
    have hexp : (1 / 2 : ℝ) - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    rcases lt_or_gt_of_ne hexp with hlt | hgt
    · have : (2 : ℝ) ^ ((1 / 2 : ℝ) - α) < (2 : ℝ) ^ (0 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hlt
      rw [Real.rpow_zero] at this
      linarith
    · have : (2 : ℝ) ^ (0 : ℝ) < (2 : ℝ) ^ ((1 / 2 : ℝ) - α) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hgt
      rw [Real.rpow_zero] at this
      linarith
  · rintro rfl N₁ N₂ _ _
    simp

/-- Section 3.3 (`sec:zstat`): for ANY proportionality constant `c > 0`, if
`SD(W) = c n^α` with `α < 1/2`, then for sufficiently large `n`, negative pairwise covariance
`Cov(w_i, w_j) < 0` is required. -/
theorem prop_frequentist_sub_sqrt_sd_general_const {n : ℕ} (hn : 1 ≤ n) (w : Fin n → Ω → ℝ)
    {c σ α : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hα : α < 1 / 2)
    (hlarge : (c / σ) ^ (2 / (1 - 2 * α)) < (n : ℝ))
    (hL2 : ∀ i, MemLp (w i) 2 μ)
    (hvar : ∀ i, variance (w i) μ = σ ^ 2)
    (hsd : Real.sqrt (variance (fun ω => ∑ i, w i ω) μ) = c * (n : ℝ) ^ α) :
    ∃ i j, i ≠ j ∧ cov[w i, w j; μ] < 0 := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h12α : 0 < 1 - 2 * α := by linarith
  have hvar_eq : variance (fun ω => ∑ i, w i ω) μ = c ^ 2 * (n : ℝ) ^ (2 * α) := by
    have hsq := congrArg (· ^ 2) hsd
    dsimp only at hsq
    rw [Real.sq_sqrt (variance_nonneg _ _), mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ α) 2,
        ← Real.rpow_mul hn_pos.le] at hsq
    rw [show α * ((2 : ℕ) : ℝ) = 2 * α by ring] at hsq
    exact hsq
  have hpow_lt : (c / σ) ^ (2 : ℝ) < (n : ℝ) ^ (1 - 2 * α) := by
    have hr := Real.rpow_lt_rpow (by positivity) hlarge h12α
    rw [← Real.rpow_mul (div_pos hc hσ).le] at hr
    have hexp : 2 / (1 - 2 * α) * (1 - 2 * α) = 2 := by field_simp [h12α.ne']
    rwa [hexp] at hr
  have hlt : variance (fun ω => ∑ i, w i ω) μ < (n : ℝ) * σ ^ 2 := by
    rw [hvar_eq]
    rw [Real.rpow_two, div_pow, div_lt_iff₀ (sq_pos_of_pos hσ)] at hpow_lt
    have hmul := mul_lt_mul_of_pos_right hpow_lt (Real.rpow_pos_of_pos hn_pos (2 * α))
    have hn_split : (n : ℝ) ^ (1 - 2 * α) * (n : ℝ) ^ (2 * α) = (n : ℝ) := by
      rw [← Real.rpow_add hn_pos, sub_add_cancel, Real.rpow_one]
    calc c ^ 2 * (n : ℝ) ^ (2 * α)
        < σ ^ 2 * (n : ℝ) ^ (1 - 2 * α) * (n : ℝ) ^ (2 * α) := by
          linarith [hmul]
      _ = σ ^ 2 * ((n : ℝ) ^ (1 - 2 * α) * (n : ℝ) ^ (2 * α)) := by ring
      _ = (n : ℝ) * σ ^ 2 := by rw [hn_split]; ring
  exact prop_frequentist_sublinear_var_exists_neg_cov w hL2 hvar hlt

/-- Section 3.3 (`sec:zstat`): when true per-event rates `r_j` vary across seasons,
the constant-rate OLS residual sum of squares absorbs the rate dispersion
`(1 / N_tot) ∑_{j<k} N_j N_k (r_j - r_k)^2 ≥ 0`, estimating `σ^2` conservatively
(strictly upward whenever rates are not constant). -/
theorem ols_rss_varying_rate_bias {m : ℕ} (hm : 0 < m) (W : Fin m → Ω → ℝ) (N r : Fin m → ℝ)
    {σ : ℝ} (hN : ∀ j, 0 < N j)
    (hL2 : ∀ j, MemLp (W j) 2 μ)
    (hmean : ∀ j, ∫ ω, W j ω ∂μ = r j * N j)
    (hvar : ∀ j, variance (W j) μ = N j * σ ^ 2)
    (huncorr : ∀ j k, j ≠ k → cov[W j, W k; μ] = 0) :
    let RSS : Ω → ℝ := fun ω => ∑ j : Fin m, (W j ω / Real.sqrt (N j) -
        ((∑ i : Fin m, W i ω) / (∑ i : Fin m, N i)) * Real.sqrt (N j)) ^ 2
    let rate_disp : ℝ := (1 / ∑ i : Fin m, N i) *
        ∑ j : Fin m, ∑ k : Fin m with j < k, N j * N k * (r j - r k) ^ 2
    ∫ ω, RSS ω ∂μ = ((m : ℝ) - 1) * σ ^ 2 + rate_disp ∧
    ((m : ℝ) - 1) * σ ^ 2 ≤ ∫ ω, RSS ω ∂μ ∧
    ((∃ j k : Fin m, r j ≠ r k) → ((m : ℝ) - 1) * σ ^ 2 < ∫ ω, RSS ω ∂μ) := by
  intro RSS rate_disp
  let N_tot : ℝ := ∑ i : Fin m, N i
  have hN_tot_pos : 0 < N_tot := Finset.sum_pos (fun j _ => hN j)
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hpt : ∀ ω : Ω,
      RSS ω = (∑ j : Fin m, W j ω ^ 2 / N j) - (∑ i : Fin m, W i ω) ^ 2 / N_tot := by
    intro ω
    exact ols_constant_rate_rss_eq_lagrange Finset.univ (fun j => W j ω) N
      (fun j _ => hN j) hN_tot_pos.ne'
  have hint_sq : ∀ j, Integrable (fun ω => W j ω ^ 2) μ := fun j => by
    simpa [pow_two] using (hL2 j).integrable_mul (hL2 j)
  have hint_term : ∀ j, Integrable (fun ω => W j ω ^ 2 / N j) μ :=
    fun j => (hint_sq j).div_const (N j)
  have hW_sum_L2 : MemLp (fun ω => ∑ i : Fin m, W i ω) 2 μ :=
    memLp_finset_sum Finset.univ (fun i _ => hL2 i)
  have hint_sum_sq : Integrable (fun ω => (∑ i : Fin m, W i ω) ^ 2 / N_tot) μ := by
    have hsq : Integrable (fun ω => (∑ i : Fin m, W i ω) ^ 2) μ := by
      simpa [pow_two] using hW_sum_L2.integrable_mul hW_sum_L2
    exact hsq.div_const N_tot
  have hE_RSS : ∫ ω, RSS ω ∂μ =
      (∑ j : Fin m, ∫ ω, W j ω ^ 2 / N j ∂μ) - ∫ ω, (∑ i : Fin m, W i ω) ^ 2 / N_tot ∂μ := by
    simp_rw [hpt]
    rw [integral_sub (integrable_finset_sum _ fun j _ => hint_term j) hint_sum_sq,
        integral_finset_sum _ fun j _ => hint_term j]
  have hE_term : ∀ j : Fin m, ∫ ω, W j ω ^ 2 / N j ∂μ = σ ^ 2 + (r j * N j) ^ 2 / N j := by
    intro j
    rw [integral_div, show ∫ ω, W j ω ^ 2 ∂μ = μ[W j ^ 2] from rfl]
    have hv := variance_eq_sub (hL2 j)
    have hsq : μ[W j ^ 2] = N j * σ ^ 2 + (r j * N j) ^ 2 := by
      rw [hvar j, show μ[W j] = r j * N j from hmean j] at hv
      linarith
    rw [hsq]
    field_simp [(hN j).ne']
  have hE_sum : ∫ ω, (∑ i : Fin m, W i ω) ∂μ = ∑ i : Fin m, r i * N i := by
    rw [integral_finset_sum _ fun i _ => (hL2 i).integrable one_le_two]
    exact Finset.sum_congr rfl fun i _ => hmean i
  have hV_sum : variance (fun ω => ∑ i : Fin m, W i ω) μ = N_tot * σ ^ 2 := by
    rw [variance_fun_sum hL2]
    have hinner : ∀ i : Fin m, ∑ k : Fin m, cov[W i, W k; μ] = N i * σ ^ 2 := by
      intro i
      rw [Finset.sum_eq_single i]
      · rw [covariance_self (hL2 i).aemeasurable, hvar i]
      · intro k _ hki; exact huncorr i k hki.symm
      · intro hi; exact absurd (Finset.mem_univ i) hi
    simp_rw [hinner]
    dsimp only [N_tot]
    rw [Finset.sum_mul]
  have hE_tot_term :
      ∫ ω, (∑ i : Fin m, W i ω) ^ 2 / N_tot ∂μ = σ ^ 2 + (∑ i : Fin m, r i * N i) ^ 2 / N_tot := by
    rw [integral_div]
    have hv := variance_eq_sub hW_sum_L2
    change variance (fun ω => ∑ i : Fin m, W i ω) μ =
        (∫ ω, (∑ i : Fin m, W i ω) ^ 2 ∂μ) - (∫ ω, (∑ i : Fin m, W i ω) ∂μ) ^ 2 at hv
    have hsq : ∫ ω, (∑ i : Fin m, W i ω) ^ 2 ∂μ =
        N_tot * σ ^ 2 + (∑ i : Fin m, r i * N i) ^ 2 := by
      rw [hV_sum, hE_sum] at hv
      linarith
    rw [hsq]
    field_simp [hN_tot_pos.ne']
  have hlag := rem_partition_ordered_pairs Finset.univ (fun j => r j * N j) N
    (fun j _ => hN j) hN_tot_pos
  have hrate_id :
      (∑ j : Fin m, (r j * N j) ^ 2 / N j) - (∑ i : Fin m, r i * N i) ^ 2 / N_tot = rate_disp := by
    rw [hlag]
    dsimp [rate_disp, N_tot]
    congr 1
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    have hj : (r j * N j) / N j = r j := mul_div_cancel_right₀ _ (hN j).ne'
    have hk : (r k * N k) / N k = r k := mul_div_cancel_right₀ _ (hN k).ne'
    rw [hj, hk]
  have hEq : ∫ ω, RSS ω ∂μ = ((m : ℝ) - 1) * σ ^ 2 + rate_disp := by
    rw [hE_RSS]
    simp_rw [hE_term, hE_tot_term, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
             Fintype.card_fin, nsmul_eq_mul]
    rw [← hrate_id]
    ring
  have hdisp_nn : 0 ≤ rate_disp := by
    dsimp [rate_disp]
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_)
    exact mul_nonneg (mul_nonneg (hN j).le (hN k).le) (sq_nonneg _)
  refine ⟨hEq, by linarith, fun ⟨j, k, hjkr⟩ => ?_⟩
  have hstrict_disp : 0 < rate_disp := by
    dsimp [rate_disp]
    refine mul_pos (one_div_pos.mpr hN_tot_pos) ?_
    let f : Fin m → Fin m → ℝ := fun a b => N a * N b * (r a - r b) ^ 2
    have hf_nn : ∀ a b : Fin m, 0 ≤ f a b := fun a b =>
      mul_nonneg (mul_nonneg (hN a).le (hN b).le) (sq_nonneg _)
    have hpair_le : ∀ a b : Fin m, a < b →
        f a b ≤ ∑ i : Fin m, ∑ l : Fin m with i < l, f i l := by
      intro a b hab
      have h1 : f a b ≤ ∑ l ∈ Finset.univ.filter (fun l : Fin m => a < l), f a l :=
        Finset.single_le_sum (fun l _ => hf_nn a l) (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hab⟩)
      have h2 : (∑ l ∈ Finset.univ.filter (fun l : Fin m => a < l), f a l) ≤
          ∑ i : Fin m, ∑ l ∈ Finset.univ.filter (fun l : Fin m => i < l), f i l :=
        Finset.single_le_sum
          (f := fun i => ∑ l ∈ Finset.univ.filter (fun l : Fin m => i < l), f i l)
          (fun i _ => Finset.sum_nonneg fun l _ => hf_nn i l) (Finset.mem_univ a)
      exact h1.trans h2
    rcases lt_trichotomy j k with hjk | rfl | hkj
    · have hterm_pos : 0 < f j k :=
        mul_pos (mul_pos (hN j) (hN k)) (sq_pos_of_ne_zero (sub_ne_zero.mpr hjkr))
      exact hterm_pos.trans_le (hpair_le j k hjk)
    · exact absurd rfl hjkr
    · have hterm_pos : 0 < f k j :=
        mul_pos (mul_pos (hN k) (hN j)) (sq_pos_of_ne_zero (sub_ne_zero.mpr hjkr.symm))
      exact hterm_pos.trans_le (hpair_le k j hkj)
  linarith

/-- Section 3.3 (`sec:zstat`): pooling residual sums of squares divided by total degrees
of freedom across players estimates `σ^2` conservatively whenever each player's expected RSS
is at least `(m_p - 1) σ^2`. -/
theorem ols_pooled_rss_conservative {ι : Type*} (P : Finset ι) (m : ι → ℕ) (E_RSS : ι → ℝ)
    {σ : ℝ} (hdf : 0 < ∑ p ∈ P, ((m p : ℝ) - 1))
    (hge : ∀ p ∈ P, ((m p : ℝ) - 1) * σ ^ 2 ≤ E_RSS p) :
    σ ^ 2 ≤ (∑ p ∈ P, E_RSS p) / (∑ p ∈ P, ((m p : ℝ) - 1)) ∧
    ((∃ p ∈ P, ((m p : ℝ) - 1) * σ ^ 2 < E_RSS p) →
      σ ^ 2 < (∑ p ∈ P, E_RSS p) / (∑ p ∈ P, ((m p : ℝ) - 1))) := by
  have hsum_le : (∑ p ∈ P, ((m p : ℝ) - 1)) * σ ^ 2 ≤ ∑ p ∈ P, E_RSS p := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hge
  refine ⟨(le_div_iff₀ hdf).mpr (by linarith), fun ⟨p0, hp0, hlt⟩ => ?_⟩
  rw [lt_div_iff₀ hdf]
  have hsum_lt : (∑ p ∈ P, ((m p : ℝ) - 1)) * σ ^ 2 < ∑ p ∈ P, E_RSS p := by
    rw [Finset.sum_mul]
    exact Finset.sum_lt_sum hge ⟨p0, hp0, hlt⟩
  linarith

end FrequentistExt

/-! ### 15.5 Season Value Ratios, Convexity Growth, & Cross-Role Scaling (Sec. 3.4, 4, 5.3) -/

/-- Section 3.4 (`sec:value`): general comparison between event-form `Z_α(W, E*S)` and
season-form `W / S^α`, showing the relative premium `(E₂ / E₁)^α` increases with `α` for `E₁ < E₂`. -/
theorem prop_gamma_season_vs_event_general_ratio {W₁ S₁ E₁ W₂ S₂ E₂ α : ℝ}
    (hS₁ : 0 < S₁) (hE₁ : 0 < E₁) (hS₂ : 0 < S₂) (hE₂ : 0 < E₂) (hW₂ : W₂ ≠ 0) :
    Z_alpha W₁ (E₁ * S₁) α / Z_alpha W₂ (E₂ * S₂) α =
      ((W₁ / S₁ ^ α) / (W₂ / S₂ ^ α)) * (E₂ / E₁) ^ α := by
  unfold Z_alpha
  rw [Real.mul_rpow hE₁.le hS₁.le, Real.mul_rpow hE₂.le hS₂.le, Real.div_rpow hE₂.le hE₁.le]
  have hS1p : S₁ ^ α ≠ 0 := (Real.rpow_pos_of_pos hS₁ α).ne'
  have hS2p : S₂ ^ α ≠ 0 := (Real.rpow_pos_of_pos hS₂ α).ne'
  have hE1p : E₁ ^ α ≠ 0 := (Real.rpow_pos_of_pos hE₁ α).ne'
  have hE2p : E₂ ^ α ≠ 0 := (Real.rpow_pos_of_pos hE₂ α).ne'
  field_simp [hS1p, hS2p, hE1p, hE2p, hW₂]

theorem prop_gamma_short_season_bonus_strictMono {E₁ E₂ : ℝ} (hE₁ : 0 < E₁) (hlt : E₁ < E₂) :
    StrictMono (fun α : ℝ => (E₂ / E₁) ^ α) :=
  fun _ _ hα => Real.rpow_lt_rpow_of_exponent_lt ((one_lt_div hE₁).mpr hlt) hα

/-- Sections 1, 3.4, & 4: doubling seasonal WAR scales value by `2^γ`,
equal to `4` at `α = 1/2` (`γ = 2`) and lying in `(2.37, 2.39)` (≈ `2.4`) at `α = 1/5` (`γ = 5/4`). -/
theorem season_value_double_ratio {s γ : ℝ} (hs : 0 < s) :
    (2 * s) ^ γ / s ^ γ = (2 : ℝ) ^ γ := by
  rw [Real.mul_rpow (by norm_num) hs.le]
  have hsγ : s ^ γ ≠ 0 := (Real.rpow_pos_of_pos hs γ).ne'
  field_simp [hsγ]

theorem season_value_double_benchmarks :
    (2 : ℝ) ^ gamma (1 / 2) = 4 ∧
      (237 / 100 : ℝ) < (2 : ℝ) ^ gamma (1 / 5) ∧ (2 : ℝ) ^ gamma (1 / 5) < (239 / 100 : ℝ) := by
  have hg_half : gamma (1 / 2 : ℝ) = 2 := by unfold gamma; norm_num
  have hg_fifth : gamma (1 / 5 : ℝ) = 5 / 4 := by unfold gamma; norm_num
  refine ⟨by rw [hg_half]; norm_num, ?_, ?_⟩
  · rw [hg_fifth]
    have hpow : ((237 / 100 : ℝ) ^ (4 : ℕ)) < (2 : ℝ) ^ (5 : ℕ) := by norm_num
    have hr := Real.rpow_lt_rpow (by norm_num) hpow (by norm_num : (0 : ℝ) < 1 / 4)
    have h1 : ((237 / 100 : ℝ) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) = 237 / 100 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    have h2 : ((2 : ℝ) ^ (5 : ℕ)) ^ (1 / 4 : ℝ) = (2 : ℝ) ^ (5 / 4 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    rwa [h1, h2] at hr
  · rw [hg_fifth]
    have hpow : (2 : ℝ) ^ (5 : ℕ) < (239 / 100 : ℝ) ^ (4 : ℕ) := by norm_num
    have hr := Real.rpow_lt_rpow (by norm_num) hpow (by norm_num : (0 : ℝ) < 1 / 4)
    have h1 : ((239 / 100 : ℝ) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) = 239 / 100 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    have h2 : ((2 : ℝ) ^ (5 : ℕ)) ^ (1 / 4 : ℝ) = (2 : ℝ) ^ (5 / 4 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    rwa [h1, h2] at hr

/-- Section 4 (`sec:gamma`): in the exponential/low-probability regime `g(s) = c (e^{bs} - 1)`
with `c, b > 0`, the log-log slope (local convexity exponent) `s g'(s)/g(s)` strictly rises with `s`. -/
theorem exp_gain_elasticity_strictMono {c b : ℝ} (hc : 0 < c) (hb : 0 < b) :
    StrictMonoOn (fun s : ℝ => s * (c * b * Real.exp (b * s)) / (c * (Real.exp (b * s) - 1)))
      (Ioi 0) := by
  let q : ℝ → ℝ := fun s => (b * s * Real.exp (b * s)) / (Real.exp (b * s) - 1)
  have h_eq : ∀ s ∈ Ioi (0 : ℝ),
      s * (c * b * Real.exp (b * s)) / (c * (Real.exp (b * s) - 1)) = q s := by
    intro s _
    dsimp [q]
    field_simp [hc.ne']
  have h_deriv : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivAt q
        (b * Real.exp (b * s) * (Real.exp (b * s) - 1 - b * s) / (Real.exp (b * s) - 1) ^ 2) s := by
    intro s (hs : 0 < s)
    have hden : Real.exp (b * s) - 1 ≠ 0 :=
      (sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos hb hs))).ne'
    have hbs : HasDerivAt (fun t : ℝ => b * t) b s := by
      simpa using (hasDerivAt_id s).const_mul b
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (b * t)) (Real.exp (b * s) * b) s :=
      (Real.hasDerivAt_exp (b * s)).comp s hbs
    have hnum : HasDerivAt (fun t : ℝ => b * t * Real.exp (b * t))
        (b * Real.exp (b * s) + (b * s) * (Real.exp (b * s) * b)) s :=
      hbs.mul hexp
    have hden_d : HasDerivAt (fun t : ℝ => Real.exp (b * t) - 1) (Real.exp (b * s) * b) s :=
      hexp.sub_const 1
    convert hnum.div hden_d hden using 1
    ring
  have hq_mono : StrictMonoOn q (Ioi 0) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioi (0 : ℝ))
      (f' := fun s => b * Real.exp (b * s) * (Real.exp (b * s) - 1 - b * s) /
        (Real.exp (b * s) - 1) ^ 2)
      (fun s hs => (h_deriv s hs).continuousAt.continuousWithinAt) ?_ ?_
    · intro s hs
      rw [interior_Ioi] at hs
      exact (h_deriv s hs).hasDerivWithinAt
    · intro s hs
      rw [interior_Ioi] at hs
      have hpos : 0 < b * s := mul_pos hb hs
      have hexp_gt : b * s + 1 < Real.exp (b * s) := Real.add_one_lt_exp hpos.ne'
      have hdiff_pos : 0 < Real.exp (b * s) - 1 - b * s := by linarith
      have hden_pos : 0 < (Real.exp (b * s) - 1) ^ 2 :=
        sq_pos_of_ne_zero (sub_pos.mpr (Real.one_lt_exp_iff.mpr hpos)).ne'
      exact div_pos (mul_pos (mul_pos hb (Real.exp_pos _)) hdiff_pos) hden_pos
  intro a ha b' hb' hab
  dsimp only
  rw [h_eq a ha, h_eq b' hb']
  exact hq_mono ha hb' hab

/-- Section 5.3 (`sec:hof`) & Remark 4 (`rem:mvp`): changing `α` shifts the relative
pitcher-to-hitter score ratio by `(N_H / N_P)^(α₂ - α₁)`, shrinking pitcher scores relative to
hitters when `N_H < N_P` and `α` increases. -/
theorem cross_role_ratio_scaling {W_P N_P W_H N_H α₁ α₂ : ℝ}
    (hN_P : 0 < N_P) (hN_H : 0 < N_H) (hW_H : W_H ≠ 0) :
    Z_alpha W_P N_P α₂ / Z_alpha W_H N_H α₂ =
      (N_H / N_P) ^ (α₂ - α₁) * (Z_alpha W_P N_P α₁ / Z_alpha W_H N_H α₁) := by
  unfold Z_alpha
  rw [Real.div_rpow hN_H.le hN_P.le, Real.rpow_sub hN_H, Real.rpow_sub hN_P]
  have h1 : N_P ^ α₁ ≠ 0 := (Real.rpow_pos_of_pos hN_P _).ne'
  have h2 : N_P ^ α₂ ≠ 0 := (Real.rpow_pos_of_pos hN_P _).ne'
  have h3 : N_H ^ α₁ ≠ 0 := (Real.rpow_pos_of_pos hN_H _).ne'
  have h4 : N_H ^ α₂ ≠ 0 := (Real.rpow_pos_of_pos hN_H _).ne'
  field_simp [h1, h2, h3, h4, hW_H]

/-! ### 15.6 Two-Way Symmetry, Negative Penalty, Regularity Details, & Null Calibration -/

lemma signedPow_neg_left (x p : ℝ) : signedPow (-x) p = -signedPow x p := by
  unfold signedPow
  rw [Real.sign_neg, abs_neg]
  ring

/-- Definition 1 (`def:twoway`): odd symmetry `Z_{α,2D}(-W₁, N₁, -W₂, N₂) = -Z_{α,2D}(W₁, N₁, W₂, N₂)`. -/
theorem Z_twoway_odd_symm (W₁ N₁ W₂ N₂ α : ℝ) :
    Z_twoway (-W₁) N₁ (-W₂) N₂ α = -Z_twoway W₁ N₁ W₂ N₂ α := by
  have hI : I_twoway (-W₁) N₁ (-W₂) N₂ α = -I_twoway W₁ N₁ W₂ N₂ α := by
    unfold I_twoway
    rw [signedPow_neg_left, signedPow_neg_left]
    ring
  unfold Z_twoway
  rw [hI, signedPow_neg_left]

/-- Proposition 5 (`prop:lagrange`) & Appendix E (`app:radon`): when both coordinates are
non-positive (`W₁, W₂ ≤ 0`), `Z_{α,2D} ≤ Z_{α,pool} ≤ 0` for EVERY `α ∈ [0, 1)`, with equality
for `α > 0` if and only if the two rates coincide. -/
theorem twoway_both_nonpos_le_zpool {W₁ N₁ W₂ N₂ α : ℝ}
    (hW₁ : W₁ ≤ 0) (hW₂ : W₂ ≤ 0) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (h0 : 0 ≤ α) (h1 : α < 1) :
    Z_twoway W₁ N₁ W₂ N₂ α ≤ Z_pool W₁ N₁ W₂ N₂ α ∧ Z_pool W₁ N₁ W₂ N₂ α ≤ 0 := by
  have hpos := twoway_ge_zpool_all_alpha (neg_nonneg.mpr hW₁) (neg_nonneg.mpr hW₂) hN₁ hN₂ h0 h1
  have htw : Z_twoway (-W₁) N₁ (-W₂) N₂ α = -Z_twoway W₁ N₁ W₂ N₂ α := Z_twoway_odd_symm W₁ N₁ W₂ N₂ α
  have hpl : Z_pool (-W₁) N₁ (-W₂) N₂ α = -Z_pool W₁ N₁ W₂ N₂ α := by
    unfold Z_pool; ring
  rw [htw, hpl] at hpos
  have hpl_nn : Z_pool W₁ N₁ W₂ N₂ α ≤ 0 := by
    unfold Z_pool
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (Real.rpow_pos_of_pos (add_pos hN₁ hN₂) α).le
  exact ⟨by linarith, hpl_nn⟩

theorem twoway_both_nonpos_eq_zpool_iff {W₁ N₁ W₂ N₂ α : ℝ}
    (hW₁ : W₁ ≤ 0) (hW₂ : W₂ ≤ 0) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (h0 : 0 < α) (h1 : α < 1) :
    Z_twoway W₁ N₁ W₂ N₂ α = Z_pool W₁ N₁ W₂ N₂ α ↔ W₁ / N₁ = W₂ / N₂ := by
  have heq := twoway_eq_zpool_iff (neg_nonneg.mpr hW₁) (neg_nonneg.mpr hW₂) hN₁ hN₂ h0 h1
  have htw : Z_twoway (-W₁) N₁ (-W₂) N₂ α = -Z_twoway W₁ N₁ W₂ N₂ α := Z_twoway_odd_symm W₁ N₁ W₂ N₂ α
  have hpl : Z_pool (-W₁) N₁ (-W₂) N₂ α = -Z_pool W₁ N₁ W₂ N₂ α := by
    unfold Z_pool; ring
  rw [htw, hpl, neg_inj] at heq
  rw [heq, neg_div, neg_div, neg_inj]

/-- Section 6.4 (`sec:twoway_empirical`): opposite-sign ratio formula when `W₁ > 0`, `W₂ ≤ 0`,
and `|Z₂| ≤ Z₁`: `Z_{α,2D} = Z₁ (1 - ρ^γ)^(1/γ)` where `ρ = (-Z₂)/Z₁`. -/
theorem twoway_opp_sign_ratio_exact {W₁ N₁ W₂ N₂ α : ℝ}
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hα : α < 1)
    (hW₁ : 0 < W₁) (hW₂ : W₂ ≤ 0)
    (hle : -Z_alpha W₂ N₂ α ≤ Z_alpha W₁ N₁ α) :
    let Z₁ := Z_alpha W₁ N₁ α
    let ρ := (-Z_alpha W₂ N₂ α) / Z₁
    Z_twoway W₁ N₁ W₂ N₂ α = Z₁ * (1 - ρ ^ gamma α) ^ (1 / gamma α) := by
  intro Z₁ ρ
  have hg : 0 < gamma α := gamma_pos hα
  have hinv : 0 < 1 / gamma α := one_div_pos.mpr hg
  have hZ₁ : 0 < Z₁ := by dsimp [Z₁, Z_alpha]; positivity
  have hZ₂ : Z_alpha W₂ N₂ α ≤ 0 := by
    unfold Z_alpha
    exact div_nonpos_of_nonpos_of_nonneg hW₂ (Real.rpow_pos_of_pos hN₂ α).le
  have hmZ₂ : 0 ≤ -Z_alpha W₂ N₂ α := neg_nonneg.mpr hZ₂
  have hρ_nn : 0 ≤ ρ := div_nonneg hmZ₂ hZ₁.le
  have hρ_le : ρ ≤ 1 := (div_le_one hZ₁).mpr hle
  have hρ_pow_le : ρ ^ gamma α ≤ 1 := by
    simpa using Real.rpow_le_one hρ_nn hρ_le hg.le
  have hI : I_twoway W₁ N₁ W₂ N₂ α = Z₁ ^ gamma α - (-Z_alpha W₂ N₂ α) ^ gamma α := by
    unfold I_twoway
    rw [twoway_I_alt_form hN₁ hα, twoway_I_alt_form hN₂ hα, signedPow_nonneg hZ₁.le hg]
    rcases eq_or_lt_of_le hZ₂ with h0 | hneg
    · rw [h0, neg_zero, signedPow_zero_left hg, Real.zero_rpow hg.ne', sub_zero, add_zero]
    · rw [signedPow_neg hneg]; ring
  have hInn : 0 ≤ I_twoway W₁ N₁ W₂ N₂ α := by
    rw [hI, sub_nonneg]
    exact Real.rpow_le_rpow hmZ₂ hle hg.le
  have hfac : Z₁ ^ gamma α - (-Z_alpha W₂ N₂ α) ^ gamma α = Z₁ ^ gamma α * (1 - ρ ^ gamma α) := by
    dsimp [ρ]
    rw [Real.div_rpow hmZ₂ hZ₁.le]
    have hZ1γ : Z₁ ^ gamma α ≠ 0 := (Real.rpow_pos_of_pos hZ₁ _).ne'
    field_simp [hZ1γ]
  unfold Z_twoway
  rw [signedPow_nonneg hInn hinv, hI, hfac,
      Real.mul_rpow (Real.rpow_pos_of_pos hZ₁ _).le (sub_nonneg.mpr hρ_pow_le),
      ← Real.rpow_mul hZ₁.le, mul_one_div_cancel hg.ne', Real.rpow_one]

/-- Section 6.4 (`sec:twoway_empirical`): for a fixed negative secondary ratio
`ρ ∈ (0, 1)`, `(1 - ρ^γ)^(1/γ)` strictly increases with `γ`, so smaller `γ` (such as `1.25`
vs. quadrature `2`) imposes a strictly larger fractional penalty `1 - (1 - ρ^γ)^(1/γ)`. -/
theorem neg_secondary_penalty_gamma_strictMono {ρ p q : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hp : 0 < p) (hpq : p < q) :
    (1 - ρ ^ p) ^ (1 / p) < (1 - ρ ^ q) ^ (1 / q) := by
  have hq : 0 < q := hp.trans hpq
  have hpow_lt : ρ ^ q < ρ ^ p := Real.rpow_lt_rpow_of_exponent_gt hρ0 hρ1 hpq
  have hbase_lt : 1 - ρ ^ p < 1 - ρ ^ q := by linarith
  have hp_lt1 : ρ ^ p < 1 := Real.rpow_lt_one hρ0.le hρ1 hp
  have hbase_pos : 0 < 1 - ρ ^ p := by linarith
  have hq_pos : 0 < ρ ^ q := Real.rpow_pos_of_pos hρ0 q
  have hbase2_lt1 : 1 - ρ ^ q < 1 := by linarith
  have h1 : (1 - ρ ^ p) ^ (1 / p) < (1 - ρ ^ q) ^ (1 / p) :=
    Real.rpow_lt_rpow hbase_pos.le hbase_lt (one_div_pos.mpr hp)
  have hexp_lt : 1 / q < 1 / p := one_div_lt_one_div_of_lt hp hpq
  have h2 : (1 - ρ ^ q) ^ (1 / p) < (1 - ρ ^ q) ^ (1 / q) :=
    Real.rpow_lt_rpow_of_exponent_gt (hbase_pos.trans hbase_lt) hbase2_lt1 hexp_lt
  exact h1.trans h2

/-- Section 6.4 & Appendix B: small-ratio asymptotic `(1 + u)^p - (1 + p u) = O(u^2)` as `u → 0`. -/
theorem one_add_rpow_first_order_isBigO (p : ℝ) :
    (fun u : ℝ => (1 + u) ^ p - (1 + p * u)) =O[𝓝 (0 : ℝ)] (fun u : ℝ => u ^ 2) := by
  have hbig := prop_alpha_taylor_isBigO p
  rw [Asymptotics.isBigO_iff] at hbig ⊢
  obtain ⟨c, hc⟩ := hbig
  refine ⟨max c 0 + |p * (1 - p) / 2|, ?_⟩
  rw [eventually_nhdsWithin_iff] at hc
  filter_upwards [hc, Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with u hu hball
  have hu1 : |u| ≤ 1 := by
    have hd : dist u 0 < 1 := Metric.mem_ball.mp hball
    rw [Real.dist_eq, sub_zero] at hd
    exact hd.le
  by_cases hu0 : u = 0
  · subst hu0; simp
  · have hbound := hu hu0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sq] at hbound ⊢
    have hid : (1 + u) ^ p - (1 + p * u) =
        u * (((1 + u) ^ p - 1) / u - (p - p * (1 - p) / 2 * u)) - (p * (1 - p) / 2) * u ^ 2 := by
      field_simp [hu0]
      ring
    have hc_le : |((1 + u) ^ p - 1) / u - (p - p * (1 - p) / 2 * u)| ≤ max c 0 * u ^ 2 :=
      hbound.trans (mul_le_mul_of_nonneg_right (le_max_left c 0) (sq_nonneg u))
    calc |(1 + u) ^ p - (1 + p * u)|
        ≤ |u * (((1 + u) ^ p - 1) / u - (p - p * (1 - p) / 2 * u))| + |(p * (1 - p) / 2) * u ^ 2| := by
          rw [hid]; exact abs_sub _ _
      _ = |u| * |((1 + u) ^ p - 1) / u - (p - p * (1 - p) / 2 * u)| + |p * (1 - p) / 2| * u ^ 2 := by
          rw [abs_mul, abs_mul, abs_sq]
      _ ≤ |u| * (max c 0 * u ^ 2) + |p * (1 - p) / 2| * u ^ 2 := by gcongr
      _ ≤ 1 * (max c 0 * u ^ 2) + |p * (1 - p) / 2| * u ^ 2 := by
          have hnn : 0 ≤ max c 0 * u ^ 2 := mul_nonneg (le_max_right c 0) (sq_nonneg u)
          nlinarith [hu1, hnn]
      _ = (max c 0 + |p * (1 - p) / 2|) * u ^ 2 := by ring

/-- Section 6.4 (`sec:twoway_empirical`): as `ρ → 0⁺`, `(1 + ρ^γ)^(1/γ) - (1 + ρ^γ / γ) = O(ρ^(2γ))`
and `(1 - ρ^γ)^(1/γ) - (1 - ρ^γ / γ) = O(ρ^(2γ))`. -/
theorem twoway_small_ratio_taylor {γ : ℝ} (hγ : 0 < γ) :
    (fun ρ : ℝ => (1 + ρ ^ γ) ^ (1 / γ) - (1 + (1 / γ) * ρ ^ γ))
      =O[𝓝[>] (0 : ℝ)] (fun ρ : ℝ => ρ ^ (2 * γ)) ∧
    (fun ρ : ℝ => (1 - ρ ^ γ) ^ (1 / γ) - (1 - (1 / γ) * ρ ^ γ))
      =O[𝓝[>] (0 : ℝ)] (fun ρ : ℝ => ρ ^ (2 * γ)) := by
  have h0 : Tendsto (fun ρ : ℝ => ρ ^ γ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous (fun ρ : ℝ => ρ ^ γ) := continuous_id.rpow_const fun _ => Or.inr hγ.le
    simpa [Real.zero_rpow hγ.ne'] using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hneg0 : Tendsto (fun ρ : ℝ => -(ρ ^ γ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using h0.neg
  have hbig := one_add_rpow_first_order_isBigO (1 / γ)
  have h1 : (fun ρ : ℝ => (1 + ρ ^ γ) ^ (1 / γ) - (1 + (1 / γ) * ρ ^ γ))
      =O[𝓝[>] (0 : ℝ)] (fun ρ : ℝ => (ρ ^ γ) ^ 2) := hbig.comp_tendsto h0
  have h2 : (fun ρ : ℝ => (1 - ρ ^ γ) ^ (1 / γ) - (1 - (1 / γ) * ρ ^ γ))
      =O[𝓝[>] (0 : ℝ)] (fun ρ : ℝ => (-(ρ ^ γ)) ^ 2) := by
    have hcomp := hbig.comp_tendsto hneg0
    refine hcomp.congr' ?_ EventuallyEq.rfl
    refine Eventually.of_forall fun ρ => ?_
    simp only [Function.comp_def, sub_eq_add_neg, mul_neg]
  have hsq : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (ρ ^ γ) ^ 2 = ρ ^ (2 * γ) := by
    filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
    rw [← Real.rpow_natCast (ρ ^ γ) 2, ← Real.rpow_mul hρ.le]
    ring_nf
  have hsq_neg : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (-(ρ ^ γ)) ^ 2 = ρ ^ (2 * γ) := by
    filter_upwards [hsq] with ρ hρ
    rw [neg_sq, hρ]
  refine ⟨h1.congr' EventuallyEq.rfl hsq, h2.congr' EventuallyEq.rfl hsq_neg⟩

/-- Appendix B (`app:twoway`): away from `0`, the second derivative of `signedPow x p`
is `sgn(x) * p * (p - 1) * |x|^(p - 2)`. -/
theorem signedPow_second_deriv_of_ne_zero {p x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => p * |t| ^ (p - 1))
      (Real.sign x * p * (p - 1) * |x| ^ (p - 2)) x := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hev : (fun t : ℝ => p * |t| ^ (p - 1)) =ᶠ[𝓝 x] fun t => p * (-t) ^ (p - 1) :=
      Filter.eventually_of_mem (Iio_mem_nhds hneg) fun t ht => by dsimp only; rw [abs_of_neg ht]
    have hd1 : HasDerivAt (fun t : ℝ => -t) (-1) x := by simpa using (hasDerivAt_id x).neg
    have hd2 : HasDerivAt (fun u : ℝ => u ^ (p - 1)) ((p - 1) * (-x) ^ (p - 1 - 1)) (-x) :=
      Real.hasDerivAt_rpow_const (Or.inl (neg_pos.mpr hneg).ne')
    have hcomp := (hd2.comp x hd1).const_mul p
    have heq : p * ((p - 1) * (-x) ^ (p - 1 - 1) * (-1)) =
        Real.sign x * p * (p - 1) * |x| ^ (p - 2) := by
      rw [Real.sign_of_neg hneg, abs_of_neg hneg, show p - 1 - 1 = p - 2 by ring]
      ring
    rw [heq] at hcomp
    exact hcomp.congr_of_eventuallyEq hev
  · have hev : (fun t : ℝ => p * |t| ^ (p - 1)) =ᶠ[𝓝 x] fun t => p * t ^ (p - 1) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hpos) fun t ht => by dsimp only; rw [abs_of_pos ht]
    have hd : HasDerivAt (fun t : ℝ => t ^ (p - 1)) ((p - 1) * x ^ (p - 1 - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hpos.ne')
    have hcomp := hd.const_mul p
    have heq : p * ((p - 1) * x ^ (p - 1 - 1)) =
        Real.sign x * p * (p - 1) * |x| ^ (p - 2) := by
      rw [Real.sign_of_pos hpos, abs_of_pos hpos, show p - 1 - 1 = p - 2 by ring]
      ring
    rw [heq] at hcomp
    exact hcomp.congr_of_eventuallyEq hev

/-- Appendix B (`app:twoway`): for `α ∈ (0, 1)` and `w ≠ 0`, the second partial derivative
of `I_{α,pos}` with respect to `W_pos` equals `sgn(w) γ (γ - 1) |w|^(γ - 2) / PA^(γ - 1)`. -/
theorem I_twoway_second_deriv_of_ne_zero {PA W_pitch BF α w : ℝ}
    (h0 : 0 < α) (h1 : α < 1) (hw : w ≠ 0) :
    HasDerivAt (deriv (fun t => I_twoway t PA W_pitch BF α))
      (Real.sign w * gamma α * (gamma α - 1) * |w| ^ (gamma α - 2) / PA ^ (gamma α - 1)) w := by
  have hg1 : 1 < gamma α := one_lt_gamma h0 h1
  have hderiv_eq : deriv (fun t => I_twoway t PA W_pitch BF α) =
      fun t => (gamma α * |t| ^ (gamma α - 1)) / PA ^ (gamma α - 1) := by
    ext t
    have hd : HasDerivAt (fun u => I_twoway u PA W_pitch BF α)
        (gamma α * |t| ^ (gamma α - 1) / PA ^ (gamma α - 1)) t := by
      unfold I_twoway
      exact ((signedPow_hasDerivAt hg1 t).div_const _).add_const _
    exact hd.deriv
  rw [hderiv_eq]
  exact (signedPow_second_deriv_of_ne_zero hw).div_const _

/-- Appendix B (`app:twoway`): for `α ∈ (0, 1/2)` (`1 < γ < 2`), the second derivative
of `I_{α,k}` diverges in magnitude to `+∞` as `W_k → 0` (`W_k ≠ 0`). -/
theorem I_twoway_second_deriv_diverges {PA W_pitch BF α : ℝ}
    (h0 : 0 < α) (hhalf : α < 1 / 2) (hPA : 0 < PA) :
    Tendsto (fun w : ℝ => |deriv (deriv (fun t => I_twoway t PA W_pitch BF α)) w|)
      (𝓝[≠] 0) atTop := by
  have h1 : α < 1 := by linarith
  have hg1 : 1 < gamma α := one_lt_gamma h0 h1
  have hg2 : gamma α < 2 := by
    unfold gamma
    rw [div_lt_iff₀ (sub_pos.mpr h1)]
    linarith
  have hc_pos : 0 < gamma α * (gamma α - 1) / PA ^ (gamma α - 1) := by
    exact div_pos (mul_pos (by linarith) (sub_pos.mpr hg1)) (Real.rpow_pos_of_pos hPA _)
  have hev : (fun w : ℝ => |deriv (deriv (fun t => I_twoway t PA W_pitch BF α)) w|) =ᶠ[𝓝[≠] 0]
      fun w => (gamma α * (gamma α - 1) / PA ^ (gamma α - 1)) * |w| ^ (-(2 - gamma α)) := by
    refine eventually_nhdsWithin_of_forall fun w (hw : w ≠ 0) => ?_
    dsimp only
    rw [(I_twoway_second_deriv_of_ne_zero h0 h1 hw).deriv]
    have hs : |Real.sign w| = 1 := by
      rcases lt_or_gt_of_ne hw with hn | hp
      · rw [Real.sign_of_neg hn]; norm_num
      · rw [Real.sign_of_pos hp]; norm_num
    rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hPA _), abs_mul, abs_mul, abs_mul, hs, one_mul,
        abs_of_pos (by linarith : 0 < gamma α), abs_of_pos (sub_pos.mpr hg1),
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg w) _)]
    have hexp : gamma α - 2 = -(2 - gamma α) := by ring
    rw [hexp]
    ring
  have h_abs_tend : Tendsto (fun w : ℝ => |w|) (𝓝[≠] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc := continuous_abs.continuousAt (x := (0 : ℝ))
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun w (hw : w ≠ 0) => abs_pos.mpr hw
  have hpow_tend : Tendsto (fun w : ℝ => |w| ^ (-(2 - gamma α))) (𝓝[≠] 0) atTop :=
    (tendsto_rpow_neg_nhdsGT_zero (by linarith : -(2 - gamma α) < 0)).comp h_abs_tend
  exact (hpow_tend.const_mul_atTop hc_pos).congr' hev.symm

/-- Appendix B (`app:twoway`): at `α = 1/2` (`γ = 2`), the second derivative of `I_{1/2,k}`
has a jump discontinuity of `4 / PA` at `W_k = 0` (`+2 / PA` for `w > 0`, `-2 / PA` for `w < 0`). -/
theorem I_twoway_second_deriv_jump_at_half {PA W_pitch BF : ℝ} (hPA : 0 < PA) :
    (∀ w : ℝ, 0 < w → deriv (deriv (fun t => I_twoway t PA W_pitch BF (1 / 2))) w = 2 / PA) ∧
    (∀ w : ℝ, w < 0 → deriv (deriv (fun t => I_twoway t PA W_pitch BF (1 / 2))) w = -(2 / PA)) ∧
    2 / PA - (-(2 / PA)) = 4 / PA ∧ 0 < 4 / PA := by
  have hg : gamma (1 / 2 : ℝ) = 2 := by unfold gamma; norm_num
  refine ⟨fun w hw => ?_, fun w hw => ?_, by ring, div_pos (by norm_num) hPA⟩
  · rw [(I_twoway_second_deriv_of_ne_zero (by norm_num) (by norm_num) hw.ne').deriv,
        Real.sign_of_pos hw, hg]
    norm_num
  · rw [(I_twoway_second_deriv_of_ne_zero (by norm_num) (by norm_num) hw.ne).deriv,
        Real.sign_of_neg hw, hg]
    norm_num
    ring

/-- Appendix B (`app:twoway`): a single-event secondary sample `(W₂, 1)` shifts an
unweighted sum `Z₁ + Z₂` by `W₂` (independent of `N₁`), whereas `Z_pool` shifts by at most
`W₂ / √(N₁ + 1)`. -/
theorem unweighted_single_event_shift (W₁ N₁ W₂ : ℝ) :
    (Z_alpha W₁ N₁ (1 / 2) + Z_alpha W₂ 1 (1 / 2)) - Z_alpha W₁ N₁ (1 / 2) = W₂ := by
  unfold Z_alpha
  simp

theorem zpool_single_event_shift_le {W₁ N₁ W₂ : ℝ} (hW₁ : 0 ≤ W₁) (hN₁ : 0 < N₁) :
    Z_pool W₁ N₁ W₂ 1 (1 / 2) - Z_alpha W₁ N₁ (1 / 2) ≤ W₂ / Real.sqrt (N₁ + 1) := by
  unfold Z_pool Z_alpha
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  have hs1 : Real.sqrt N₁ ≤ Real.sqrt (N₁ + 1) := Real.sqrt_le_sqrt (by linarith)
  have h1 : W₁ / Real.sqrt (N₁ + 1) ≤ W₁ / Real.sqrt N₁ := by
    rcases eq_or_lt_of_le hW₁ with rfl | hpos
    · simp
    · exact div_le_div_of_nonneg_left hW₁ (Real.sqrt_pos.mpr hN₁) hs1
  have hsplit : (W₁ + W₂) / Real.sqrt (N₁ + 1) =
      W₁ / Real.sqrt (N₁ + 1) + W₂ / Real.sqrt (N₁ + 1) := add_div _ _ _
  linarith

section NullCalibration

/-- Appendix B (`app:twoway`): pointwise and measure-level `χ²_2` over `χ²_1`
stochastic dominance `(Z₁²)/σ² ≤ (Z₁² + Z₂²)/σ²`. -/
theorem chi2_dominance_measure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z₁ Z₂ : Ω → ℝ) (σ t : ℝ) :
    μ {ω | t ≤ Z₁ ω ^ 2 / σ ^ 2} ≤ μ {ω | t ≤ (Z₁ ω ^ 2 + Z₂ ω ^ 2) / σ ^ 2} := by
  refine measure_mono fun ω hω => ?_
  dsimp only [Set.mem_setOf_eq] at hω ⊢
  have hadd : Z₁ ω ^ 2 / σ ^ 2 ≤ (Z₁ ω ^ 2 + Z₂ ω ^ 2) / σ ^ 2 :=
    div_le_div_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg _)) (sq_nonneg σ)
  exact hω.trans hadd

/-- Appendix B (`app:twoway`): for two independent non-degenerate centered Gaussians,
`(Z₁² + Z₂²)/σ²` strictly stochastically dominates `Z₁²/σ²` at every threshold `t > 0`. -/
theorem chi2_dominance_gaussian_strict (v : ℝ≥0) (hv : v ≠ 0) {σ t : ℝ}
    (hσ : 0 < σ) (ht : 0 < t) :
    let μp : Measure (ℝ × ℝ) := (gaussianReal 0 v).prod (gaussianReal 0 v)
    μp {p | t ≤ p.1 ^ 2 / σ ^ 2} < μp {p | t ≤ (p.1 ^ 2 + p.2 ^ 2) / σ ^ 2} := by
  intro μp
  let E₁ : Set (ℝ × ℝ) := {p | t ≤ p.1 ^ 2 / σ ^ 2}
  let E₂ : Set (ℝ × ℝ) := {p | t ≤ (p.1 ^ 2 + p.2 ^ 2) / σ ^ 2}
  let S : Set (ℝ × ℝ) := {p | p.1 ^ 2 / σ ^ 2 < t ∧ t ≤ (p.1 ^ 2 + p.2 ^ 2) / σ ^ 2}
  have hE₁_meas : MeasurableSet E₁ :=
    measurableSet_le measurable_const ((measurable_fst.pow_const 2).div_const _)
  have hE₂_meas : MeasurableSet E₂ :=
    measurableSet_le measurable_const
      (((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)).div_const _)
  have hS_meas : MeasurableSet S :=
    (measurableSet_lt ((measurable_fst.pow_const 2).div_const _) measurable_const).inter hE₂_meas
  have hdisj : Disjoint E₁ S := Set.disjoint_left.mpr fun p h1 h2 => not_lt_of_ge h1 h2.1
  have hunion : E₁ ∪ S = E₂ := by
    ext p
    simp only [Set.mem_union, Set.mem_setOf_eq, E₁, S, E₂]
    constructor
    · rintro (h | ⟨_, h⟩)
      · exact h.trans (div_le_div_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg _)) (sq_nonneg σ))
      · exact h
    · intro h
      by_cases h1 : t ≤ p.1 ^ 2 / σ ^ 2
      · exact Or.inl h1
      · exact Or.inr ⟨lt_of_not_ge h1, h⟩
  let a : ℝ := Real.sqrt t * σ
  have ha : 0 < a := mul_pos (Real.sqrt_pos.mpr ht) hσ
  let A : Set ℝ := Ioo 0 (a / 2)
  let B : Set ℝ := Ioo a (a + 1)
  have hrect_sub : A ×ˢ B ⊆ S := by
    intro ⟨x, y⟩ ⟨hx, hy⟩
    have hx_sq : x ^ 2 < (a / 2) ^ 2 := by
      have := sq_lt_sq' (by linarith [hx.1]) hx.2
      exact this
    have ha_sq : a ^ 2 = t * σ ^ 2 := by
      dsimp [a]; rw [mul_pow, Real.sq_sqrt ht.le]
    have hx_lt : x ^ 2 / σ ^ 2 < t := by
      rw [div_lt_iff₀ (sq_pos_of_pos hσ)]
      have h4 : (a / 2) ^ 2 < t * σ ^ 2 := by rw [div_pow, ha_sq]; linarith [mul_pos ht (sq_pos_of_pos hσ)]
      linarith
    have hy_sq : a ^ 2 < y ^ 2 := by
      have : a < y := hy.1
      nlinarith [ha, hy.1]
    have hxy_ge : t ≤ (x ^ 2 + y ^ 2) / σ ^ 2 := by
      rw [le_div_iff₀ (sq_pos_of_pos hσ)]
      nlinarith [sq_nonneg x, ha_sq, hy_sq]
    exact ⟨hx_lt, hxy_ge⟩
  have hvol_ac : volume ≪ gaussianReal 0 v := gaussianReal_absolutelyContinuous' 0 hv
  have hA_pos : 0 < gaussianReal 0 v A := by
    rw [pos_iff_ne_zero]
    intro h0
    have hv0 := hvol_ac h0
    have hvolA : ENNReal.ofReal (a / 2 - 0) = 0 := by
      rw [← Real.volume_Ioo (a := (0 : ℝ)) (b := a / 2)]
      exact hv0
    rw [sub_zero, ENNReal.ofReal_eq_zero] at hvolA
    linarith
  have hB_pos : 0 < gaussianReal 0 v B := by
    rw [pos_iff_ne_zero]
    intro h0
    have hv0 := hvol_ac h0
    have hvolB : volume B = ENNReal.ofReal ((a + 1) - a) := Real.volume_Ioo
    rw [hv0] at hvolB
    norm_num at hvolB
  have hrect_pos : 0 < μp (A ×ˢ B) := by
    dsimp [μp]
    rw [Measure.prod_prod]
    exact ENNReal.mul_pos hA_pos.ne' hB_pos.ne'
  have hS_pos : 0 < μp S := hrect_pos.trans_le (measure_mono hrect_sub)
  have h_add : μp E₂ = μp E₁ + μp S := by
    rw [← hunion, measure_union hdisj hS_meas]
  rw [h_add]
  exact ENNReal.lt_add_right (measure_ne_top μp E₁) hS_pos.ne'

end NullCalibration

/-! ### 15.7 Remark 5 General Partition Refinement, Appendix E Attainment & Quadrature Equivalence -/

/-- Remark 5 (`rem:partition`): for non-negative parts, ANY partition refinement
weakly raises the `ℓ_γ`-aggregated score `Z_{α,γ}` for every `α ∈ [0, 1)`. -/
theorem radon_refinement_le {ι κ : Type*} (s : Finset ι) (t : ι → Finset κ)
    (ht : ∀ j ∈ s, (t j).Nonempty) (W' N' : ι → κ → ℝ)
    {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1)
    (hW' : ∀ j ∈ s, ∀ l ∈ t j, 0 ≤ W' j l)
    (hN' : ∀ j ∈ s, ∀ l ∈ t j, 0 < N' j l) :
    let W : ι → ℝ := fun j => ∑ l ∈ t j, W' j l
    let N : ι → ℝ := fun j => ∑ l ∈ t j, N' j l
    (∑ j ∈ s, (Z_alpha (W j) (N j) α) ^ gamma α) ^ (1 / gamma α) ≤
      (∑ j ∈ s, ∑ l ∈ t j, (Z_alpha (W' j l) (N' j l) α) ^ gamma α) ^ (1 / gamma α) := by
  intro W N
  have hgpos : 0 < gamma α := gamma_pos h1
  have hpart : ∀ j ∈ s,
      (Z_alpha (W j) (N j) α) ^ gamma α ≤ ∑ l ∈ t j, (Z_alpha (W' j l) (N' j l) α) ^ gamma α := by
    intro j hj
    have hrad := radon_inequality (t j) (ht j hj) (W' j) (N' j) h0 h1
      (fun l hl => hW' j hj l hl) (fun l hl => hN' j hj l hl)
    change Z_alpha (W j) (N j) α ≤
      (∑ l ∈ t j, (Z_alpha (W' j l) (N' j l) α) ^ gamma α) ^ (1 / gamma α) at hrad
    have hZnn : 0 ≤ Z_alpha (W j) (N j) α := by
      unfold Z_alpha
      have hWn : 0 ≤ W j := Finset.sum_nonneg fun l hl => hW' j hj l hl
      have hNp : 0 < N j := Finset.sum_pos (fun l hl => hN' j hj l hl) (ht j hj)
      exact div_nonneg hWn (Real.rpow_pos_of_pos hNp α).le
    have hrpow := Real.rpow_le_rpow hZnn hrad hgpos.le
    have hsum_nn : 0 ≤ ∑ l ∈ t j, (Z_alpha (W' j l) (N' j l) α) ^ gamma α :=
      Finset.sum_nonneg fun l hl => Real.rpow_nonneg
        (div_nonneg (hW' j hj l hl) (Real.rpow_pos_of_pos (hN' j hj l hl) α).le) _
    rwa [← Real.rpow_mul hsum_nn, one_div_mul_cancel hgpos.ne', Real.rpow_one] at hrpow
  have hsum_le : ∑ j ∈ s, (Z_alpha (W j) (N j) α) ^ gamma α ≤
      ∑ j ∈ s, ∑ l ∈ t j, (Z_alpha (W' j l) (N' j l) α) ^ gamma α :=
    Finset.sum_le_sum hpart
  have hcoarse_nn : 0 ≤ ∑ j ∈ s, (Z_alpha (W j) (N j) α) ^ gamma α := by
    refine Finset.sum_nonneg fun j hj => ?_
    have hWn : 0 ≤ W j := Finset.sum_nonneg fun l hl => hW' j hj l hl
    have hNp : 0 < N j := Finset.sum_pos (fun l hl => hN' j hj l hl) (ht j hj)
    exact Real.rpow_nonneg (div_nonneg hWn (Real.rpow_pos_of_pos hNp α).le) _
  exact Real.rpow_le_rpow hcoarse_nn hsum_le (one_div_pos.mpr hgpos).le

/-- Remark 5 (`rem:partition`): for `α ∈ (0, 1)`, a partition refinement strictly raises
the score whenever any part has unequal sub-rates. -/
theorem radon_refinement_strict_lt {ι κ : Type*} (s : Finset ι) (t : ι → Finset κ)
    (ht : ∀ j ∈ s, (t j).Nonempty) (W' N' : ι → κ → ℝ)
    {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (hW' : ∀ j ∈ s, ∀ l ∈ t j, 0 ≤ W' j l)
    (hN' : ∀ j ∈ s, ∀ l ∈ t j, 0 < N' j l)
    (hneq : ∃ j ∈ s, ∃ l₁ ∈ t j, ∃ l₂ ∈ t j, W' j l₁ / N' j l₁ ≠ W' j l₂ / N' j l₂) :
    let W : ι → ℝ := fun j => ∑ l ∈ t j, W' j l
    let N : ι → ℝ := fun j => ∑ l ∈ t j, N' j l
    (∑ j ∈ s, (Z_alpha (W j) (N j) α) ^ gamma α) ^ (1 / gamma α) <
      (∑ j ∈ s, ∑ l ∈ t j, (Z_alpha (W' j l) (N' j l) α) ^ gamma α) ^ (1 / gamma α) := by
  intro W N
  have hgpos : 0 < gamma α := gamma_pos h1
  have hpart_le : ∀ j ∈ s,
      (Z_alpha (W j) (N j) α) ^ gamma α ≤ ∑ l ∈ t j, (Z_alpha (W' j l) (N' j l) α) ^ gamma α := by
    intro j hj
    have hrad := radon_inequality (t j) (ht j hj) (W' j) (N' j) h0.le h1
      (fun l hl => hW' j hj l hl) (fun l hl => hN' j hj l hl)
    change Z_alpha (W j) (N j) α ≤
      (∑ l ∈ t j, (Z_alpha (W' j l) (N' j l) α) ^ gamma α) ^ (1 / gamma α) at hrad
    have hZnn : 0 ≤ Z_alpha (W j) (N j) α := by
      unfold Z_alpha
      exact div_nonneg (Finset.sum_nonneg fun l hl => hW' j hj l hl)
        (Real.rpow_pos_of_pos (Finset.sum_pos (fun l hl => hN' j hj l hl) (ht j hj)) α).le
    have hrpow := Real.rpow_le_rpow hZnn hrad hgpos.le
    have hsum_nn : 0 ≤ ∑ l ∈ t j, (Z_alpha (W' j l) (N' j l) α) ^ gamma α :=
      Finset.sum_nonneg fun l hl => Real.rpow_nonneg
        (div_nonneg (hW' j hj l hl) (Real.rpow_pos_of_pos (hN' j hj l hl) α).le) _
    rwa [← Real.rpow_mul hsum_nn, one_div_mul_cancel hgpos.ne', Real.rpow_one] at hrpow
  obtain ⟨j0, hj0, l1, hl1, l2, hl2, hrate_ne⟩ := hneq
  have hj0_lt : (Z_alpha (W j0) (N j0) α) ^ gamma α <
      ∑ l ∈ t j0, (Z_alpha (W' j0 l) (N' j0 l) α) ^ gamma α := by
    have hle := hpart_le j0 hj0
    refine lt_of_le_of_ne hle fun heq => ?_
    have hsum_nn : 0 ≤ ∑ l ∈ t j0, (Z_alpha (W' j0 l) (N' j0 l) α) ^ gamma α :=
      Finset.sum_nonneg fun l hl => Real.rpow_nonneg
        (div_nonneg (hW' j0 hj0 l hl) (Real.rpow_pos_of_pos (hN' j0 hj0 l hl) α).le) _
    have hrpow := congrArg (· ^ (1 / gamma α)) heq
    dsimp only at hrpow
    have hZnn : 0 ≤ Z_alpha (W j0) (N j0) α := by
      unfold Z_alpha
      exact div_nonneg (Finset.sum_nonneg fun l hl => hW' j0 hj0 l hl)
        (Real.rpow_pos_of_pos (Finset.sum_pos (fun l hl => hN' j0 hj0 l hl) (ht j0 hj0)) α).le
    rw [← Real.rpow_mul hZnn, mul_one_div_cancel hgpos.ne', Real.rpow_one] at hrpow
    have hiff := (radon_equality_iff (t j0) (ht j0 hj0) (W' j0) (N' j0) h0 h1
      (fun l hl => hW' j0 hj0 l hl) (fun l hl => hN' j0 hj0 l hl)).mp hrpow.symm
    exact hrate_ne (hiff l1 hl1 l2 hl2)
  have hsum_lt : ∑ j ∈ s, (Z_alpha (W j) (N j) α) ^ gamma α <
      ∑ j ∈ s, ∑ l ∈ t j, (Z_alpha (W' j l) (N' j l) α) ^ gamma α :=
    Finset.sum_lt_sum hpart_le ⟨j0, hj0, hj0_lt⟩
  have hcoarse_nn : 0 ≤ ∑ j ∈ s, (Z_alpha (W j) (N j) α) ^ gamma α := by
    refine Finset.sum_nonneg fun j hj => ?_
    have hWn : 0 ≤ W j := Finset.sum_nonneg fun l hl => hW' j hj l hl
    have hNp : 0 < N j := Finset.sum_pos (fun l hl => hN' j hj l hl) (ht j hj)
    exact Real.rpow_nonneg (div_nonneg hWn (Real.rpow_pos_of_pos hNp α).le) _
  exact Real.rpow_lt_rpow hcoarse_nn hsum_lt (one_div_pos.mpr hgpos)

/-- Appendix E (`app:radon`): the Radon lower bound `Z_α` on `(∑_s N_s^(1-γ) W_s^γ)^(1/γ)`
is explicitly attained by the constant-rate season profile `W_s = (W / N) * N_s`. -/
theorem radon_constant_rate_attained {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (N_s : ι → ℝ) (hN_s : ∀ j ∈ s, 0 < N_s j) {W α : ℝ} (hW : 0 ≤ W) (h0 : 0 ≤ α) (h1 : α < 1) :
    let N := ∑ j ∈ s, N_s j
    let W_s : ι → ℝ := fun j => (W / N) * N_s j
    ∑ j ∈ s, W_s j = W ∧
    (∑ j ∈ s, N_s j ^ (1 - gamma α) * W_s j ^ gamma α) ^ (1 / gamma α) = Z_alpha W N α := by
  intro N W_s
  have hN : 0 < N := Finset.sum_pos hN_s hs
  have hsum_W : ∑ j ∈ s, W_s j = W := by
    dsimp [W_s]
    rw [← Finset.mul_sum]
    change (W / N) * N = W
    exact div_mul_cancel₀ W hN.ne'
  refine ⟨hsum_W, ?_⟩
  have hterm : ∀ j ∈ s, N_s j ^ (1 - gamma α) * W_s j ^ gamma α =
      (Z_alpha (W_s j) (N_s j) α) ^ gamma α := by
    intro j hj
    unfold Z_alpha
    have hNj := hN_s j hj
    have hWj : 0 ≤ W_s j := mul_nonneg (div_nonneg hW hN.le) hNj.le
    rw [Real.div_rpow hWj (Real.rpow_pos_of_pos hNj α).le,
        ← Real.rpow_mul hNj.le, alpha_mul_gamma h1.ne,
        div_eq_mul_inv, ← Real.rpow_neg hNj.le, neg_sub]
    ring
  rw [Finset.sum_congr rfl hterm]
  rcases eq_or_lt_of_le h0 with rfl | h0pos
  · have hg : gamma 0 = 1 := by unfold gamma; norm_num
    simp only [hg, Real.rpow_one, Z_alpha, Real.rpow_zero, div_one]
    exact hsum_W
  · have hrate : ∀ j ∈ s, ∀ k ∈ s, W_s j / N_s j = W_s k / N_s k := by
      intro j hj k hk
      dsimp [W_s]
      rw [mul_div_cancel_right₀ _ (hN_s j hj).ne', mul_div_cancel_right₀ _ (hN_s k hk).ne']
    have heq := (radon_equality_iff s hs W_s N_s h0pos h1
      (fun j hj => mul_nonneg (div_nonneg hW hN.le) (hN_s j hj).le) hN_s).mpr hrate
    rw [hsum_W] at heq
    exact heq

/-- Appendix E (`app:radon`): relative to a reference season exposure `E₀`, a short
season `0 < N_i < E₀` receives strictly less weight under unnormalized `E₀^(1-γ) s_i^γ` than
under exposure-normalized `N_i^(1-γ) s_i^γ` when `α ∈ (0, 1)` (`γ > 1`) and `s_i > 0`. -/
theorem season_unnormalized_discounts_short_exposure {N_i E₀ s_i α : ℝ}
    (h0 : 0 < α) (h1 : α < 1) (hNi : 0 < N_i) (hlt : N_i < E₀) (hs : 0 < s_i) :
    E₀ ^ (1 - gamma α) * s_i ^ gamma α < N_i ^ (1 - gamma α) * s_i ^ gamma α := by
  have hg1 : 1 < gamma α := one_lt_gamma h0 h1
  have hneg_exp : 1 - gamma α < 0 := by linarith
  have hE0 : 0 < E₀ := hNi.trans hlt
  have hpow_gt : N_i ^ (gamma α - 1) < E₀ ^ (gamma α - 1) :=
    Real.rpow_lt_rpow hNi.le hlt (sub_pos.mpr hg1)
  have hneg_pow : E₀ ^ (1 - gamma α) < N_i ^ (1 - gamma α) := by
    rw [show 1 - gamma α = -(gamma α - 1) by ring, Real.rpow_neg hE0.le, Real.rpow_neg hNi.le]
    exact inv_strictAnti₀ (Real.rpow_pos_of_pos hNi _) hpow_gt
  exact mul_lt_mul_of_pos_right hneg_pow (Real.rpow_pos_of_pos hs _)

/-- Appendix E (`app:radon`): exact squared equivalence for quadrature `< Z_pool`,
and exact threshold `α < 1/2` when exposures and values match. -/
theorem quadrature_lt_zpool_iff_sq {W₁ N₁ W₂ N₂ α : ℝ}
    (hpool : 0 ≤ Z_pool W₁ N₁ W₂ N₂ α) :
    Real.sqrt (Z_alpha W₁ N₁ α ^ 2 + Z_alpha W₂ N₂ α ^ 2) < Z_pool W₁ N₁ W₂ N₂ α ↔
      Z_alpha W₁ N₁ α ^ 2 + Z_alpha W₂ N₂ α ^ 2 < Z_pool W₁ N₁ W₂ N₂ α ^ 2 := by
  conv_lhs => rw [← Real.sqrt_sq hpool]
  exact Real.sqrt_lt_sqrt_iff (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem quadrature_lt_zpool_equal_inputs_iff {W N α : ℝ} (hW : 0 < W) (hN : 0 < N) :
    Real.sqrt (Z_alpha W N α ^ 2 + Z_alpha W N α ^ 2) < Z_pool W N W N α ↔ α < 1 / 2 := by
  have hpool_pos : 0 < Z_pool W N W N α := by
    unfold Z_pool
    exact div_pos (by linarith) (Real.rpow_pos_of_pos (by linarith) α)
  rw [quadrature_lt_zpool_iff_sq hpool_pos.le]
  unfold Z_alpha Z_pool
  have h2N : (N + N) ^ α = (2 : ℝ) ^ α * N ^ α := by
    rw [← two_mul, Real.mul_rpow (by norm_num) hN.le]
  rw [h2N]
  have hWpos : 0 < W ^ 2 := sq_pos_of_pos hW
  have hNα : 0 < N ^ α := Real.rpow_pos_of_pos hN α
  have h2α : 0 < (2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
  have hlhs : (W / N ^ α) ^ 2 + (W / N ^ α) ^ 2 = 2 * W ^ 2 / (N ^ α) ^ 2 := by ring
  have hrhs : ((W + W) / ((2 : ℝ) ^ α * N ^ α)) ^ 2 =
      (4 / (2 : ℝ) ^ (2 * α)) * (W ^ 2 / (N ^ α) ^ 2) := by
    rw [show (2 : ℝ) ^ (2 * α) = ((2 : ℝ) ^ α) ^ 2 by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ α) 2, ← Real.rpow_mul (by norm_num)]; ring_nf]
    ring
  rw [hlhs, hrhs]
  have hbase_pos : 0 < W ^ 2 / (N ^ α) ^ 2 := div_pos hWpos (sq_pos_of_pos hNα)
  rw [show 2 * W ^ 2 / (N ^ α) ^ 2 = 2 * (W ^ 2 / (N ^ α) ^ 2) by ring,
      mul_lt_mul_iff_left₀ hbase_pos]
  have h2sq : (0 : ℝ) < (2 : ℝ) ^ (2 * α) := Real.rpow_pos_of_pos (by norm_num) _
  rw [lt_div_iff₀ h2sq]
  have h2_1 : (2 : ℝ) * (2 : ℝ) ^ (2 * α) = (2 : ℝ) ^ (1 + 2 * α) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]
  have h4_eq : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
  rw [h2_1, h4_eq, Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)]
  constructor <;> intro h <;> linarith

/-! ### 15.8 Proposition 6 / Appendix C Null Extensions & KL for `Z_null` -/

/-- Section 1 (Eq. 2) & Appendix C (`app:null`): `Z_{0, r_avg} = W - r_avg N = WAA`. -/
theorem Z_null_zero_eq_waa (W N r_avg : ℝ) :
    Z_null W N r_avg 0 = W - r_avg * N := by
  simp [Z_null]

/-- Appendix C.1 (`sec:null`, Eq. 16): `Z_{α,λ} = (W - λ D) / N^α` equals `Z_null` at
`r₀ = λ D / N`. -/
theorem Z_null_lambda_eq {W N lam D α : ℝ} (hN : N ≠ 0) :
    (W - lam * D) / N ^ α = Z_null W N (lam * D / N) α := by
  unfold Z_null
  rw [div_mul_cancel₀ _ hN]

theorem prop_null_lambda_iff {W N lam D r_marg α : ℝ} (hN : 0 < N) :
    N ^ (-α) * ((r_marg - lam * D / N) - α * (W / N - lam * D / N)) > 0 ↔
      r_marg > (1 - α) * (lam * D / N) + α * (W / N) :=
  prop_null_iff hN

theorem prop_null_lambda_alpha_eff {W N lam D α : ℝ} (hW : W ≠ 0) (hN : N ≠ 0) :
    ((1 - α) * (lam * D / N) + α * (W / N)) / (W / N) = α + (1 - α) * (lam * D / W) := by
  have h1 := prop_null_alpha_eff (r₀ := lam * D / N) (α := α) (div_ne_zero hW hN)
  have hratio : (lam * D / N) / (W / N) = lam * D / W := by field_simp [hN, hW]
  rwa [hratio] at h1

/-- Appendix C (`app:null`): raising the null rate `r₀` strictly increases the effective
exponent `α_eff = α + (1 - α) r₀ / r̄` whenever `α < 1` and `r̄ > 0`. -/
theorem prop_null_alpha_eff_strictMono_r0 {r_bar α : ℝ} (hα : α < 1) (hr : 0 < r_bar) :
    StrictMono (fun r₀ : ℝ => α + (1 - α) * (r₀ / r_bar)) := by
  intro a b hab
  have h1α : 0 < 1 - α := sub_pos.mpr hα
  have hdiv : a / r_bar < b / r_bar := div_lt_div_of_pos_right hab hr
  linarith [mul_lt_mul_of_pos_left hdiv h1α]

/-- Appendix C (`app:null`): when `W - r₀ N > 0` and `N > 1`, `Z_{α,r₀}` is strictly
decreasing in `α` (the positive-numerator counterpart to `prop_null_neg_numerator_strictMono_alpha`). -/
theorem prop_null_pos_numerator_strictAnti_alpha {W N r₀ α₁ α₂ : ℝ}
    (hpos : 0 < W - r₀ * N) (hN : 1 < N) (hα : α₁ < α₂) :
    Z_null W N r₀ α₂ < Z_null W N r₀ α₁ := by
  unfold Z_null
  have hpow : N ^ α₁ < N ^ α₂ := Real.rpow_lt_rpow_of_exponent_lt hN hα
  have hNpos : 0 < N := by linarith
  have hp1 : 0 < N ^ α₁ := Real.rpow_pos_of_pos hNpos α₁
  exact div_lt_div_of_pos_left hpos hp1 hpow

/-- Remark 6 & Appendix C (`rem:interp`, `prop:null`): KL divergence against a general null
rate `r₀`, `D_KL(N(W/N, σ²/N) ‖ N(r₀, σ²/N)) = (W - r₀ N)² / (2σ² N)`, and
`Z_{1/2, r₀} = sgn(W - r₀ N) σ √(2 D_KL)`. -/
theorem kl_gaussian_zwar_null {W N r₀ σ : ℝ} (hN : 0 < N) (hσ : 0 < σ) :
    let v : ℝ≥0 := ⟨σ ^ 2 / N, by positivity⟩
    InformationTheory.klDiv (gaussianReal (W / N) v) (gaussianReal r₀ v) =
      ENNReal.ofReal ((W - r₀ * N) ^ 2 / (2 * σ ^ 2 * N)) ∧
    Real.sign (W - r₀ * N) * σ * Real.sqrt
        (2 * (InformationTheory.klDiv (gaussianReal (W / N) v) (gaussianReal r₀ v)).toReal) =
      Z_null W N r₀ (1 / 2) := by
  intro v
  have hv_pos : (0 : ℝ) < (v : ℝ) := by dsimp [v]; positivity
  have hv_ne : v ≠ 0 := NNReal.coe_ne_zero.mp hv_pos.ne'
  have hkl : InformationTheory.klDiv (gaussianReal (W / N) v) (gaussianReal r₀ v) =
      ENNReal.ofReal ((W - r₀ * N) ^ 2 / (2 * σ ^ 2 * N)) := by
    rw [klDiv_gaussianReal_same_var (W / N) r₀ v hv_ne]
    congr 1
    dsimp [v]
    field_simp [hN.ne', hσ.ne']
  refine ⟨hkl, ?_⟩
  rw [hkl, ENNReal.toReal_ofReal (by positivity)]
  have h2D : 2 * ((W - r₀ * N) ^ 2 / (2 * σ ^ 2 * N)) = (W - r₀ * N) ^ 2 / (σ ^ 2 * N) := by
    field_simp [hσ.ne', hN.ne']
  rw [h2D, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs, Real.sqrt_mul (sq_nonneg σ),
      Real.sqrt_sq hσ.le, Real.sqrt_eq_rpow]
  have h1 : σ * (|W - r₀ * N| / (σ * N ^ (1 / 2 : ℝ))) = |W - r₀ * N| / N ^ (1 / 2 : ℝ) := by
    field_simp [hσ.ne']
  calc Real.sign (W - r₀ * N) * σ * (|W - r₀ * N| / (σ * N ^ (1 / 2 : ℝ)))
      = Real.sign (W - r₀ * N) * (σ * (|W - r₀ * N| / (σ * N ^ (1 / 2 : ℝ)))) := by ring
    _ = Real.sign (W - r₀ * N) * (|W - r₀ * N| / N ^ (1 / 2 : ℝ)) := by rw [h1]
    _ = (Real.sign (W - r₀ * N) * |W - r₀ * N|) / N ^ (1 / 2 : ℝ) := by ring
    _ = (W - r₀ * N) / N ^ (1 / 2 : ℝ) := by rw [real_sign_mul_abs]
    _ = Z_null W N r₀ (1 / 2) := rfl

/-! ### 15.9 Appendix H Direct Delta Method on `Z_twoway` & Pairwise Rounding Bound -/

/-- Appendix B & H (`app:twoway`, `app:uncert`): when both coordinates are non-negative,
`Z_{1/2, 2D} = √(Z₁² + Z₂²)`. -/
theorem Z_twoway_half_both_nonneg {W₁ N₁ W₂ N₂ : ℝ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (h1 : 0 ≤ W₁) (h2 : 0 ≤ W₂) :
    Z_twoway W₁ N₁ W₂ N₂ (1 / 2) =
      Real.sqrt (Z_alpha W₁ N₁ (1 / 2) ^ 2 + Z_alpha W₂ N₂ (1 / 2) ^ 2) := by
  have hg : gamma (1 / 2 : ℝ) = 2 := by unfold gamma; norm_num
  have hZ1_nn : 0 ≤ Z_alpha W₁ N₁ (1 / 2) := by
    unfold Z_alpha; exact div_nonneg h1 (Real.rpow_pos_of_pos hN₁ _).le
  have hZ2_nn : 0 ≤ Z_alpha W₂ N₂ (1 / 2) := by
    unfold Z_alpha; exact div_nonneg h2 (Real.rpow_pos_of_pos hN₂ _).le
  have hI : I_twoway W₁ N₁ W₂ N₂ (1 / 2) =
      Z_alpha W₁ N₁ (1 / 2) ^ 2 + Z_alpha W₂ N₂ (1 / 2) ^ 2 := by
    unfold I_twoway
    rw [twoway_I_alt_form hN₁ (by norm_num), twoway_I_alt_form hN₂ (by norm_num), hg,
        signedPow_nonneg hZ1_nn (by norm_num), signedPow_nonneg hZ2_nn (by norm_num),
        Real.rpow_two, Real.rpow_two]
  have hInn : 0 ≤ I_twoway W₁ N₁ W₂ N₂ (1 / 2) := by rw [hI]; positivity
  unfold Z_twoway
  rw [hg, signedPow_nonneg hInn (by norm_num), ← Real.sqrt_eq_rpow, hI]

private lemma same_sign_or_zero_I_half_ne_zero {μ₁ μ₂ PA BF : ℝ}
    (hPA : 0 < PA) (hBF : 0 < BF) (hne : μ₁ ≠ 0 ∨ μ₂ ≠ 0)
    (hsame : (0 ≤ μ₁ ∧ 0 ≤ μ₂) ∨ (μ₁ ≤ 0 ∧ μ₂ ≤ 0)) :
    I_twoway μ₁ PA μ₂ BF (1 / 2) ≠ 0 ∧
      |Z_twoway μ₁ PA μ₂ BF (1 / 2)| = Real.sqrt (μ₁ ^ 2 / PA + μ₂ ^ 2 / BF) := by
  have hg : gamma (1 / 2 : ℝ) = 2 := by unfold gamma; norm_num
  have hss_pos : 0 < μ₁ ^ 2 / PA + μ₂ ^ 2 / BF := by
    rcases hne with h1 | h2
    · exact add_pos_of_pos_of_nonneg (div_pos (sq_pos_of_ne_zero h1) hPA)
        (div_nonneg (sq_nonneg _) hBF.le)
    · exact add_pos_of_nonneg_of_pos (div_nonneg (sq_nonneg _) hPA.le)
        (div_pos (sq_pos_of_ne_zero h2) hBF)
  have hI_abs : |I_twoway μ₁ PA μ₂ BF (1 / 2)| = μ₁ ^ 2 / PA + μ₂ ^ 2 / BF := by
    unfold I_twoway
    rw [hg, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_one]
    rcases hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [signedPow_nonneg h1 (by norm_num), signedPow_nonneg h2 (by norm_num),
          Real.rpow_two, Real.rpow_two, abs_of_nonneg (by positivity)]
    · have hs1 : signedPow μ₁ 2 = -(μ₁ ^ 2) := by
        rcases eq_or_lt_of_le h1 with rfl | hlt
        · simp [signedPow_zero_left]
        · rw [signedPow_neg hlt, Real.rpow_two]; ring
      have hs2 : signedPow μ₂ 2 = -(μ₂ ^ 2) := by
        rcases eq_or_lt_of_le h2 with rfl | hlt
        · simp [signedPow_zero_left]
        · rw [signedPow_neg hlt, Real.rpow_two]; ring
      rw [hs1, hs2, show -(μ₁ ^ 2) / PA + -(μ₂ ^ 2) / BF = -(μ₁ ^ 2 / PA + μ₂ ^ 2 / BF) by ring,
          abs_neg, abs_of_pos hss_pos]
  have hIne : I_twoway μ₁ PA μ₂ BF (1 / 2) ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hI_abs; linarith
  have hZabs : |Z_twoway μ₁ PA μ₂ BF (1 / 2)| = Real.sqrt (μ₁ ^ 2 / PA + μ₂ ^ 2 / BF) := by
    unfold Z_twoway signedPow
    rw [hg, show (1 : ℝ) / 2 = 1 / 2 by norm_num, abs_mul]
    have hs : |Real.sign (I_twoway μ₁ PA μ₂ BF (1 / 2))| = 1 := by
      rcases lt_or_gt_of_ne hIne with hn | hp
      · rw [Real.sign_of_neg hn]; norm_num
      · rw [Real.sign_of_pos hp]; norm_num
    rw [hs, one_mul, hI_abs, abs_of_nonneg (Real.rpow_nonneg hss_pos.le _), Real.sqrt_eq_rpow]
  exact ⟨hIne, hZabs⟩

/-- Appendix H (`app:uncert`): direct Fréchet derivative of `Z_{1/2, 2D}` in `(W₁, W₂)`
on same-sign coordinates or when one coordinate vanishes (away from `(0, 0)`), and unit-norm
gradient in standardized `(Z₁, Z₂)` coordinates (`‖∇‖² = 1`). -/
theorem delta_method_Z_twoway_half_grad_norm_sq {z₁ z₂ PA BF : ℝ}
    (hPA : 0 < PA) (hBF : 0 < BF) (hne : z₁ ≠ 0 ∨ z₂ ≠ 0)
    (hsame : (0 ≤ z₁ ∧ 0 ≤ z₂) ∨ (z₁ ≤ 0 ∧ z₂ ≤ 0)) :
    let D := Real.sqrt (z₁ ^ 2 + z₂ ^ 2)
    let g₁ := |z₁| / D
    let g₂ := |z₂| / D
    HasFDerivAt (fun p : ℝ × ℝ => Z_twoway (p.1 * Real.sqrt PA) PA (p.2 * Real.sqrt BF) BF (1 / 2))
      (g₁ • ContinuousLinearMap.fst ℝ ℝ ℝ + g₂ • ContinuousLinearMap.snd ℝ ℝ ℝ) (z₁, z₂) ∧
    g₁ ^ 2 + g₂ ^ 2 = 1 := by
  intro D g₁ g₂
  let μ₁ := z₁ * Real.sqrt PA
  let μ₂ := z₂ * Real.sqrt BF
  have hsPA : 0 < Real.sqrt PA := Real.sqrt_pos.mpr hPA
  have hsBF : 0 < Real.sqrt BF := Real.sqrt_pos.mpr hBF
  have hneμ : μ₁ ≠ 0 ∨ μ₂ ≠ 0 := by
    rcases hne with h1 | h2
    · exact Or.inl (mul_ne_zero h1 hsPA.ne')
    · exact Or.inr (mul_ne_zero h2 hsBF.ne')
  have hsameμ : (0 ≤ μ₁ ∧ 0 ≤ μ₂) ∨ (μ₁ ≤ 0 ∧ μ₂ ≤ 0) := by
    rcases hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨mul_nonneg h1 hsPA.le, mul_nonneg h2 hsBF.le⟩
    · exact Or.inr ⟨mul_nonpos_of_nonpos_of_nonneg h1 hsPA.le, mul_nonpos_of_nonpos_of_nonneg h2 hsBF.le⟩
  obtain ⟨hI, hZabs⟩ := same_sign_or_zero_I_half_ne_zero hPA hBF hneμ hsameμ
  have hfd := Z_twoway_hasFDerivAt (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    hPA hBF hI
  have hlin : HasFDerivAt (fun p : ℝ × ℝ => (p.1 * Real.sqrt PA, p.2 * Real.sqrt BF))
      ((Real.sqrt PA • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (Real.sqrt BF • ContinuousLinearMap.snd ℝ ℝ ℝ)) (z₁, z₂) := by
    have h1 : HasFDerivAt (fun p : ℝ × ℝ => p.1 * Real.sqrt PA)
        (Real.sqrt PA • ContinuousLinearMap.fst ℝ ℝ ℝ) (z₁, z₂) := by
      simpa [mul_comm] using
        ((hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (z₁, z₂))).const_mul (Real.sqrt PA))
    have h2 : HasFDerivAt (fun p : ℝ × ℝ => p.2 * Real.sqrt BF)
        (Real.sqrt BF • ContinuousLinearMap.snd ℝ ℝ ℝ) (z₁, z₂) := by
      simpa [mul_comm] using
        ((hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (z₁, z₂))).const_mul (Real.sqrt BF))
    exact h1.prodMk h2
  have hcomp := hfd.comp (z₁, z₂) hlin
  have hss_pos : 0 < z₁ ^ 2 + z₂ ^ 2 := by
    rcases hne with h1 | h2
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h1) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h2)
  have hD_eq : Real.sqrt (μ₁ ^ 2 / PA + μ₂ ^ 2 / BF) = D := by
    have hμsq : μ₁ ^ 2 / PA + μ₂ ^ 2 / BF = z₁ ^ 2 + z₂ ^ 2 := by
      dsimp [μ₁, μ₂]
      rw [mul_pow, mul_pow, Real.sq_sqrt hPA.le, Real.sq_sqrt hBF.le]
      field_simp [hPA.ne', hBF.ne']
    rw [hμsq]
  have hg : gamma (1 / 2 : ℝ) = 2 := by unfold gamma; norm_num
  have hnorm_sq : g₁ ^ 2 + g₂ ^ 2 = 1 := by
    dsimp [g₁, g₂, D]
    rw [div_pow, div_pow, Real.sq_sqrt hss_pos.le, sq_abs, sq_abs, ← add_div, div_self hss_pos.ne']
  have hD_pos : 0 < D := Real.sqrt_pos.mpr hss_pos
  have hZabs_D : |Z_twoway μ₁ PA μ₂ BF (1 / 2)| = D := hZabs.trans hD_eq
  have h_fst : Real.sqrt PA * ((|μ₁| / PA) ^ (gamma (1 / 2) - 1) *
      |Z_twoway μ₁ PA μ₂ BF (1 / 2)| ^ (1 - gamma (1 / 2))) = g₁ := by
    rw [hg, show (2 : ℝ) - 1 = 1 by norm_num, show (1 : ℝ) - 2 = -1 by norm_num,
        Real.rpow_one, Real.rpow_neg_one, hZabs_D]
    dsimp [μ₁, g₁]
    rw [abs_mul, abs_of_pos hsPA]
    have hsqPA : Real.sqrt PA ^ 2 = PA := Real.sq_sqrt hPA.le
    calc Real.sqrt PA * ((|z₁| * Real.sqrt PA / PA) * D⁻¹)
        = (Real.sqrt PA ^ 2 / PA) * (|z₁| / D) := by rw [div_eq_mul_inv]; ring
      _ = (PA / PA) * (|z₁| / D) := by rw [hsqPA]
      _ = |z₁| / D := by rw [div_self hPA.ne', one_mul]
  have h_snd : Real.sqrt BF * ((|μ₂| / BF) ^ (gamma (1 / 2) - 1) *
      |Z_twoway μ₁ PA μ₂ BF (1 / 2)| ^ (1 - gamma (1 / 2))) = g₂ := by
    rw [hg, show (2 : ℝ) - 1 = 1 by norm_num, show (1 : ℝ) - 2 = -1 by norm_num,
        Real.rpow_one, Real.rpow_neg_one, hZabs_D]
    dsimp [μ₂, g₂]
    rw [abs_mul, abs_of_pos hsBF]
    have hsqBF : Real.sqrt BF ^ 2 = BF := Real.sq_sqrt hBF.le
    calc Real.sqrt BF * ((|z₂| * Real.sqrt BF / BF) * D⁻¹)
        = (Real.sqrt BF ^ 2 / BF) * (|z₂| / D) := by rw [div_eq_mul_inv]; ring
      _ = (BF / BF) * (|z₂| / D) := by rw [hsqBF]
      _ = |z₂| / D := by rw [div_self hBF.ne', one_mul]
  refine ⟨?_, hnorm_sq⟩
  convert hcomp using 1
  refine ContinuousLinearMap.ext fun p => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, smul_eq_mul]
  calc g₁ * p.1 + g₂ * p.2
      = (Real.sqrt PA * ((|μ₁| / PA) ^ (gamma (1 / 2) - 1) *
          |Z_twoway μ₁ PA μ₂ BF (1 / 2)| ^ (1 - gamma (1 / 2)))) * p.1 +
        (Real.sqrt BF * ((|μ₂| / BF) ^ (gamma (1 / 2) - 1) *
          |Z_twoway μ₁ PA μ₂ BF (1 / 2)| ^ (1 - gamma (1 / 2)))) * p.2 := by rw [h_fst, h_snd]
    _ = (|μ₁| / PA) ^ (gamma (1 / 2) - 1) * |Z_twoway μ₁ PA μ₂ BF (1 / 2)| ^ (1 - gamma (1 / 2)) *
          (Real.sqrt PA * p.1) +
        (|μ₂| / BF) ^ (gamma (1 / 2) - 1) * |Z_twoway μ₁ PA μ₂ BF (1 / 2)| ^ (1 - gamma (1 / 2)) *
          (Real.sqrt BF * p.2) := by ring

section DeltaMethodVar

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Appendix H (`app:uncert`): under the model of Proposition 3 (`Var(W_k) = N_k σ²`,
uncorrelated roles), the first-order delta-method linearization of `Z_{1/2, 2D}` at `(μ₁, μ₂)`
has exact variance `σ²` whenever `μ₁, μ₂` have the same sign or one vanishes (away from `(0, 0)`). -/
theorem delta_method_Z_twoway_half_linear_var (W₁ W₂ : Ω → ℝ) {PA BF μ₁ μ₂ σ : ℝ}
    (h1 : MemLp W₁ 2 μ) (h2 : MemLp W₂ 2 μ)
    (huncorr : cov[W₁, W₂; μ] = 0)
    (hv1 : variance W₁ μ = PA * σ ^ 2) (hv2 : variance W₂ μ = BF * σ ^ 2)
    (hPA : 0 < PA) (hBF : 0 < BF) (hne : μ₁ ≠ 0 ∨ μ₂ ≠ 0)
    (hsame : (0 ≤ μ₁ ∧ 0 ≤ μ₂) ∨ (μ₁ ≤ 0 ∧ μ₂ ≤ 0)) :
    variance (fun ω =>
      fderiv ℝ (fun w : ℝ × ℝ => Z_twoway w.1 PA w.2 BF (1 / 2)) (μ₁, μ₂)
        (W₁ ω - μ₁, W₂ ω - μ₂)) μ = σ ^ 2 := by
  obtain ⟨hI, hZabs⟩ := same_sign_or_zero_I_half_ne_zero hPA hBF hne hsame
  have hfd := Z_twoway_hasFDerivAt (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    hPA hBF hI
  rw [hfd.fderiv]
  have hg : gamma (1 / 2 : ℝ) = 2 := by unfold gamma; norm_num
  let D : ℝ := |Z_twoway μ₁ PA μ₂ BF (1 / 2)|
  have hD_eq : D = Real.sqrt (μ₁ ^ 2 / PA + μ₂ ^ 2 / BF) := hZabs
  have hD_pos : 0 < D := by
    rw [hD_eq]
    rcases hne with hμ1 | hμ2
    · exact Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg (div_pos (sq_pos_of_ne_zero hμ1) hPA)
        (div_nonneg (sq_nonneg _) hBF.le))
    · exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (div_nonneg (sq_nonneg _) hPA.le)
        (div_pos (sq_pos_of_ne_zero hμ2) hBF))
  let c₁ : ℝ := (|μ₁| / PA) ^ (gamma (1 / 2) - 1) * D ^ (1 - gamma (1 / 2))
  let c₂ : ℝ := (|μ₂| / BF) ^ (gamma (1 / 2) - 1) * D ^ (1 - gamma (1 / 2))
  have heval : (fun ω =>
      (c₁ • ContinuousLinearMap.fst ℝ ℝ ℝ + c₂ • ContinuousLinearMap.snd ℝ ℝ ℝ)
        (W₁ ω - μ₁, W₂ ω - μ₂)) =
      fun ω => (c₁ * W₁ ω + c₂ * W₂ ω) - (c₁ * μ₁ + c₂ * μ₂) := by
    ext ω
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
    ring
  change variance (fun ω =>
      (c₁ • ContinuousLinearMap.fst ℝ ℝ ℝ + c₂ • ContinuousLinearMap.snd ℝ ℝ ℝ)
        (W₁ ω - μ₁, W₂ ω - μ₂)) μ = σ ^ 2
  rw [heval]
  have hL2_1 : MemLp (fun ω => c₁ * W₁ ω) 2 μ := h1.const_mul c₁
  have hL2_2 : MemLp (fun ω => c₂ * W₂ ω) 2 μ := h2.const_mul c₂
  have hL2_sum : MemLp (fun ω => c₁ * W₁ ω + c₂ * W₂ ω) 2 μ := hL2_1.add hL2_2
  rw [variance_sub_const hL2_sum.aestronglyMeasurable, variance_fun_add hL2_1 hL2_2]
  have hcov : cov[fun ω => c₁ * W₁ ω, fun ω => c₂ * W₂ ω; μ] = 0 := by
    rw [covariance_const_mul_left, covariance_const_mul_right, huncorr, mul_zero, mul_zero]
  rw [hcov, variance_const_mul, variance_const_mul, hv1, hv2]
  have hc1_eq : c₁ = (|μ₁| / PA) / D := by
    dsimp [c₁]
    rw [hg, show (2 : ℝ) - 1 = 1 by norm_num, show (1 : ℝ) - 2 = -1 by norm_num,
        Real.rpow_one, Real.rpow_neg_one, ← div_eq_mul_inv]
  have hc2_eq : c₂ = (|μ₂| / BF) / D := by
    dsimp [c₂]
    rw [hg, show (2 : ℝ) - 1 = 1 by norm_num, show (1 : ℝ) - 2 = -1 by norm_num,
        Real.rpow_one, Real.rpow_neg_one, ← div_eq_mul_inv]
  have hD_sq : D ^ 2 = μ₁ ^ 2 / PA + μ₂ ^ 2 / BF := by
    rw [hD_eq, Real.sq_sqrt (by positivity)]
  have hcoeff : c₁ ^ 2 * PA + c₂ ^ 2 * BF = 1 := by
    rw [hc1_eq, hc2_eq, div_pow, div_pow, div_pow, div_pow, sq_abs μ₁, sq_abs μ₂]
    have hPAne : PA ≠ 0 := hPA.ne'
    have hBFne : BF ≠ 0 := hBF.ne'
    have hDne : D ^ 2 ≠ 0 := (sq_pos_of_pos hD_pos).ne'
    have hsum_eq : (μ₁ ^ 2 / PA ^ 2) / D ^ 2 * PA + (μ₂ ^ 2 / BF ^ 2) / D ^ 2 * BF =
        (μ₁ ^ 2 / PA + μ₂ ^ 2 / BF) / D ^ 2 := by
      field_simp [hPAne, hBFne, hDne]
    rw [hsum_eq, hD_sq, div_self (by rw [← hD_sq]; exact hDne)]
  calc c₁ ^ 2 * (PA * σ ^ 2) + 2 * 0 + c₂ ^ 2 * (BF * σ ^ 2)
      = (c₁ ^ 2 * PA + c₂ ^ 2 * BF) * σ ^ 2 := by ring
    _ = 1 * σ ^ 2 := by rw [hcoeff]
    _ = σ ^ 2 := one_mul _

end DeltaMethodVar

/-- Appendix H (`app:uncert`): in the opposite-sign regime, as one coordinate dominates
(`z₂ / z₁ → 0`), the delta-method variance multiplier `(z₁² + z₂²) / |z₁² - z₂²|` converges to `1`. -/
theorem delta_method_opp_sign_ratio_tendsto_one {z₁ : ℝ} (hz₁ : z₁ ≠ 0) :
    Tendsto (fun r : ℝ => (z₁ ^ 2 + (r * z₁) ^ 2) / |z₁ ^ 2 - (r * z₁) ^ 2|) (𝓝 0) (𝓝 1) := by
  have heq : (fun r : ℝ => (z₁ ^ 2 + (r * z₁) ^ 2) / |z₁ ^ 2 - (r * z₁) ^ 2|) =
      fun r : ℝ => (1 + r ^ 2) / |1 - r ^ 2| := by
    ext r
    have h1 : z₁ ^ 2 + (r * z₁) ^ 2 = z₁ ^ 2 * (1 + r ^ 2) := by ring
    have h2 : |z₁ ^ 2 - (r * z₁) ^ 2| = z₁ ^ 2 * |1 - r ^ 2| := by
      rw [show z₁ ^ 2 - (r * z₁) ^ 2 = z₁ ^ 2 * (1 - r ^ 2) by ring, abs_mul,
          abs_of_pos (sq_pos_of_ne_zero hz₁)]
    rw [h1, h2]
    field_simp [sq_pos_of_ne_zero hz₁]
  rw [heq]
  have hcont : ContinuousAt (fun r : ℝ => (1 + r ^ 2) / |1 - r ^ 2|) 0 := by
    refine (continuousAt_const.add (continuousAt_id.pow 2)).div
      ((continuousAt_const.sub (continuousAt_id.pow 2)).abs) ?_
    norm_num
  simpa using hcont.tendsto

/-- Appendix H (`app:uncert`): rounding `WAR` by `|δ₁|, |δ₂| ≤ ε` perturbs the difference
between two players' `Z_α` scores by at most `ε / N₁^α + ε / N₂^α`. -/
theorem app_h_rounding_pair_diff_bound {W₁ δ₁ N₁ W₂ δ₂ N₂ α ε : ℝ}
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hδ₁ : |δ₁| ≤ ε) (hδ₂ : |δ₂| ≤ ε) :
    |(Z_alpha (W₁ + δ₁) N₁ α - Z_alpha (W₂ + δ₂) N₂ α) -
        (Z_alpha W₁ N₁ α - Z_alpha W₂ N₂ α)| ≤
      ε / N₁ ^ α + ε / N₂ ^ α := by
  have h1 := (app_h_rounding_shift (W := W₁) (ΔW := δ₁) (N := N₁) (α := α) hN₁).2
  have h2 := (app_h_rounding_shift (W := W₂) (ΔW := δ₂) (N := N₂) (α := α) hN₂).2
  have hid : (Z_alpha (W₁ + δ₁) N₁ α - Z_alpha (W₂ + δ₂) N₂ α) -
        (Z_alpha W₁ N₁ α - Z_alpha W₂ N₂ α) =
      (Z_alpha (W₁ + δ₁) N₁ α - Z_alpha W₁ N₁ α) -
        (Z_alpha (W₂ + δ₂) N₂ α - Z_alpha W₂ N₂ α) := by ring
  rw [hid]
  calc |(Z_alpha (W₁ + δ₁) N₁ α - Z_alpha W₁ N₁ α) -
          (Z_alpha (W₂ + δ₂) N₂ α - Z_alpha W₂ N₂ α)|
      ≤ |Z_alpha (W₁ + δ₁) N₁ α - Z_alpha W₁ N₁ α| +
          |Z_alpha (W₂ + δ₂) N₂ α - Z_alpha W₂ N₂ α| := abs_sub _ _
    _ = |δ₁| / N₁ ^ α + |δ₂| / N₂ ^ α := by rw [h1, h2]
    _ ≤ ε / N₁ ^ α + ε / N₂ ^ α := by
        gcongr

/-! ### 15.10 Continuity in α, α → 1⁻ Limit, Noise/Calibration Corollaries, & Opposite-Sign Delta Method -/

/-- Sec. 1 & 3 (`eq:family`): for fixed `W` and `N > 0`, `α ↦ Z_α(W, N, α)` is continuous on `ℝ`. -/
theorem z_alpha_continuous_alpha {W N : ℝ} (hN : 0 < N) :
    Continuous (fun α : ℝ => Z_alpha W N α) := by
  unfold Z_alpha
  exact continuous_const.div
    (continuous_const.rpow continuous_id fun _ => Or.inl hN.ne')
    fun α => (Real.rpow_pos_of_pos hN α).ne'

/-- Sec. 1 & 3 (`eq:family`): with the exposure floor `max N 1`, `α ↦ Z_α(W, max N 1, α)`
is continuous on `ℝ` for every `W, N : ℝ`. -/
theorem z_alpha_floored_continuous_alpha (W N : ℝ) :
    Continuous (fun α : ℝ => Z_alpha_floored W N α) :=
  z_alpha_continuous_alpha (lt_of_lt_of_le zero_lt_one (le_max_right N 1))

private lemma signedPow_continuousAt_comp {f g : ℝ → ℝ} {a : ℝ}
    (hf : ContinuousAt f a) (hg : ContinuousAt g a) (hga : 0 < g a) :
    ContinuousAt (fun t => signedPow (f t) (g t)) a := by
  rcases lt_trichotomy (f a) 0 with hfa | hfa0 | hfa
  · have hev : (fun t => signedPow (f t) (g t)) =ᶠ[𝓝 a] fun t => -((-f t) ^ (g t)) := by
      filter_upwards [hf.eventually (Iio_mem_nhds hfa)] with t ht
      exact signedPow_neg ht
    have hcont : ContinuousAt (fun t => -((-f t) ^ (g t))) a :=
      (hf.neg.rpow hg (Or.inl (neg_pos.mpr hfa).ne')).neg
    exact hcont.congr_of_eventuallyEq hev
  · rw [ContinuousAt, hfa0, signedPow_zero_left hga]
    set p₀ := g a / 2
    have hp₀ : 0 < p₀ := half_pos hga
    have hge : ∀ᶠ t in 𝓝 a, p₀ ≤ g t := hg.eventually (Ici_mem_nhds (half_lt_self hga))
    have hle1 : ∀ᶠ t in 𝓝 a, |f t| ≤ 1 := by
      have h0 : |f a| < 1 := by simp [hfa0]
      filter_upwards [(continuous_abs.continuousAt.comp hf).eventually (Iio_mem_nhds h0)] with t ht
      exact ht.le
    have hbound : ∀ᶠ t in 𝓝 a, ‖signedPow (f t) (g t)‖ ≤ |f t| ^ p₀ := by
      filter_upwards [hge, hle1] with t hgt hft1
      have hgt_pos : 0 < g t := lt_of_lt_of_le hp₀ hgt
      unfold signedPow
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      have hs : |Real.sign (f t)| ≤ 1 := by
        rcases lt_trichotomy (f t) 0 with ht | h0 | ht
        · simp [Real.sign_of_neg ht]
        · simp [h0, Real.sign_zero]
        · simp [Real.sign_of_pos ht]
      calc |Real.sign (f t)| * |f t| ^ g t
          ≤ 1 * |f t| ^ g t := mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg (abs_nonneg _) _)
        _ = |f t| ^ g t := one_mul _
        _ ≤ |f t| ^ p₀ := by
            rcases eq_or_ne (f t) 0 with h0 | hne
            · simp [h0, Real.zero_rpow hgt_pos.ne', Real.zero_rpow hp₀.ne']
            · exact Real.rpow_le_rpow_of_exponent_ge (abs_pos.mpr hne) hft1 hgt
    have htend : Tendsto (fun t => |f t| ^ p₀) (𝓝 a) (𝓝 0) := by
      have hc : Continuous (fun u : ℝ => |u| ^ p₀) :=
        continuous_abs.rpow_const fun _ => Or.inr hp₀.le
      have hcomp := (hc.continuousAt (x := f a)).comp hf
      simpa [hfa0, Real.zero_rpow hp₀.ne'] using hcomp.tendsto
    exact squeeze_zero_norm' hbound htend
  · have hev : (fun t => signedPow (f t) (g t)) =ᶠ[𝓝 a] fun t => (f t) ^ (g t) := by
      filter_upwards [hf.eventually (Ioi_mem_nhds hfa), hg.eventually (Ioi_mem_nhds hga)] with t ht hgt
      exact signedPow_nonneg ht.le hgt
    exact (hf.rpow hg (Or.inl hfa.ne')).congr_of_eventuallyEq hev

/-- Sec. 3.5 (`def:twoway`): for `PA, BF > 0` and any `W₁, W₂ : ℝ`, `α ↦ Z_{α,2D}(W₁, PA, W₂, BF)`
is continuous on `(-∞, 1)` (in particular on `[0, 1)`, connecting continuously to `W₁ + W₂` at `α = 0`). -/
theorem Z_twoway_continuous_alpha {W₁ PA W₂ BF : ℝ} (hPA : 0 < PA) (hBF : 0 < BF) :
    ContinuousOn (fun α : ℝ => Z_twoway W₁ PA W₂ BF α) (Iio 1) := by
  intro α hα
  have h1α : (1 : ℝ) - α ≠ 0 := sub_ne_zero.mpr (ne_of_gt hα)
  have hγ_cont : ContinuousAt gamma α :=
    continuousAt_const.div (continuousAt_const.sub continuousAt_id) h1α
  have hγ_pos : 0 < gamma α := gamma_pos hα
  have hPA_cont : ContinuousAt (fun t => PA ^ (gamma t - 1)) α :=
    continuousAt_const.rpow (hγ_cont.sub continuousAt_const) (Or.inl hPA.ne')
  have hBF_cont : ContinuousAt (fun t => BF ^ (gamma t - 1)) α :=
    continuousAt_const.rpow (hγ_cont.sub continuousAt_const) (Or.inl hBF.ne')
  have hI_cont : ContinuousAt (fun t => I_twoway W₁ PA W₂ BF t) α := by
    unfold I_twoway
    have h1 := (signedPow_continuousAt_comp (continuousAt_const (y := W₁)) hγ_cont hγ_pos).div
      hPA_cont (Real.rpow_pos_of_pos hPA _).ne'
    have h2 := (signedPow_continuousAt_comp (continuousAt_const (y := W₂)) hγ_cont hγ_pos).div
      hBF_cont (Real.rpow_pos_of_pos hBF _).ne'
    exact h1.add h2
  have hinv_cont : ContinuousAt (fun t => 1 / gamma t) α := by
    simpa only [one_div_gamma] using continuousAt_const.sub continuousAt_id
  have hinv_pos : 0 < 1 / gamma α := one_div_pos.mpr hγ_pos
  exact (signedPow_continuousAt_comp hI_cont hinv_cont hinv_pos).continuousWithinAt

private lemma I_twoway_rate_form {W₁ N₁ W₂ N₂ α : ℝ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) :
    I_twoway W₁ N₁ W₂ N₂ α =
      N₁ * signedPow (W₁ / N₁) (gamma α) + N₂ * signedPow (W₂ / N₂) (gamma α) := by
  have hterm : ∀ W N : ℝ, 0 < N →
      signedPow W (gamma α) / N ^ (gamma α - 1) = N * signedPow (W / N) (gamma α) := by
    intro W N hN
    have hW : W = N * (W / N) := by field_simp [hN.ne']
    conv_lhs => rw [hW, signedPow_mul_pos hN]
    rw [Real.rpow_sub hN, Real.rpow_one]
    have hNp : N ^ gamma α ≠ 0 := (Real.rpow_pos_of_pos hN _).ne'
    field_simp [hN.ne', hNp]
  unfold I_twoway
  rw [hterm W₁ N₁ hN₁, hterm W₂ N₂ hN₂]

private lemma tendsto_gamma_atTop : Tendsto gamma (𝓝[<] (1 : ℝ)) atTop := by
  have hsub : Tendsto (fun α : ℝ => (1 : ℝ) - α) (𝓝[<] 1) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun α : ℝ => (1 : ℝ) - α) 1 := continuousAt_const.sub continuousAt_id
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun α (hα : α < 1) => sub_pos.mpr hα
  have hinv := tendsto_inv_nhdsGT_zero.comp hsub
  refine hinv.congr' ?_
  filter_upwards with α
  simp [gamma, one_div]

private lemma tendsto_rpow_one_sub {c : ℝ} (hc : 0 < c) :
    Tendsto (fun α : ℝ => c ^ (1 - α)) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
  have hcont : ContinuousAt (fun α : ℝ => c ^ (1 - α)) 1 :=
    continuousAt_const.rpow (continuousAt_const.sub continuousAt_id) (Or.inl hc.ne')
  simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds

private lemma Z_twoway_tendsto_one_left_of_abs_gt {W₁ N₁ W₂ N₂ : ℝ}
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hgt : |W₂ / N₂| < |W₁ / N₁|) :
    Tendsto (fun α => Z_twoway W₁ N₁ W₂ N₂ α) (𝓝[<] 1) (𝓝 (W₁ / N₁)) := by
  set r₁ := W₁ / N₁
  set r₂ := W₂ / N₂
  have hr1_abs_pos : 0 < |r₁| := lt_of_le_of_lt (abs_nonneg _) hgt
  have hr1_ne : r₁ ≠ 0 := abs_pos.mp hr1_abs_pos
  set q := |r₂| / |r₁|
  have hq_nn : 0 ≤ q := div_nonneg (abs_nonneg _) hr1_abs_pos.le
  have hq_lt1 : q < 1 := (div_lt_one hr1_abs_pos).mpr hgt
  let u : ℝ → ℝ := fun α => Real.sign r₁ + (N₂ / N₁) * Real.sign r₂ * q ^ (gamma α)
  have hq_tend : Tendsto (fun α => q ^ (gamma α)) (𝓝[<] 1) (𝓝 0) := by
    rcases eq_or_lt_of_le hq_nn with hq0 | hq_pos
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with α (hα : α < 1)
      have hg_pos : 0 < gamma α := gamma_pos hα
      rw [← hq0, Real.zero_rpow hg_pos.ne']
    · exact (tendsto_rpow_atTop_of_base_lt_one q (by linarith) hq_lt1).comp tendsto_gamma_atTop
  have hu_tend : Tendsto u (𝓝[<] 1) (𝓝 (Real.sign r₁)) := by
    have h0 : Tendsto (fun α => (N₂ / N₁) * Real.sign r₂ * q ^ (gamma α)) (𝓝[<] 1) (𝓝 0) := by
      simpa using hq_tend.const_mul ((N₂ / N₁) * Real.sign r₂)
    simpa [u] using tendsto_const_nhds.add h0
  have hu_sgn : ∀ᶠ α in 𝓝[<] (1 : ℝ), Real.sign (u α) = Real.sign r₁ := by
    rcases lt_or_gt_of_ne hr1_ne with hneg | hpos
    · have hs : Real.sign r₁ = -1 := Real.sign_of_neg hneg
      rw [hs] at hu_tend ⊢
      filter_upwards [hu_tend.eventually (Iio_mem_nhds (by norm_num : (-1 : ℝ) < 0))] with α hα
      exact Real.sign_of_neg hα
    · have hs : Real.sign r₁ = 1 := Real.sign_of_pos hpos
      rw [hs] at hu_tend ⊢
      filter_upwards [hu_tend.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))] with α hα
      exact Real.sign_of_pos hα
  have hI_eq : ∀ α < (1 : ℝ),
      I_twoway W₁ N₁ W₂ N₂ α = (N₁ * |r₁| ^ gamma α) * u α := by
    intro α _
    rw [I_twoway_rate_form hN₁ hN₂]
    have hr2_eq : |r₂| ^ gamma α = q ^ gamma α * |r₁| ^ gamma α := by
      rw [show |r₂| = q * |r₁| by dsimp [q]; field_simp [hr1_abs_pos.ne'],
          Real.mul_rpow hq_nn hr1_abs_pos.le]
    unfold signedPow
    rw [hr2_eq]
    dsimp [u]
    field_simp [hN₁.ne']
    ring
  have hZ_eq : ∀ᶠ α in 𝓝[<] (1 : ℝ),
      Z_twoway W₁ N₁ W₂ N₂ α = Real.sign r₁ * (N₁ ^ (1 - α) * |r₁| * |u α| ^ (1 - α)) := by
    filter_upwards [self_mem_nhdsWithin, hu_sgn] with α (hα : α < 1) hs_u
    have hg_pos : 0 < gamma α := gamma_pos hα
    have hfac_pos : 0 < N₁ * |r₁| ^ gamma α := mul_pos hN₁ (Real.rpow_pos_of_pos hr1_abs_pos _)
    have hI := hI_eq α hα
    have hs_I : Real.sign (I_twoway W₁ N₁ W₂ N₂ α) = Real.sign (u α) := by
      rw [hI]
      rcases lt_trichotomy (u α) 0 with hun | hu0 | hup
      · rw [Real.sign_of_neg hun, Real.sign_of_neg (mul_neg_of_pos_of_neg hfac_pos hun)]
      · simp [hu0, Real.sign_zero]
      · rw [Real.sign_of_pos hup, Real.sign_of_pos (mul_pos hfac_pos hup)]
    have habs_I : |I_twoway W₁ N₁ W₂ N₂ α| ^ (1 - α) =
        N₁ ^ (1 - α) * |r₁| * |u α| ^ (1 - α) := by
      rw [hI, abs_mul, abs_of_pos hfac_pos,
          Real.mul_rpow hfac_pos.le (abs_nonneg _),
          Real.mul_rpow hN₁.le (Real.rpow_nonneg hr1_abs_pos.le _),
          ← Real.rpow_mul hr1_abs_pos.le,
          show gamma α * (1 - α) = 1 by unfold gamma; field_simp [(sub_pos.mpr hα).ne'],
          Real.rpow_one]
    unfold Z_twoway signedPow
    rw [one_div_gamma, hs_I, hs_u, habs_I]
  have hu_abs_tend : Tendsto (fun α => |u α| ^ (1 - α)) (𝓝[<] 1) (𝓝 1) := by
    have h_abs : Tendsto (fun α => |u α|) (𝓝[<] 1) (𝓝 |Real.sign r₁|) :=
      (continuous_abs.continuousAt.tendsto).comp hu_tend
    have hsabs : |Real.sign r₁| = 1 := by
      rcases lt_or_gt_of_ne hr1_ne with hneg | hpos
      · rw [Real.sign_of_neg hneg]; norm_num
      · rw [Real.sign_of_pos hpos]; norm_num
    rw [hsabs] at h_abs
    have h_exp : Tendsto (fun α : ℝ => 1 - α) (𝓝[<] 1) (𝓝 0) := by
      have hc : ContinuousAt (fun α : ℝ => 1 - α) 1 := continuousAt_const.sub continuousAt_id
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    have hcont_rpow : ContinuousAt (fun p : ℝ × ℝ => p.1 ^ p.2) (1, 0) :=
      continuousAt_fst.rpow continuousAt_snd (Or.inl one_ne_zero)
    have hpair : Tendsto (fun α => (|u α|, 1 - α)) (𝓝[<] 1) (𝓝 (1, 0)) := h_abs.prodMk_nhds h_exp
    simpa using (hcont_rpow.tendsto.comp hpair)
  have hprod : Tendsto (fun α => Real.sign r₁ * (N₁ ^ (1 - α) * |r₁| * |u α| ^ (1 - α)))
      (𝓝[<] 1) (𝓝 (Real.sign r₁ * (1 * |r₁| * 1))) :=
    tendsto_const_nhds.mul (((tendsto_rpow_one_sub hN₁).mul_const |r₁|).mul hu_abs_tend)
  have hlim : Real.sign r₁ * (1 * |r₁| * 1) = r₁ := by
    calc Real.sign r₁ * (1 * |r₁| * 1) = Real.sign r₁ * |r₁| := by ring
      _ = r₁ := real_sign_mul_abs r₁
  rw [hlim] at hprod
  exact hprod.congr' (EventuallyEq.symm hZ_eq)

private lemma signedPow_cancel {r g : ℝ} (hg : 0 < g) :
    signedPow (signedPow r g) (1 / g) = r := by
  have hinv : 0 < 1 / g := one_div_pos.mpr hg
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · rw [signedPow_neg hr]
    have hneg : -((-r) ^ g) < 0 := by linarith [Real.rpow_pos_of_pos (neg_pos.mpr hr) g]
    rw [signedPow_neg hneg, neg_neg, ← Real.rpow_mul (neg_pos.mpr hr).le,
        mul_one_div_cancel hg.ne', Real.rpow_one]
    ring
  · rw [signedPow_zero_left hg, signedPow_zero_left hinv]
  · rw [signedPow_nonneg hr.le hg,
        signedPow_nonneg (Real.rpow_nonneg hr.le g) hinv,
        ← Real.rpow_mul hr.le, mul_one_div_cancel hg.ne', Real.rpow_one]

private lemma Z_twoway_tendsto_one_left_of_scale_eq {W₁ N₁ W₂ N₂ c r : ℝ}
    (hc : 0 < c) (hI : ∀ α < (1 : ℝ), I_twoway W₁ N₁ W₂ N₂ α = c * signedPow r (gamma α)) :
    Tendsto (fun α => Z_twoway W₁ N₁ W₂ N₂ α) (𝓝[<] 1) (𝓝 r) := by
  have hev : ∀ᶠ α in 𝓝[<] (1 : ℝ), Z_twoway W₁ N₁ W₂ N₂ α = c ^ (1 - α) * r := by
    filter_upwards [self_mem_nhdsWithin] with α (hα : α < 1)
    unfold Z_twoway
    rw [hI α hα, signedPow_mul_pos hc, one_div_gamma]
    rw [← one_div_gamma, signedPow_cancel (gamma_pos hα)]
  have hlim : Tendsto (fun α : ℝ => c ^ (1 - α) * r) (𝓝[<] 1) (𝓝 (1 * r)) :=
    (tendsto_rpow_one_sub hc).mul_const r
  rw [one_mul] at hlim
  exact hlim.congr' (EventuallyEq.symm hev)

/-- Sec. 5.4 (`sec:expert`, Table 5): as `α → 1⁻` (`γ → ∞`), `Z_{α,2D}` converges to the
coordinate rate `W_k / N_k` with larger absolute magnitude (covering all cases: `|r₁| > |r₂|`,
`|r₂| > |r₁|`, equal rates `r₁ = r₂`, and opposite equal-magnitude rates `r₁ = -r₂` across
`N₁ > N₂`, `N₂ > N₁`, and `N₁ = N₂`). -/
theorem Z_twoway_tendsto_one_left {W₁ N₁ W₂ N₂ : ℝ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) :
    (|W₁ / N₁| > |W₂ / N₂| →
      Tendsto (fun α => Z_twoway W₁ N₁ W₂ N₂ α) (𝓝[<] 1) (𝓝 (W₁ / N₁))) ∧
    (|W₂ / N₂| > |W₁ / N₁| →
      Tendsto (fun α => Z_twoway W₁ N₁ W₂ N₂ α) (𝓝[<] 1) (𝓝 (W₂ / N₂))) ∧
    (W₁ / N₁ = W₂ / N₂ →
      Tendsto (fun α => Z_twoway W₁ N₁ W₂ N₂ α) (𝓝[<] 1) (𝓝 (W₁ / N₁))) ∧
    (W₁ / N₁ = -(W₂ / N₂) → N₁ > N₂ →
      Tendsto (fun α => Z_twoway W₁ N₁ W₂ N₂ α) (𝓝[<] 1) (𝓝 (W₁ / N₁))) ∧
    (W₁ / N₁ = -(W₂ / N₂) → N₂ > N₁ →
      Tendsto (fun α => Z_twoway W₁ N₁ W₂ N₂ α) (𝓝[<] 1) (𝓝 (W₂ / N₂))) ∧
    (W₁ / N₁ = -(W₂ / N₂) → N₁ = N₂ →
      Tendsto (fun α => Z_twoway W₁ N₁ W₂ N₂ α) (𝓝[<] 1) (𝓝 0)) := by
  refine ⟨fun hgt => Z_twoway_tendsto_one_left_of_abs_gt hN₁ hN₂ hgt, fun hgt => ?_,
    fun heq => ?_, fun hneg hN => ?_, fun hneg hN => ?_, fun hneg hN => ?_⟩
  · have hswap : (fun α => Z_twoway W₁ N₁ W₂ N₂ α) = fun α => Z_twoway W₂ N₂ W₁ N₁ α := by
      ext α; unfold Z_twoway I_twoway; rw [add_comm]
    rw [hswap]
    exact Z_twoway_tendsto_one_left_of_abs_gt hN₂ hN₁ hgt
  · refine Z_twoway_tendsto_one_left_of_scale_eq (add_pos hN₁ hN₂) fun α _ => ?_
    rw [I_twoway_rate_form hN₁ hN₂, ← heq]
    ring
  · refine Z_twoway_tendsto_one_left_of_scale_eq (sub_pos.mpr hN) fun α _ => ?_
    rw [I_twoway_rate_form hN₁ hN₂]
    have hr2 : W₂ / N₂ = -(W₁ / N₁) := by linarith
    rw [hr2, signedPow_neg_left]
    ring
  · refine Z_twoway_tendsto_one_left_of_scale_eq (sub_pos.mpr hN) fun α _ => ?_
    rw [I_twoway_rate_form hN₁ hN₂, hneg, signedPow_neg_left]
    ring
  · have hev : ∀ᶠ α in 𝓝[<] (1 : ℝ), Z_twoway W₁ N₁ W₂ N₂ α = 0 := by
      filter_upwards [self_mem_nhdsWithin] with α (hα : α < 1)
      have hI : I_twoway W₁ N₁ W₂ N₂ α = 0 := by
        rw [I_twoway_rate_form hN₁ hN₂, hneg, hN, signedPow_neg_left]
        ring
      unfold Z_twoway
      rw [hI, signedPow_zero_left (one_div_pos.mpr (gamma_pos hα))]
    exact tendsto_const_nhds.congr' (EventuallyEq.symm hev)

/-- Remark 4 (`rem:mvp`): when `N_H < N_P` and `W_P, W_H > 0`, the pitcher-to-hitter score ratio
`Z_α(W_P, N_P) / Z_α(W_H, N_H)` is strictly decreasing in `α`. -/
theorem cross_role_ratio_strictAnti {W_P N_P W_H N_H : ℝ}
    (hW_P : 0 < W_P) (hW_H : 0 < W_H) (hN_P : 0 < N_P) (hN_H : 0 < N_H) (hNP_gt : N_H < N_P) :
    StrictAnti (fun α : ℝ => Z_alpha W_P N_P α / Z_alpha W_H N_H α) := by
  intro α₁ α₂ hα
  dsimp only
  rw [cross_role_ratio_scaling hN_P hN_H hW_H.ne' (α₁ := α₁) (α₂ := α₂)]
  have hbase_pos : 0 < N_H / N_P := div_pos hN_H hN_P
  have hbase_lt : N_H / N_P < 1 := (div_lt_one hN_P).mpr hNP_gt
  have hpow_lt : (N_H / N_P) ^ (α₂ - α₁) < 1 :=
    Real.rpow_lt_one hbase_pos.le hbase_lt (sub_pos.mpr hα)
  have hratio_pos : 0 < Z_alpha W_P N_P α₁ / Z_alpha W_H N_H α₁ := by
    unfold Z_alpha; positivity
  nlinarith

/-- Appendix B (`app:twoway`): mapping the `χ²_2` tail probability back to `χ²_1` strictly
shrinks every positive threshold (`t_cal < t`). -/
theorem chi2_calibration_shrinks (v : ℝ≥0) (hv : v ≠ 0) {σ t t_cal : ℝ}
    (hσ : 0 < σ) (ht : 0 < t)
    (hmatch : (gaussianReal 0 v).prod (gaussianReal 0 v) {p | t_cal ≤ p.1 ^ 2 / σ ^ 2} =
      (gaussianReal 0 v).prod (gaussianReal 0 v) {p | t ≤ (p.1 ^ 2 + p.2 ^ 2) / σ ^ 2}) :
    t_cal < t := by
  by_contra hle
  have ht_le : t ≤ t_cal := le_of_not_gt hle
  let μp : Measure (ℝ × ℝ) := (gaussianReal 0 v).prod (gaussianReal 0 v)
  have hmono : μp {p | t_cal ≤ p.1 ^ 2 / σ ^ 2} ≤ μp {p | t ≤ p.1 ^ 2 / σ ^ 2} :=
    measure_mono fun p hp => ht_le.trans hp
  have hstrict := chi2_dominance_gaussian_strict v hv hσ ht
  have hlt : μp {p | t_cal ≤ p.1 ^ 2 / σ ^ 2} < μp {p | t ≤ (p.1 ^ 2 + p.2 ^ 2) / σ ^ 2} :=
    hmono.trans_lt hstrict
  exact hlt.ne hmatch

section NoiseAndOppSignDelta

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Section 3.3 (`sec:zstat`): persistent positive covariance (`Cov ≥ 0` with at least one
strictly positive pair) with `SD(W) = σ n^α` (`n ≥ 2`, `σ > 0`) forces `1/2 < α`. -/
theorem prop_frequentist_pos_cov_sd_gt_half {n : ℕ} (hn : 2 ≤ n) (w : Fin n → Ω → ℝ)
    {σ α : ℝ} (hσ : 0 < σ)
    (hL2 : ∀ i, MemLp (w i) 2 μ)
    (hvar : ∀ i, variance (w i) μ = σ ^ 2)
    (hcov_nn : ∀ i j, i ≠ j → 0 ≤ cov[w i, w j; μ])
    (hcov_pos : ∃ i j, i ≠ j ∧ 0 < cov[w i, w j; μ])
    (hsd : Real.sqrt (variance (fun ω => ∑ i, w i ω) μ) = σ * (n : ℝ) ^ α) :
    1 / 2 < α := by
  obtain ⟨i0, j0, hij, hcov0⟩ := hcov_pos
  have hrow_ge : ∀ i : Fin n, σ ^ 2 ≤ ∑ j : Fin n, cov[w i, w j; μ] := by
    intro i
    rw [← Finset.add_sum_erase Finset.univ (fun j => cov[w i, w j; μ]) (Finset.mem_univ i),
        covariance_self (hL2 i).aemeasurable, hvar i]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun j hj =>
      hcov_nn i j (Finset.ne_of_mem_erase hj).symm)
  have hrow_gt : σ ^ 2 < ∑ j : Fin n, cov[w i0, w j; μ] := by
    rw [← Finset.add_sum_erase Finset.univ (fun j => cov[w i0, w j; μ]) (Finset.mem_univ i0),
        covariance_self (hL2 i0).aemeasurable, hvar i0]
    have hj0_mem : j0 ∈ Finset.univ.erase i0 := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j0⟩
    have hsum_pos : 0 < ∑ j ∈ Finset.univ.erase i0, cov[w i0, w j; μ] :=
      hcov0.trans_le (Finset.single_le_sum
        (fun j hj => hcov_nn i0 j (Finset.ne_of_mem_erase hj).symm) hj0_mem)
    linarith
  have hvar_gt : (n : ℝ) * σ ^ 2 < variance (fun ω => ∑ i, w i ω) μ := by
    rw [variance_fun_sum hL2]
    calc (n : ℝ) * σ ^ 2
        = ∑ _i : Fin n, σ ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ < ∑ i : Fin n, ∑ j : Fin n, cov[w i, w j; μ] :=
          Finset.sum_lt_sum (fun i _ => hrow_ge i) ⟨i0, Finset.mem_univ i0, hrow_gt⟩
  have hn_pos : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hvar_eq : variance (fun ω => ∑ i, w i ω) μ = σ ^ 2 * (n : ℝ) ^ (2 * α) := by
    have hsq := congrArg (· ^ 2) hsd
    dsimp only at hsq
    rw [Real.sq_sqrt (variance_nonneg _ _), mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ α) 2,
        ← Real.rpow_mul hn_pos.le] at hsq
    rw [show α * ((2 : ℕ) : ℝ) = 2 * α by ring] at hsq
    exact hsq
  rw [hvar_eq, mul_comm (n : ℝ) (σ ^ 2), mul_lt_mul_iff_right₀ (sq_pos_of_pos hσ)] at hvar_gt
  conv_lhs at hvar_gt => rw [← Real.rpow_one (n : ℝ)]
  have hexp := (Real.rpow_lt_rpow_left_iff hn1).mp hvar_gt
  linarith

/-- Appendix H (`app:uncert`): under opposite-sign expectations (`μ₁ μ₂ < 0`) away from
the cancellation locus (`μ₁² / PA ≠ μ₂² / BF`), the first-order delta-method linearization of
`Z_{1/2, 2D}` at `(μ₁, μ₂)` has exact variance `((z₁² + z₂²) / |z₁² - z₂²|) σ² > σ²`. -/
theorem delta_method_Z_twoway_half_opp_sign_linear_var (W₁ W₂ : Ω → ℝ) {PA BF μ₁ μ₂ σ : ℝ}
    (h1 : MemLp W₁ 2 μ) (h2 : MemLp W₂ 2 μ)
    (huncorr : cov[W₁, W₂; μ] = 0)
    (hv1 : variance W₁ μ = PA * σ ^ 2) (hv2 : variance W₂ μ = BF * σ ^ 2)
    (hPA : 0 < PA) (hBF : 0 < BF) (hσ : 0 < σ)
    (hopp : (0 < μ₁ ∧ μ₂ < 0) ∨ (μ₁ < 0 ∧ 0 < μ₂))
    (hne : μ₁ ^ 2 / PA ≠ μ₂ ^ 2 / BF) :
    let z₁ := Z_alpha μ₁ PA (1 / 2)
    let z₂ := Z_alpha μ₂ BF (1 / 2)
    variance (fun ω =>
      fderiv ℝ (fun w : ℝ × ℝ => Z_twoway w.1 PA w.2 BF (1 / 2)) (μ₁, μ₂)
        (W₁ ω - μ₁, W₂ ω - μ₂)) μ =
      ((z₁ ^ 2 + z₂ ^ 2) / |z₁ ^ 2 - z₂ ^ 2|) * σ ^ 2 ∧
    σ ^ 2 < variance (fun ω =>
      fderiv ℝ (fun w : ℝ × ℝ => Z_twoway w.1 PA w.2 BF (1 / 2)) (μ₁, μ₂)
        (W₁ ω - μ₁, W₂ ω - μ₂)) μ := by
  intro z₁ z₂
  have hg : gamma (1 / 2 : ℝ) = 2 := by unfold gamma; norm_num
  have hz1_sq : z₁ ^ 2 = μ₁ ^ 2 / PA := by
    dsimp [z₁, Z_alpha]
    rw [div_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hPA.le]
  have hz2_sq : z₂ ^ 2 = μ₂ ^ 2 / BF := by
    dsimp [z₂, Z_alpha]
    rw [div_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hBF.le]
  have hI_eq : |I_twoway μ₁ PA μ₂ BF (1 / 2)| = |z₁ ^ 2 - z₂ ^ 2| := by
    unfold I_twoway
    rw [hg, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_one, hz1_sq, hz2_sq]
    rcases hopp with ⟨hμ1, hμ2⟩ | ⟨hμ1, hμ2⟩
    · rw [signedPow_nonneg hμ1.le (by norm_num), signedPow_neg hμ2, Real.rpow_two, Real.rpow_two]
      congr 1; ring
    · rw [signedPow_neg hμ1, signedPow_nonneg hμ2.le (by norm_num), Real.rpow_two, Real.rpow_two]
      rw [neg_sq, show -(μ₁ ^ 2) / PA + μ₂ ^ 2 / BF = -(μ₁ ^ 2 / PA - μ₂ ^ 2 / BF) by ring, abs_neg]
  have hdiff_pos : 0 < |z₁ ^ 2 - z₂ ^ 2| := by
    rw [hz1_sq, hz2_sq]
    exact abs_pos.mpr (sub_ne_zero.mpr hne)
  have hI_ne : I_twoway μ₁ PA μ₂ BF (1 / 2) ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hI_eq
    linarith
  have hfd := Z_twoway_hasFDerivAt (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    hPA hBF hI_ne
  rw [hfd.fderiv]
  let D : ℝ := |Z_twoway μ₁ PA μ₂ BF (1 / 2)|
  have hD_eq : D = Real.sqrt |z₁ ^ 2 - z₂ ^ 2| := by
    dsimp [D]
    unfold Z_twoway signedPow
    rw [hg, show (1 : ℝ) / 2 = 1 / 2 by norm_num, abs_mul]
    have hs : |Real.sign (I_twoway μ₁ PA μ₂ BF (1 / 2))| = 1 := by
      rcases lt_or_gt_of_ne hI_ne with hn | hp
      · rw [Real.sign_of_neg hn]; norm_num
      · rw [Real.sign_of_pos hp]; norm_num
    rw [hs, one_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), hI_eq, Real.sqrt_eq_rpow]
  have hD_pos : 0 < D := by rw [hD_eq]; exact Real.sqrt_pos.mpr hdiff_pos
  have hD_sq : D ^ 2 = |z₁ ^ 2 - z₂ ^ 2| := by rw [hD_eq, Real.sq_sqrt hdiff_pos.le]
  let c₁ : ℝ := (|μ₁| / PA) ^ (gamma (1 / 2) - 1) * D ^ (1 - gamma (1 / 2))
  let c₂ : ℝ := (|μ₂| / BF) ^ (gamma (1 / 2) - 1) * D ^ (1 - gamma (1 / 2))
  have heval : (fun ω =>
      (c₁ • ContinuousLinearMap.fst ℝ ℝ ℝ + c₂ • ContinuousLinearMap.snd ℝ ℝ ℝ)
        (W₁ ω - μ₁, W₂ ω - μ₂)) =
      fun ω => (c₁ * W₁ ω + c₂ * W₂ ω) - (c₁ * μ₁ + c₂ * μ₂) := by
    ext ω
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
    ring
  have hvar_eq : variance (fun ω =>
      (c₁ • ContinuousLinearMap.fst ℝ ℝ ℝ + c₂ • ContinuousLinearMap.snd ℝ ℝ ℝ)
        (W₁ ω - μ₁, W₂ ω - μ₂)) μ = ((z₁ ^ 2 + z₂ ^ 2) / |z₁ ^ 2 - z₂ ^ 2|) * σ ^ 2 := by
    rw [heval]
    have hL2_1 : MemLp (fun ω => c₁ * W₁ ω) 2 μ := h1.const_mul c₁
    have hL2_2 : MemLp (fun ω => c₂ * W₂ ω) 2 μ := h2.const_mul c₂
    have hL2_sum : MemLp (fun ω => c₁ * W₁ ω + c₂ * W₂ ω) 2 μ := hL2_1.add hL2_2
    rw [variance_sub_const hL2_sum.aestronglyMeasurable, variance_fun_add hL2_1 hL2_2]
    have hcov : cov[fun ω => c₁ * W₁ ω, fun ω => c₂ * W₂ ω; μ] = 0 := by
      rw [covariance_const_mul_left, covariance_const_mul_right, huncorr, mul_zero, mul_zero]
    rw [hcov, variance_const_mul, variance_const_mul, hv1, hv2]
    have hc1_eq : c₁ = (|μ₁| / PA) / D := by
      dsimp [c₁]
      rw [hg, show (2 : ℝ) - 1 = 1 by norm_num, show (1 : ℝ) - 2 = -1 by norm_num,
          Real.rpow_one, Real.rpow_neg_one, ← div_eq_mul_inv]
    have hc2_eq : c₂ = (|μ₂| / BF) / D := by
      dsimp [c₂]
      rw [hg, show (2 : ℝ) - 1 = 1 by norm_num, show (1 : ℝ) - 2 = -1 by norm_num,
          Real.rpow_one, Real.rpow_neg_one, ← div_eq_mul_inv]
    have hcoeff : c₁ ^ 2 * PA + c₂ ^ 2 * BF = (z₁ ^ 2 + z₂ ^ 2) / |z₁ ^ 2 - z₂ ^ 2| := by
      rw [hc1_eq, hc2_eq, div_pow, div_pow, div_pow, div_pow, sq_abs μ₁, sq_abs μ₂, hD_sq]
      have hPAne : PA ≠ 0 := hPA.ne'
      have hBFne : BF ≠ 0 := hBF.ne'
      have hDne : |z₁ ^ 2 - z₂ ^ 2| ≠ 0 := hdiff_pos.ne'
      rw [hz1_sq, hz2_sq]
      field_simp [hPAne, hBFne, hDne]
    calc c₁ ^ 2 * (PA * σ ^ 2) + 2 * 0 + c₂ ^ 2 * (BF * σ ^ 2)
        = (c₁ ^ 2 * PA + c₂ ^ 2 * BF) * σ ^ 2 := by ring
      _ = ((z₁ ^ 2 + z₂ ^ 2) / |z₁ ^ 2 - z₂ ^ 2|) * σ ^ 2 := by rw [hcoeff]
  refine ⟨hvar_eq, ?_⟩
  rw [hvar_eq]
  have hz1_ne : z₁ ≠ 0 := by
    dsimp [z₁, Z_alpha]
    rcases hopp with ⟨h1', _⟩ | ⟨h1', _⟩
    · exact div_ne_zero h1'.ne' (Real.rpow_pos_of_pos hPA _).ne'
    · exact div_ne_zero h1'.ne (Real.rpow_pos_of_pos hPA _).ne'
  have hz2_ne : z₂ ≠ 0 := by
    dsimp [z₂, Z_alpha]
    rcases hopp with ⟨_, h2'⟩ | ⟨_, h2'⟩
    · exact div_ne_zero h2'.ne (Real.rpow_pos_of_pos hBF _).ne'
    · exact div_ne_zero h2'.ne' (Real.rpow_pos_of_pos hBF _).ne'
  have hmult_gt : 1 < (z₁ ^ 2 + z₂ ^ 2) / |z₁ ^ 2 - z₂ ^ 2| := by
    rw [one_lt_div hdiff_pos]
    have h1p : 0 < z₁ ^ 2 := sq_pos_of_ne_zero hz1_ne
    have h2p : 0 < z₂ ^ 2 := sq_pos_of_ne_zero hz2_ne
    rcases abs_cases (z₁ ^ 2 - z₂ ^ 2) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  calc σ ^ 2 = 1 * σ ^ 2 := (one_mul _).symm
    _ < ((z₁ ^ 2 + z₂ ^ 2) / |z₁ ^ 2 - z₂ ^ 2|) * σ ^ 2 :=
        mul_lt_mul_of_pos_right hmult_gt (sq_pos_of_pos hσ)

end NoiseAndOppSignDelta

/-! ### 15.11 Proposition 1 Discrete Decline-Phase Behavior (`prop:alpha`, Sec. 3.1) -/

/-- Proposition 1 (`prop:alpha`, Sec. 3.1): for `0 < W`, `0 < N`, `0 < ΔN`, `α ∈ (0, 1]`,
and any non-positive marginal block (`r_marg ≤ 0`), `Z_α` strictly decreases. -/
theorem prop_alpha_discrete_nonpos_lt {W N ΔN α r_marg : ℝ}
    (hW : 0 < W) (hN : 0 < N) (hΔN : 0 < ΔN) (hα0 : 0 < α) (hα1 : α ≤ 1) (hr : r_marg ≤ 0) :
    Z_alpha (W + r_marg * ΔN) (N + ΔN) α < Z_alpha W N α := by
  have _ : α ≤ 1 := hα1
  have hN_add : 0 < N + ΔN := by linarith
  have hpow_pos : 0 < N ^ α := Real.rpow_pos_of_pos hN α
  have hpow_add_pos : 0 < (N + ΔN) ^ α := Real.rpow_pos_of_pos hN_add α
  have hpow_lt : N ^ α < (N + ΔN) ^ α :=
    Real.rpow_lt_rpow hN.le (by linarith) hα0
  have hnum_le : W + r_marg * ΔN ≤ W := by
    nlinarith
  unfold Z_alpha
  calc (W + r_marg * ΔN) / (N + ΔN) ^ α
      ≤ W / (N + ΔN) ^ α := div_le_div_of_nonneg_right hnum_le hpow_add_pos.le
    _ < W / N ^ α := div_lt_div_of_pos_left hW hpow_pos hpow_lt

/-- Proposition 1 (`prop:alpha`, Sec. 3.1): for `α ∈ (0, 1)` and `0 < N`, the discrete
relative threshold `((1 + ΔN / N) ^ α - 1) / (ΔN / N)` shrinks to `0` as `ΔN → ∞`. -/
theorem prop_alpha_discrete_threshold_tendsto_zero {N α : ℝ}
    (hN : 0 < N) (hα0 : 0 < α) (hα1 : α < 1) :
    Tendsto (fun ΔN => ((1 + ΔN / N) ^ α - 1) / (ΔN / N)) atTop (𝓝 0) := by
  have hx_tend : Tendsto (fun x : ℝ => ((1 + x) ^ α - 1) / x) atTop (𝓝 0) := by
    have hnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ ((1 + x) ^ α - 1) / x := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have h1x : 1 < 1 + x := by linarith
      have hpow : 1 < (1 + x) ^ α := Real.one_lt_rpow h1x hα0
      exact div_nonneg (sub_nonneg.mpr hpow.le) hx.le
    have hle : ∀ᶠ x : ℝ in atTop, ((1 + x) ^ α - 1) / x ≤ (2 : ℝ) ^ α * x ^ (α - 1) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
      have h1x_le : 1 + x ≤ 2 * x := by linarith
      have hpow_le : (1 + x) ^ α ≤ (2 * x) ^ α :=
        Real.rpow_le_rpow (by linarith) h1x_le hα0.le
      have hpow_mul : (2 * x) ^ α = (2 : ℝ) ^ α * x ^ α :=
        Real.mul_rpow (by norm_num) hx_pos.le
      have hsub_le : (1 + x) ^ α - 1 ≤ (2 : ℝ) ^ α * x ^ α := by linarith
      calc ((1 + x) ^ α - 1) / x
          ≤ ((2 : ℝ) ^ α * x ^ α) / x := div_le_div_of_nonneg_right hsub_le hx_pos.le
        _ = (2 : ℝ) ^ α * (x ^ α / x) := by ring
        _ = (2 : ℝ) ^ α * x ^ (α - 1) := by rw [Real.rpow_sub hx_pos, Real.rpow_one]
    have hdom : Tendsto (fun x : ℝ => (2 : ℝ) ^ α * x ^ (α - 1)) atTop (𝓝 0) := by
      have hexp : 0 < 1 - α := sub_pos.mpr hα1
      have hpow_atTop : Tendsto (fun x : ℝ => x ^ (1 - α)) atTop atTop :=
        tendsto_rpow_atTop hexp
      have hinv : Tendsto (fun x : ℝ => (x ^ (1 - α))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp hpow_atTop
      have hneg_pow : Tendsto (fun x : ℝ => x ^ (α - 1)) atTop (𝓝 0) := by
        refine hinv.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        rw [← Real.rpow_neg hx.le]
        congr 1
        ring
      simpa using hneg_pow.const_mul ((2 : ℝ) ^ α)
    exact squeeze_zero' hnonneg hle hdom
  have hdiv : Tendsto (fun ΔN : ℝ => ΔN / N) atTop atTop := by
    have h : Tendsto (fun ΔN : ℝ => ΔN * N⁻¹) atTop atTop :=
      tendsto_id.atTop_mul_const (inv_pos.mpr hN)
    simpa [div_eq_mul_inv] using h
  exact hx_tend.comp hdiv

/-- Proposition 1 (`prop:alpha`, Sec. 3.1): for `0 < W`, `0 < N`, `α ∈ (0, 1)`, and any fixed
positive marginal rate `0 < r_marg` (even when `r_marg < α * (W / N)`), a sufficiently long
block `ΔN` eventually raises `Z_α` above its pre-block value. -/
theorem prop_alpha_discrete_fixed_pos_eventually_gt {W N α r_marg : ℝ}
    (hW : 0 < W) (hN : 0 < N) (hα0 : 0 < α) (hα1 : α < 1) (hr : 0 < r_marg) :
    ∀ᶠ ΔN in atTop, Z_alpha W N α < Z_alpha (W + r_marg * ΔN) (N + ΔN) α := by
  have hr_bar : 0 < W / N := div_pos hW hN
  have hev : ∀ᶠ ΔN : ℝ in atTop,
      ((1 + ΔN / N) ^ α - 1) / (ΔN / N) < r_marg / (W / N) :=
    (prop_alpha_discrete_threshold_tendsto_zero hN hα0 hα1).eventually
      (Iio_mem_nhds (div_pos hr hr_bar))
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with ΔN hlt hΔN
  have hdiv : (r_marg * ΔN) / ΔN = r_marg := mul_div_cancel_right₀ r_marg hΔN.ne'
  have hthresh : (((1 + ΔN / N) ^ α - 1) / (ΔN / N)) * (W / N) < r_marg :=
    (lt_div_iff₀ hr_bar).mp hlt
  exact (prop_alpha_discrete_iff hN hΔN).mpr (by rw [hdiv]; exact hthresh)

/-! ### 15.12 Adversarial Audit Additions: Shrinkage, Discrete Threshold Crossover, Concordance/AUC, OLS Residual Variance, Two-Way Orthant Rounding, One-Sided χ² Calibration, and Benchmarks -/

/-- Sec. 1 Eq. (3): the convex combination weights in `r_EB` are strictly positive (`N/(N+N₀) > 0`)
and non-negative (`N₀/(N+N₀) ≥ 0`), and when `N₀ > 0` and `W/N ≠ r₀`, `r_EB` strictly shrinks
the distance to the prior `r₀`. -/
theorem r_EB_convex_weights_nonneg {N N₀ : ℝ} (hN : 0 < N) (hN₀ : 0 ≤ N₀) :
    0 < N / (N + N₀) ∧ 0 ≤ N₀ / (N + N₀) ∧ N / (N + N₀) + N₀ / (N + N₀) = 1 := by
  have hsum : 0 < N + N₀ := by linarith
  refine ⟨div_pos hN hsum, div_nonneg hN₀ hsum.le, ?_⟩
  field_simp [hsum.ne']

theorem r_EB_shrinks_dist {W N N₀ r₀ : ℝ} (hN : 0 < N) (hN₀ : 0 < N₀) (hne : W / N ≠ r₀) :
    |r_EB W N N₀ r₀ - r₀| = (N / (N + N₀)) * |W / N - r₀| ∧
      |r_EB W N N₀ r₀ - r₀| < |W / N - r₀| := by
  have hsum : 0 < N + N₀ := by linarith
  have hdiff : r_EB W N N₀ r₀ - r₀ = (N / (N + N₀)) * (W / N - r₀) := by
    unfold r_EB
    field_simp [hN.ne', hsum.ne']
    ring
  have hweight_pos : 0 < N / (N + N₀) := div_pos hN hsum
  have hweight_lt : N / (N + N₀) < 1 := (div_lt_one hsum).mpr (by linarith)
  have heq : |r_EB W N N₀ r₀ - r₀| = (N / (N + N₀)) * |W / N - r₀| := by
    rw [hdiff, abs_mul, abs_of_pos hweight_pos]
  have hdist_pos : 0 < |W / N - r₀| := abs_pos.mpr (sub_ne_zero.mpr hne)
  refine ⟨heq, ?_⟩
  rw [heq]
  nlinarith

/-- Prop. 1 (`prop:alpha`, Eq. 6): discrete threshold equivalence for strict decrease and tie. -/
theorem prop_alpha_discrete_lt_iff {W N ΔW ΔN α : ℝ} (hN : 0 < N) (hΔN : 0 < ΔN) :
    Z_alpha (W + ΔW) (N + ΔN) α < Z_alpha W N α ↔
      ΔW / ΔN < (((1 + ΔN / N) ^ α - 1) / (ΔN / N)) * (W / N) := by
  unfold Z_alpha
  have hN_add : 0 < N + ΔN := by linarith
  have hpowN : 0 < N ^ α := Real.rpow_pos_of_pos hN α
  have hpowN_add : 0 < (N + ΔN) ^ α := Real.rpow_pos_of_pos hN_add α
  have hratio : (N + ΔN) / N = 1 + ΔN / N := by field_simp [hN.ne']
  have hpow_ratio : (N + ΔN) ^ α / N ^ α = (1 + ΔN / N) ^ α := by
    rw [← Real.div_rpow hN_add.le hN.le, hratio]
  have hrhs :
      (((1 + ΔN / N) ^ α - 1) / (ΔN / N)) * (W / N) =
        (((N + ΔN) ^ α / N ^ α - 1) * W) / ΔN := by
    rw [hpow_ratio]
    field_simp [hN.ne', hΔN.ne']
  rw [hrhs, div_lt_div_iff₀ hpowN_add hpowN, div_lt_div_iff₀ hΔN hΔN]
  have hmul :
      (W + ΔW) * N ^ α < W * (N + ΔN) ^ α ↔
        ΔW < ((N + ΔN) ^ α / N ^ α - 1) * W := by
    calc (W + ΔW) * N ^ α < W * (N + ΔN) ^ α
        ↔ ((W + ΔW) * N ^ α) / N ^ α < (W * (N + ΔN) ^ α) / N ^ α :=
          (div_lt_div_iff_of_pos_right hpowN).symm
      _ ↔ W + ΔW < ((N + ΔN) ^ α / N ^ α) * W := by
          field_simp [hpowN.ne']
      _ ↔ ΔW < ((N + ΔN) ^ α / N ^ α - 1) * W := by
          constructor <;> intro h <;> linarith
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul.trans (mul_lt_mul_iff_left₀ hΔN).symm

theorem prop_alpha_discrete_eq_iff {W N ΔW ΔN α : ℝ} (hN : 0 < N) (hΔN : 0 < ΔN) :
    Z_alpha (W + ΔW) (N + ΔN) α = Z_alpha W N α ↔
      ΔW / ΔN = (((1 + ΔN / N) ^ α - 1) / (ΔN / N)) * (W / N) := by
  constructor
  · intro heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ((prop_alpha_discrete_lt_iff hN hΔN).mpr hlt).ne heq
    · exact ((prop_alpha_discrete_iff hN hΔN).mpr hgt).ne' heq
  · intro heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ((prop_alpha_discrete_lt_iff hN hΔN).mp hlt).ne heq
    · exact ((prop_alpha_discrete_iff hN hΔN).mp hgt).ne' heq

/-- Prop. 1 (`prop:alpha`, Eq. 6): right-hand Taylor expansion scaled by `r̄ = W / N` in terms of `ΔN`. -/
theorem prop_alpha_taylor_scaled_isBigO {W N α : ℝ} (hN : 0 < N) :
    (fun ΔN : ℝ =>
        (((1 + ΔN / N) ^ α - 1) / (ΔN / N)) * (W / N) -
          (α - α * (1 - α) / 2 * (ΔN / N)) * (W / N))
      =O[𝓝[>] (0 : ℝ)] (fun ΔN : ℝ => (ΔN / N) ^ 2) := by
  have hdiv : Tendsto (fun ΔN : ℝ => ΔN / N) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun ΔN : ℝ => ΔN / N) 0 := continuousAt_id.div_const N
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun ΔN (hΔN : 0 < ΔN) => div_pos hΔN hN
  have hcomp := ((prop_alpha_taylor_isBigO_nhdsGT α).comp_tendsto hdiv).const_mul_left (W / N)
  refine hcomp.congr' ?_ EventuallyEq.rfl
  refine Eventually.of_forall fun ΔN => ?_
  dsimp [Function.comp_def]
  ring

/-- Prop. 1 (`prop:alpha`, Sec. 3.1): as `x → 0` (`x ≠ 0`), the discrete threshold factor
`((1 + x)^α - 1) / x` converges to the continuous exponent `α`. -/
theorem prop_alpha_discrete_threshold_tendsto_continuous (α : ℝ) :
    Tendsto (fun x : ℝ => ((1 + x) ^ α - 1) / x) (𝓝[≠] 0) (𝓝 α) := by
  have hd_base : HasDerivAt (fun x : ℝ => 1 + x) 1 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) (1 : ℝ)).add (hasDerivAt_id (0 : ℝ))
  have hd_pow : HasDerivAt (fun x : ℝ => (1 + x) ^ α) α 0 := by
    simpa using hd_base.rpow_const (p := α) (Or.inl (by norm_num : (1 + (0 : ℝ)) ≠ 0))
  have hslope := hd_pow.tendsto_slope_zero
  refine hslope.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x _
  simp [div_eq_inv_mul]

/-- Prop. 1 (`prop:alpha`, Sec. 3.1): for `α ∈ (0, 1)`, the discrete relative threshold
`x ↦ ((1 + x)^α - 1) / x` is strictly decreasing on `(0, ∞)`. -/
theorem prop_alpha_discrete_threshold_strictAnti {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    StrictAntiOn (fun x : ℝ => ((1 + x) ^ α - 1) / x) (Ioi 0) := by
  let h : ℝ → ℝ := fun t => (1 + t) ^ (1 - α) - (1 + (1 - α) * t)
  have hh_deriv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt h ((1 - α) * ((1 + t) ^ (-α) - 1)) t := by
    intro t (ht : 0 ≤ t)
    have hpos : 0 < 1 + t := by linarith
    have hd1 : HasDerivAt (fun u : ℝ => (1 + u) ^ (1 - α))
        ((1 - α) * (1 + t) ^ ((1 - α) - 1)) t := by
      simpa using ((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)).rpow_const
        (p := 1 - α) (Or.inl hpos.ne')
    have hd2 : HasDerivAt (fun u : ℝ => 1 + (1 - α) * u) (1 - α) t := by
      convert (hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).const_mul (1 - α)) using 1
      simp
    convert hd1.sub hd2 using 1
    rw [show (1 - α) - 1 = -α by ring]
    ring
  have hh_anti : StrictAntiOn h (Ici 0) := by
    refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Ici 0)
      (f' := fun t => (1 - α) * ((1 + t) ^ (-α) - 1))
      (fun t ht => (hh_deriv t ht).continuousAt.continuousWithinAt) ?_ ?_
    · intro t ht
      rw [interior_Ici] at ht
      exact (hh_deriv t (Set.mem_Ioi.mp ht).le).hasDerivWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have h1t : 1 < 1 + t := by linarith [Set.mem_Ioi.mp ht]
      have hpow_lt : (1 + t) ^ (-α) < 1 := Real.rpow_lt_one_of_one_lt_of_neg h1t (neg_lt_zero.mpr hα0)
      exact mul_neg_of_pos_of_neg (sub_pos.mpr hα1) (sub_neg.mpr hpow_lt)
  have hbern : ∀ x : ℝ, 0 < x → (1 + x) ^ (1 - α) < 1 + (1 - α) * x := by
    intro x hx
    have hlt := hh_anti (Set.left_mem_Ici) hx.le hx
    have h0 : h 0 = 0 := by simp [h]
    rw [h0] at hlt
    exact sub_neg.mp hlt
  let g : ℝ → ℝ := fun x => ((1 + x) ^ α - 1) / x
  let g' : ℝ → ℝ := fun x => (1 - (1 + x) ^ (α - 1) * (1 + (1 - α) * x)) / x ^ 2
  have hg_deriv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt g (g' x) x := by
    intro x (hx : 0 < x)
    have hpos : 0 < 1 + x := by linarith
    have hd_num : HasDerivAt (fun t : ℝ => (1 + t) ^ α - 1) (α * (1 + x) ^ (α - 1)) x := by
      simpa using (((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).rpow_const
        (p := α) (Or.inl hpos.ne')).sub_const 1
    have hdiv := hd_num.div (hasDerivAt_id x) hx.ne'
    convert hdiv using 1
    have hpow_split : (1 + x) ^ α = (1 + x) ^ (α - 1) * (1 + x) := by
      calc (1 + x) ^ α = (1 + x) ^ ((α - 1) + 1) := by congr 1; ring
        _ = (1 + x) ^ (α - 1) * (1 + x) ^ (1 : ℝ) := Real.rpow_add hpos _ _
        _ = (1 + x) ^ (α - 1) * (1 + x) := by rw [Real.rpow_one]
    dsimp [g']
    rw [hpow_split]
    ring
  show StrictAntiOn g (Ioi 0)
  refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Ioi 0) (f' := g')
    (fun x hx => (hg_deriv x hx).continuousAt.continuousWithinAt) ?_ ?_
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hg_deriv x hx).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx_pos : 0 < x := hx
    have h1x : 0 < 1 + x := by linarith
    have hpow_pos : 0 < (1 + x) ^ (α - 1) := Real.rpow_pos_of_pos h1x _
    have hmul : (1 + x) ^ (α - 1) * (1 + x) ^ (1 - α) = 1 := by
      rw [← Real.rpow_add h1x, show (α - 1) + (1 - α) = 0 by ring, Real.rpow_zero]
    have hlt1 : 1 < (1 + x) ^ (α - 1) * (1 + (1 - α) * x) := by
      calc 1 = (1 + x) ^ (α - 1) * (1 + x) ^ (1 - α) := hmul.symm
        _ < (1 + x) ^ (α - 1) * (1 + (1 - α) * x) :=
            mul_lt_mul_of_pos_left (hbern x hx_pos) hpow_pos
    exact div_neg_of_neg_of_pos (sub_neg.mpr hlt1) (sq_pos_of_pos hx_pos)

/-- Prop. 1 (`prop:alpha`, Sec. 3.1): for `0 < W, 0 < N, α ∈ (0, 1)`, a positive rate
`r_marg < α * (W / N)` strictly lowers `Z_α` over short blocks (`ΔN → 0⁺`). -/
theorem prop_alpha_discrete_short_block_lt {W N α r_marg : ℝ}
    (hW : 0 < W) (hN : 0 < N) (hα0 : 0 < α) (hα1 : α < 1) (hr : r_marg < α * (W / N)) :
    ∀ᶠ ΔN in 𝓝[>] 0, Z_alpha (W + r_marg * ΔN) (N + ΔN) α < Z_alpha W N α := by
  have _ := hα0
  have _ := hα1
  have hr_bar : 0 < W / N := div_pos hW hN
  have hdiv_tend : Tendsto (fun ΔN : ℝ => ΔN / N) (𝓝[>] 0) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun ΔN : ℝ => ΔN / N) 0 := continuousAt_id.div_const N
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun ΔN (hΔN : 0 < ΔN) => (div_pos hΔN hN).ne'
  have hthresh_tend :
      Tendsto (fun ΔN : ℝ => (((1 + ΔN / N) ^ α - 1) / (ΔN / N)) * (W / N))
        (𝓝[>] 0) (𝓝 (α * (W / N))) :=
    ((prop_alpha_discrete_threshold_tendsto_continuous α).comp hdiv_tend).mul_const (W / N)
  have hev_thresh :
      ∀ᶠ ΔN in 𝓝[>] 0, r_marg < (((1 + ΔN / N) ^ α - 1) / (ΔN / N)) * (W / N) :=
    hthresh_tend.eventually (Ioi_mem_nhds hr)
  filter_upwards [hev_thresh, self_mem_nhdsWithin] with ΔN hlt (hΔN : 0 < ΔN)
  have hrate : (r_marg * ΔN) / ΔN = r_marg := mul_div_cancel_right₀ r_marg hΔN.ne'
  exact (prop_alpha_discrete_lt_iff hN hΔN).mpr (by rw [hrate]; exact hlt)

/-- Prop. 1 (`prop:alpha`, Sec. 3.1): for `0 < W, 0 < N, α ∈ (0, 1)`, and `0 < r_marg < α * (W / N)`,
there is a unique crossover block size `ΔN_* > 0` below which `Z_α` drops, at which it ties,
and above which it rises. -/
theorem prop_alpha_discrete_crossover_unique {W N α r_marg : ℝ}
    (hW : 0 < W) (hN : 0 < N) (hα0 : 0 < α) (hα1 : α < 1)
    (hr_pos : 0 < r_marg) (hr_lt : r_marg < α * (W / N)) :
    ∃! ΔN_star : ℝ, 0 < ΔN_star ∧
      (∀ ΔN, 0 < ΔN → ΔN < ΔN_star → Z_alpha (W + r_marg * ΔN) (N + ΔN) α < Z_alpha W N α) ∧
      Z_alpha (W + r_marg * ΔN_star) (N + ΔN_star) α = Z_alpha W N α ∧
      (∀ ΔN, ΔN_star < ΔN → Z_alpha W N α < Z_alpha (W + r_marg * ΔN) (N + ΔN) α) := by
  let g : ℝ → ℝ := fun x => ((1 + x) ^ α - 1) / x
  have hr_bar : 0 < W / N := div_pos hW hN
  let q : ℝ := r_marg / (W / N)
  have hq_pos : 0 < q := div_pos hr_pos hr_bar
  have hq_lt : q < α := (div_lt_iff₀ hr_bar).mpr hr_lt
  have h_small : ∃ a > 0, q < g a := by
    have hev : ∀ᶠ x in 𝓝[>] 0, q < g x :=
      ((prop_alpha_discrete_threshold_tendsto_continuous α).mono_left
        (nhdsWithin_mono 0 fun _ hx => (lt_of_lt_of_le hx le_rfl).ne')).eventually
          (Ioi_mem_nhds hq_lt)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδ, hmem⟩ := hev
    refine ⟨δ / 2, half_pos hδ, hmem ?_ (half_pos hδ)⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
    linarith
  obtain ⟨a, ha_pos, ha_gt⟩ := h_small
  have h_large : ∃ b > a, g b < q := by
    have htend : Tendsto g atTop (𝓝 0) := by
      have h1 := prop_alpha_discrete_threshold_tendsto_zero zero_lt_one hα0 hα1
      simpa [g, div_one] using h1
    have hev : ∀ᶠ b in atTop, g b < q := htend.eventually (Iio_mem_nhds hq_pos)
    rw [eventually_atTop] at hev
    obtain ⟨B, hB⟩ := hev
    refine ⟨max (a + 1) B, by linarith [le_max_left (a + 1) B], hB _ (le_max_right (a + 1) B)⟩
  obtain ⟨b, hab, hb_lt⟩ := h_large
  have hg_cont : ContinuousOn g (Icc a b) := by
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hx.1
    have h1x : 0 < 1 + x := by linarith
    exact (((continuousAt_const.add continuousAt_id).rpow_const (Or.inl h1x.ne')).sub
      continuousAt_const |>.div continuousAt_id hx_pos.ne').continuousWithinAt
  have hmem_Icc : q ∈ Icc (g b) (g a) := ⟨hb_lt.le, ha_gt.le⟩
  obtain ⟨x_star, hx_mem, hx_eq⟩ := intermediate_value_Icc' hab.le hg_cont hmem_Icc
  have hx_pos : 0 < x_star := lt_of_lt_of_le ha_pos hx_mem.1
  have hg_anti := prop_alpha_discrete_threshold_strictAnti hα0 hα1
  refine ⟨N * x_star, ⟨mul_pos hN hx_pos, ?_, ?_, ?_⟩, ?_⟩
  · intro ΔN hΔN_pos hΔN_lt
    have hx_lt : ΔN / N < x_star := (div_lt_iff₀ hN).mpr (by linarith)
    have hgt : q < g (ΔN / N) := by
      rw [← hx_eq]
      exact hg_anti (div_pos hΔN_pos hN) hx_pos hx_lt
    have hrate : (r_marg * ΔN) / ΔN = r_marg := mul_div_cancel_right₀ r_marg hΔN_pos.ne'
    have hthresh : r_marg < g (ΔN / N) * (W / N) := (div_lt_iff₀ hr_bar).mp hgt
    exact (prop_alpha_discrete_lt_iff hN hΔN_pos).mpr (by rw [hrate]; exact hthresh)
  · have hΔN_pos : 0 < N * x_star := mul_pos hN hx_pos
    have hrate : (r_marg * (N * x_star)) / (N * x_star) = r_marg :=
      mul_div_cancel_right₀ r_marg hΔN_pos.ne'
    have hdiv : (N * x_star) / N = x_star := mul_div_cancel_left₀ x_star hN.ne'
    have hthresh : r_marg = g ((N * x_star) / N) * (W / N) := by
      rw [hdiv, hx_eq]
      dsimp [q]
      field_simp [hr_bar.ne']
    exact (prop_alpha_discrete_eq_iff hN hΔN_pos).mpr (by rw [hrate]; exact hthresh)
  · intro ΔN hΔN_gt
    have hΔN_pos : 0 < ΔN := lt_trans (mul_pos hN hx_pos) hΔN_gt
    have hx_gt : x_star < ΔN / N := (lt_div_iff₀ hN).mpr (by linarith)
    have hlt : g (ΔN / N) < q := by
      rw [← hx_eq]
      exact hg_anti hx_pos (div_pos hΔN_pos hN) hx_gt
    have hrate : (r_marg * ΔN) / ΔN = r_marg := mul_div_cancel_right₀ r_marg hΔN_pos.ne'
    have hthresh : g (ΔN / N) * (W / N) < r_marg := (lt_div_iff₀ hr_bar).mp hlt
    exact (prop_alpha_discrete_iff hN hΔN_pos).mpr (by rw [hrate]; exact hthresh)
  · intro ΔN' ⟨hΔN'_pos, _, heq', _⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hx_lt : ΔN' / N < x_star := (div_lt_iff₀ hN).mpr (by linarith)
      have hgt' : q < g (ΔN' / N) := by rw [← hx_eq]; exact hg_anti (div_pos hΔN'_pos hN) hx_pos hx_lt
      have hrate : (r_marg * ΔN') / ΔN' = r_marg := mul_div_cancel_right₀ r_marg hΔN'_pos.ne'
      have hthresh : r_marg < g (ΔN' / N) * (W / N) := (div_lt_iff₀ hr_bar).mp hgt'
      have hlt_z : Z_alpha (W + r_marg * ΔN') (N + ΔN') α < Z_alpha W N α :=
        (prop_alpha_discrete_lt_iff hN hΔN'_pos).mpr (by rw [hrate]; exact hthresh)
      exact absurd heq' hlt_z.ne
    · have hx_gt : x_star < ΔN' / N := (lt_div_iff₀ hN).mpr (by linarith)
      have hlt' : g (ΔN' / N) < q := by rw [← hx_eq]; exact hg_anti hx_pos (div_pos hΔN'_pos hN) hx_gt
      have hrate : (r_marg * ΔN') / ΔN' = r_marg := mul_div_cancel_right₀ r_marg hΔN'_pos.ne'
      have hthresh : g (ΔN' / N) * (W / N) < r_marg := (lt_div_iff₀ hr_bar).mp hlt'
      have hgt_z : Z_alpha W N α < Z_alpha (W + r_marg * ΔN') (N + ΔN') α :=
        (prop_alpha_discrete_iff hN hΔN'_pos).mpr (by rw [hrate]; exact hthresh)
      exact absurd heq' hgt_z.ne'

section TargetConcordance

/-- Sec. 3.2 (`sec:target`): conditional-independence log expectation directly in terms of
`Z_alpha W N (1 - β / κ)` and order equivalence for `0 < κ`. -/
theorem prop_target_forecast_indep_z_alpha {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (r_f N_f : Ω → ℝ) {W N c₁ c₂ κ β : ℝ}
    (hW : 0 < W) (hN : 0 < N) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hκ : κ ≠ 0)
    (hindep : IndepFun r_f N_f μ)
    (hr_meas : AEStronglyMeasurable r_f μ) (hN_meas : AEStronglyMeasurable N_f μ)
    (hr_mean : ∫ ω, r_f ω ∂μ = c₁ * (W / N) ^ κ)
    (hN_mean : ∫ ω, N_f ω ∂μ = c₂ * N ^ β) :
    Real.log (∫ ω, r_f ω * N_f ω ∂μ) =
      κ * Real.log (Z_alpha W N (1 - β / κ)) + Real.log (c₁ * c₂) := by
  have hlog := (prop_target_forecast_indep_expectation r_f N_f hW hN hc₁ hc₂
    hindep hr_meas hN_meas hr_mean hN_mean).2
  have hZ : Real.log (Z_alpha W N (1 - β / κ)) = Real.log W - (1 - β / κ) * Real.log N := by
    unfold Z_alpha
    rw [Real.log_div hW.ne' (Real.rpow_pos_of_pos hN _).ne', Real.log_rpow hN]
  rw [hlog, hZ]
  field_simp [hκ]
  ring

private noncomputable def pairConc (W₁ N₁ W₂ N₂ α : ℝ) : ℝ :=
  if Z_alpha W₁ N₁ α > Z_alpha W₂ N₂ α then 1
  else if Z_alpha W₁ N₁ α = Z_alpha W₂ N₂ α then (1 / 2 : ℝ)
  else 0

private lemma pairConc_unimodal_of_star {W₁ N₁ W₂ N₂ α_star : ℝ}
    (hW₁ : 0 < W₁) (hN₁ : 0 < N₁) (hW₂ : 0 < W₂) (hN₂ : 0 < N₂)
    (hstar : Z_alpha W₁ N₁ α_star > Z_alpha W₂ N₂ α_star) :
    MonotoneOn (pairConc W₁ N₁ W₂ N₂) (Iic α_star) ∧
      AntitoneOn (pairConc W₁ N₁ W₂ N₂) (Ici α_star) ∧
      pairConc W₁ N₁ W₂ N₂ α_star = 1 := by
  have h_gt_iff : ∀ α, Z_alpha W₁ N₁ α > Z_alpha W₂ N₂ α ↔
      Real.log W₁ - Real.log W₂ > α * (Real.log N₁ - Real.log N₂) := by
    intro α
    have hZ1 : 0 < Z_alpha W₁ N₁ α := by unfold Z_alpha; positivity
    have hZ2 : 0 < Z_alpha W₂ N₂ α := by unfold Z_alpha; positivity
    rw [gt_iff_lt, ← Real.log_lt_log_iff hZ2 hZ1]
    unfold Z_alpha
    rw [Real.log_div hW₁.ne' (Real.rpow_pos_of_pos hN₁ _).ne', Real.log_rpow hN₁,
        Real.log_div hW₂.ne' (Real.rpow_pos_of_pos hN₂ _).ne', Real.log_rpow hN₂]
    constructor <;> intro h <;> linarith
  have h_eq_iff : ∀ α, Z_alpha W₁ N₁ α = Z_alpha W₂ N₂ α ↔
      Real.log W₁ - Real.log W₂ = α * (Real.log N₁ - Real.log N₂) := by
    intro α
    have hZ1 : 0 < Z_alpha W₁ N₁ α := by unfold Z_alpha; positivity
    have hZ2 : 0 < Z_alpha W₂ N₂ α := by unfold Z_alpha; positivity
    rw [← Real.log_injOn_pos.eq_iff hZ1 hZ2]
    unfold Z_alpha
    rw [Real.log_div hW₁.ne' (Real.rpow_pos_of_pos hN₁ _).ne', Real.log_rpow hN₁,
        Real.log_div hW₂.ne' (Real.rpow_pos_of_pos hN₂ _).ne', Real.log_rpow hN₂]
    constructor <;> intro h <;> linarith
  have hpc_star : pairConc W₁ N₁ W₂ N₂ α_star = 1 := by
    unfold pairConc; rw [if_pos hstar]
  have hstar_lin : α_star * (Real.log N₁ - Real.log N₂) < Real.log W₁ - Real.log W₂ :=
    (h_gt_iff α_star).mp hstar
  have hpair_le : ∀ {a b : ℝ},
      (Z_alpha W₁ N₁ b > Z_alpha W₂ N₂ b → Z_alpha W₁ N₁ a > Z_alpha W₂ N₂ a) →
      (Z_alpha W₁ N₁ b ≥ Z_alpha W₂ N₂ b → Z_alpha W₁ N₁ a ≥ Z_alpha W₂ N₂ a) →
      pairConc W₁ N₁ W₂ N₂ b ≤ pairConc W₁ N₁ W₂ N₂ a := by
    intro a b hgt hge
    unfold pairConc
    rcases lt_trichotomy (Z_alpha W₁ N₁ a) (Z_alpha W₂ N₂ a) with ha_lt | ha_eq | ha_gt <;>
      rcases lt_trichotomy (Z_alpha W₁ N₁ b) (Z_alpha W₂ N₂ b) with hb_lt | hb_eq | hb_gt
    · simp [not_lt.mpr ha_lt.le, ha_lt.ne, not_lt.mpr hb_lt.le, hb_lt.ne]
    · simp [not_lt.mpr ha_lt.le, ha_lt.ne, hb_eq]
      exact absurd (hge hb_eq.ge) (not_le.mpr ha_lt)
    · simp [not_lt.mpr ha_lt.le, ha_lt.ne, hb_gt]
      exact absurd (hgt hb_gt) (not_lt.mpr ha_lt.le)
    · simp [ha_eq, not_lt.mpr hb_lt.le, hb_lt.ne]
    · simp [ha_eq, hb_eq]
    · simp [ha_eq, hb_gt]
      exact absurd (hgt hb_gt) (not_lt.mpr ha_eq.le)
    · simp [ha_gt, not_lt.mpr hb_lt.le, hb_lt.ne]
    · simp [ha_gt, hb_eq]; norm_num
    · simp [ha_gt, hb_gt]
  refine ⟨fun a ha b hb hab => ?_, fun a ha b hb hab => ?_, hpc_star⟩
  · rcases lt_trichotomy (Real.log N₁ - Real.log N₂) 0 with hdz | hdz | hdz
    · refine hpair_le ?_ ?_
      · intro ha_gt
        have ha_lin := (h_gt_iff a).mp ha_gt
        have hmul : b * (Real.log N₁ - Real.log N₂) ≤ a * (Real.log N₁ - Real.log N₂) :=
          mul_le_mul_of_nonpos_right hab hdz.le
        exact (h_gt_iff b).mpr (by linarith)
      · intro ha_ge
        rcases eq_or_lt_of_le ha_ge with ha_eq | ha_gt
        · have ha_lin := (h_eq_iff a).mp ha_eq.symm
          have hba : b * (Real.log N₁ - Real.log N₂) ≤ a * (Real.log N₁ - Real.log N₂) :=
            mul_le_mul_of_nonpos_right hab hdz.le
          rcases eq_or_lt_of_le hba with heq | hlt
          · exact ((h_eq_iff b).mpr (by linarith)).symm.le
          · exact ((h_gt_iff b).mpr (by linarith)).le
        · have ha_lin := (h_gt_iff a).mp ha_gt
          have hmul : b * (Real.log N₁ - Real.log N₂) ≤ a * (Real.log N₁ - Real.log N₂) :=
            mul_le_mul_of_nonpos_right hab hdz.le
          exact ((h_gt_iff b).mpr (by linarith)).le
    · have hlog_pos : 0 < Real.log W₁ - Real.log W₂ := by
        rw [hdz, mul_zero] at hstar_lin; exact hstar_lin
      have ha_gt : Z_alpha W₁ N₁ a > Z_alpha W₂ N₂ a := (h_gt_iff a).mpr (by rw [hdz, mul_zero]; exact hlog_pos)
      have hb_gt : Z_alpha W₁ N₁ b > Z_alpha W₂ N₂ b := (h_gt_iff b).mpr (by rw [hdz, mul_zero]; exact hlog_pos)
      unfold pairConc; rw [if_pos ha_gt, if_pos hb_gt]
    · have hma : a * (Real.log N₁ - Real.log N₂) ≤ α_star * (Real.log N₁ - Real.log N₂) :=
        mul_le_mul_of_nonneg_right ha hdz.le
      have hmb : b * (Real.log N₁ - Real.log N₂) ≤ α_star * (Real.log N₁ - Real.log N₂) :=
        mul_le_mul_of_nonneg_right hb hdz.le
      have ha_gt : Z_alpha W₁ N₁ a > Z_alpha W₂ N₂ a := (h_gt_iff a).mpr (by linarith)
      have hb_gt : Z_alpha W₁ N₁ b > Z_alpha W₂ N₂ b := (h_gt_iff b).mpr (by linarith)
      unfold pairConc; rw [if_pos ha_gt, if_pos hb_gt]
  · rcases lt_trichotomy (Real.log N₁ - Real.log N₂) 0 with hdz | hdz | hdz
    · have hma : a * (Real.log N₁ - Real.log N₂) ≤ α_star * (Real.log N₁ - Real.log N₂) :=
        mul_le_mul_of_nonpos_right ha hdz.le
      have hmb : b * (Real.log N₁ - Real.log N₂) ≤ α_star * (Real.log N₁ - Real.log N₂) :=
        mul_le_mul_of_nonpos_right hb hdz.le
      have ha_gt : Z_alpha W₁ N₁ a > Z_alpha W₂ N₂ a := (h_gt_iff a).mpr (by linarith)
      have hb_gt : Z_alpha W₁ N₁ b > Z_alpha W₂ N₂ b := (h_gt_iff b).mpr (by linarith)
      unfold pairConc; rw [if_pos ha_gt, if_pos hb_gt]
    · have hlog_pos : 0 < Real.log W₁ - Real.log W₂ := by
        rw [hdz, mul_zero] at hstar_lin; exact hstar_lin
      have ha_gt : Z_alpha W₁ N₁ a > Z_alpha W₂ N₂ a := (h_gt_iff a).mpr (by rw [hdz, mul_zero]; exact hlog_pos)
      have hb_gt : Z_alpha W₁ N₁ b > Z_alpha W₂ N₂ b := (h_gt_iff b).mpr (by rw [hdz, mul_zero]; exact hlog_pos)
      unfold pairConc; rw [if_pos ha_gt, if_pos hb_gt]
    · refine hpair_le ?_ ?_
      · intro hb_gt
        have hb_lin := (h_gt_iff b).mp hb_gt
        have hmul : a * (Real.log N₁ - Real.log N₂) ≤ b * (Real.log N₁ - Real.log N₂) :=
          mul_le_mul_of_nonneg_right hab hdz.le
        exact (h_gt_iff a).mpr (by linarith)
      · intro hb_ge
        rcases eq_or_lt_of_le hb_ge with hb_eq | hb_gt
        · have hb_lin := (h_eq_iff b).mp hb_eq.symm
          have hab_mul : a * (Real.log N₁ - Real.log N₂) ≤ b * (Real.log N₁ - Real.log N₂) :=
            mul_le_mul_of_nonneg_right hab hdz.le
          rcases eq_or_lt_of_le hab_mul with heq | hlt
          · exact ((h_eq_iff a).mpr (by linarith)).symm.le
          · exact ((h_gt_iff a).mpr (by linarith)).le
        · have hb_lin := (h_gt_iff b).mp hb_gt
          have hmul : a * (Real.log N₁ - Real.log N₂) ≤ b * (Real.log N₁ - Real.log N₂) :=
            mul_le_mul_of_nonneg_right hab hdz.le
          exact ((h_gt_iff a).mpr (by linarith)).le

/-- Sec. 3.2 (`sec:target`): for any binary target `y` separated by `Z_{α*}` on positive
careers `(W_i, N_i)`, the Mann-Whitney AUC / concordance score is unimodal around `α*`
(monotonically non-decreasing on `(-∞, α*]` and non-increasing on `[α*, ∞)`), and is
maximized on `[0, 1]` at the clipped exponent `max 0 (min 1 α*)`. -/
theorem prop_target_concordance_unimodal_clipped_max {ι : Type*} (s : Finset ι)
    (W N : ι → ℝ) (y : ι → Bool) (α_star : ℝ)
    (hW : ∀ i ∈ s, 0 < W i) (hN : ∀ i ∈ s, 0 < N i)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, y i = true → y j = false →
      Z_alpha (W i) (N i) α_star > Z_alpha (W j) (N j) α_star) :
    let conc : ℝ → ℝ := fun α =>
      ∑ i ∈ s with y i = true, ∑ j ∈ s with y j = false, pairConc (W i) (N i) (W j) (N j) α
    MonotoneOn conc (Iic α_star) ∧
    AntitoneOn conc (Ici α_star) ∧
    (∀ α : ℝ, conc α ≤ conc α_star) ∧
    (let α_clip := max (0 : ℝ) (min (1 : ℝ) α_star)
     α_clip ∈ Icc (0 : ℝ) 1 ∧ ∀ α ∈ Icc (0 : ℝ) 1, conc α ≤ conc α_clip) := by
  intro conc
  have hmono : MonotoneOn conc (Iic α_star) := by
    intro a ha b hb hab
    dsimp [conc]
    refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
    rw [Finset.mem_filter] at hi hj
    exact (pairConc_unimodal_of_star (hW i hi.1) (hN i hi.1) (hW j hj.1) (hN j hj.1)
      (hsep i hi.1 j hj.1 hi.2 hj.2)).1 ha hb hab
  have hanti : AntitoneOn conc (Ici α_star) := by
    intro a ha b hb hab
    dsimp [conc]
    refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
    rw [Finset.mem_filter] at hi hj
    exact (pairConc_unimodal_of_star (hW i hi.1) (hN i hi.1) (hW j hj.1) (hN j hj.1)
      (hsep i hi.1 j hj.1 hi.2 hj.2)).2.1 ha hb hab
  have hmax : ∀ α : ℝ, conc α ≤ conc α_star := by
    intro α
    rcases le_total α α_star with hle | hge
    · exact hmono hle Set.right_mem_Iic hle
    · exact hanti Set.left_mem_Ici hge hge
  refine ⟨hmono, hanti, hmax, ?_⟩
  intro α_clip
  have hclip_mem : α_clip ∈ Icc (0 : ℝ) 1 := ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  refine ⟨hclip_mem, fun α hα => ?_⟩
  rcases le_total α_star 0 with hle0 | hge0
  · have hclip0 : α_clip = 0 := by
      dsimp [α_clip]
      rw [min_eq_right (by linarith), max_eq_left hle0]
    rw [hclip0]
    exact hanti hle0 (hle0.trans hα.1) hα.1
  · rcases le_total α_star 1 with hle1 | hge1
    · have hclip_star : α_clip = α_star := by
        dsimp [α_clip]
        rw [min_eq_right hle1, max_eq_right hge0]
      rw [hclip_star]
      exact hmax α
    · have hclip1 : α_clip = 1 := by
        dsimp [α_clip]
        rw [min_eq_left hge1]
        norm_num
      rw [hclip1]
      exact hmono (hα.2.trans hge1) hge1 hα.2

end TargetConcordance

section NoiseAndOLSAdditions

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Sec. 3.3 (`sec:zstat`): persistent positive covariance (`Cov ≥ c₀ > 0` for `i ≠ j`) with
`SD(W) = c n^α` for any proportionality constant `c > 0` forces `α > 1/2` once
`1 + (c² - σ²)/c₀ < n`. -/
theorem prop_frequentist_pos_cov_sd_general_const {n : ℕ} (hn : 2 ≤ n) (w : Fin n → Ω → ℝ)
    {c c₀ σ α : ℝ} (hc : 0 < c) (hc₀ : 0 < c₀)
    (hlarge : 1 + (c ^ 2 - σ ^ 2) / c₀ < (n : ℝ))
    (hL2 : ∀ i, MemLp (w i) 2 μ)
    (hvar : ∀ i, variance (w i) μ = σ ^ 2)
    (hcov : ∀ i j, i ≠ j → c₀ ≤ cov[w i, w j; μ])
    (hsd : Real.sqrt (variance (fun ω => ∑ i, w i ω) μ) = c * (n : ℝ) ^ α) :
    1 / 2 < α := by
  have hn_pos : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hvar_ge := (prop_frequentist_pos_cov_var_gt hn w hc₀ hL2 hvar hcov).1
  have hvar_eq : variance (fun ω => ∑ i, w i ω) μ = c ^ 2 * (n : ℝ) ^ (2 * α) := by
    have hsq := congrArg (· ^ 2) hsd
    dsimp only at hsq
    rw [Real.sq_sqrt (variance_nonneg _ _), mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ α) 2,
        ← Real.rpow_mul hn_pos.le] at hsq
    rw [show α * ((2 : ℕ) : ℝ) = 2 * α by ring] at hsq
    exact hsq
  have hgt_c : c ^ 2 * (n : ℝ) < (n : ℝ) * σ ^ 2 + (n : ℝ) * ((n : ℝ) - 1) * c₀ := by
    have h1 : (c ^ 2 - σ ^ 2) < ((n : ℝ) - 1) * c₀ := by
      have : (c ^ 2 - σ ^ 2) / c₀ < (n : ℝ) - 1 := by linarith
      exact (div_lt_iff₀ hc₀).mp this
    nlinarith [hn_pos]
  have hgt : c ^ 2 * (n : ℝ) < c ^ 2 * (n : ℝ) ^ (2 * α) := by
    linarith [hvar_ge, hvar_eq]
  rw [mul_lt_mul_iff_right₀ (sq_pos_of_pos hc)] at hgt
  conv_lhs at hgt => rw [← Real.rpow_one (n : ℝ)]
  have hexp := (Real.rpow_lt_rpow_left_iff hn1).mp hgt
  linarith

/-- Sec. 7 & App. H (`app:uncert`): absolute sampling standard deviation `σ N^(1/2 - α)` strictly
increases with exposure `N > 0` for `α < 1/2` (such as `α = 1/5`), whereas relative noise
`σ / (r √N)` strictly decreases with `N > 0` for `r > 0`. -/
theorem prop_frequentist_sd_strictMono_N {σ α : ℝ} (hσ : 0 < σ) (hα : α < 1 / 2) :
    StrictMonoOn (fun N : ℝ => σ * N ^ ((1 / 2 : ℝ) - α)) (Ioi 0) := by
  intro a ha b hb hab
  have hexp : 0 < (1 / 2 : ℝ) - α := sub_pos.mpr hα
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow (le_of_lt ha) hab hexp) hσ

theorem prop_frequentist_rel_sd_strictAnti_N {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    StrictAntiOn (fun N : ℝ => σ / (r * Real.sqrt N)) (Ioi 0) := by
  intro a ha b hb hab
  have hs_lt : Real.sqrt a < Real.sqrt b := Real.sqrt_lt_sqrt (le_of_lt ha) hab
  exact div_lt_div_of_pos_left hσ (mul_pos hr (Real.sqrt_pos.mpr ha))
    (mul_lt_mul_of_pos_left hs_lt hr)

/-- Sec. 3.3 (`sec:zstat`): exact variance of the individual OLS residual
`e_j = W_j / √N_j - r̂ √N_j` in the no-intercept regression of `W_s/√N_s` on `√N_s`
equals `(1 - N_j / N_tot) σ²` (so individual OLS residuals depend on `N_j / N_tot`
even though the errors `W_j/√N_j - r √N_j` are homoscedastic and `E[RSS] = (m-1)σ²`). -/
theorem ols_residual_var {m : ℕ} (W : Fin m → Ω → ℝ) (N : Fin m → ℝ) {σ : ℝ}
    (hN : ∀ j, 0 < N j)
    (hL2 : ∀ j, MemLp (W j) 2 μ)
    (hvar : ∀ j, variance (W j) μ = N j * σ ^ 2)
    (huncorr : ∀ j k, j ≠ k → cov[W j, W k; μ] = 0) (j : Fin m) :
    let N_tot : ℝ := ∑ i : Fin m, N i
    variance (fun ω => W j ω / Real.sqrt (N j) -
      ((∑ i : Fin m, W i ω) / N_tot) * Real.sqrt (N j)) μ =
      (1 - N j / N_tot) * σ ^ 2 := by
  intro N_tot
  have hN_tot_pos : 0 < N_tot :=
    Finset.sum_pos (fun i _ => hN i) ⟨j, Finset.mem_univ j⟩
  have hsNj : 0 < Real.sqrt (N j) := Real.sqrt_pos.mpr (hN j)
  have hsqNj : Real.sqrt (N j) ^ 2 = N j := Real.sq_sqrt (hN j).le
  let a : Fin m → ℝ := fun i =>
    if i = j then (1 : ℝ) / Real.sqrt (N j) - Real.sqrt (N j) / N_tot
    else -(Real.sqrt (N j) / N_tot)
  have heq : (fun ω => W j ω / Real.sqrt (N j) -
      ((∑ i : Fin m, W i ω) / N_tot) * Real.sqrt (N j)) =
      fun ω => ∑ i : Fin m, a i * W i ω := by
    ext ω
    have hsplit : ∑ i : Fin m, a i * W i ω =
        (W j ω / Real.sqrt (N j)) + ∑ i : Fin m, -(Real.sqrt (N j) / N_tot) * W i ω := by
      have hterm : ∀ i : Fin m,
          a i * W i ω = (if i = j then W j ω / Real.sqrt (N j) else 0) +
            (-(Real.sqrt (N j) / N_tot) * W i ω) := by
        intro i
        dsimp [a]
        split_ifs with hij
        · subst hij; ring
        · ring
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib]
      simp [Finset.sum_ite_eq']
    rw [hsplit, ← Finset.mul_sum]
    ring
  rw [heq, variance_fun_sum (fun i => (hL2 i).const_mul (a i))]
  have hcov_term : ∀ i : Fin m,
      ∑ k : Fin m, cov[fun ω => a i * W i ω, fun ω => a k * W k ω; μ] =
        (a i) ^ 2 * N i * σ ^ 2 := by
    intro i
    rw [Finset.sum_eq_single i]
    · rw [covariance_self ((hL2 i).const_mul (a i)).aemeasurable, variance_const_mul, hvar i]
      ring
    · intro k _ hki
      rw [covariance_const_mul_left, covariance_const_mul_right, huncorr i k hki.symm,
          mul_zero, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  simp_rw [hcov_term]
  have hsum_coeff : ∑ i : Fin m, (a i) ^ 2 * N i = 1 - N j / N_tot := by
    rw [← Finset.add_sum_erase Finset.univ (fun i => (a i) ^ 2 * N i) (Finset.mem_univ j)]
    have haj : (a j) ^ 2 * N j = (1 - N j / N_tot) ^ 2 := by
      dsimp [a]
      rw [if_pos rfl]
      calc ((1 : ℝ) / Real.sqrt (N j) - Real.sqrt (N j) / N_tot) ^ 2 * N j
          = ((1 / Real.sqrt (N j) ^ 2 - 2 / N_tot + Real.sqrt (N j) ^ 2 / N_tot ^ 2) * N j) := by
              field_simp [hsNj.ne', hN_tot_pos.ne']
              ring
        _ = (1 / N j - 2 / N_tot + N j / N_tot ^ 2) * N j := by rw [hsqNj]
        _ = (1 - N j / N_tot) ^ 2 := by field_simp [(hN j).ne', hN_tot_pos.ne']; ring
    have ha_other : ∑ i ∈ Finset.univ.erase j, (a i) ^ 2 * N i =
        (N j / N_tot ^ 2) * (N_tot - N j) := by
      have hterm : ∀ i ∈ Finset.univ.erase j, (a i) ^ 2 * N i = (N j / N_tot ^ 2) * N i := by
        intro i hi
        have hne : i ≠ j := (Finset.mem_erase.mp hi).1
        dsimp [a]
        rw [if_neg hne, neg_sq, div_pow, hsqNj]
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      have hsum_erase : ∑ i ∈ Finset.univ.erase j, N i = N_tot - N j := by
        have := Finset.add_sum_erase Finset.univ N (Finset.mem_univ j)
        dsimp only [N_tot]
        linarith
      rw [hsum_erase]
    rw [haj, ha_other]
    field_simp [hN_tot_pos.ne']
    ring
  rw [← Finset.sum_mul, hsum_coeff]

end NoiseAndOLSAdditions

/-- Sec. 3.5 (`sec:twoway_theory`): for non-negative coordinates and `α ∈ [0, 1)`, `Z_{α,2D}`
is the `ℓ_γ` norm `((Z₁)^γ + (Z₂)^γ)^(1/γ)` (in particular `ℓ_{5/4}` at `α = 1/5`). -/
theorem Z_twoway_both_nonneg {W₁ N₁ W₂ N₂ α : ℝ}
    (h1 : 0 ≤ W₁) (h2 : 0 ≤ W₂) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hα : α < 1) :
    Z_twoway W₁ N₁ W₂ N₂ α =
      (Z_alpha W₁ N₁ α ^ gamma α + Z_alpha W₂ N₂ α ^ gamma α) ^ (1 / gamma α) := by
  simpa [Fin.sum_univ_two] using twoway_nonneg_eq_radon h1 h2 hN₁ hN₂ hα

theorem Z_twoway_fifth_both_nonneg {W₁ N₁ W₂ N₂ : ℝ}
    (h1 : 0 ≤ W₁) (h2 : 0 ≤ W₂) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) :
    Z_twoway W₁ N₁ W₂ N₂ (1 / 5) =
      (Z_alpha W₁ N₁ (1 / 5) ^ ((5 : ℝ) / 4) +
        Z_alpha W₂ N₂ (1 / 5) ^ ((5 : ℝ) / 4)) ^ ((4 : ℝ) / 5) := by
  have hg : gamma (1 / 5 : ℝ) = 5 / 4 := by unfold gamma; norm_num
  have h1g : (1 : ℝ) / gamma (1 / 5 : ℝ) = 4 / 5 := by rw [hg]; norm_num
  rw [Z_twoway_both_nonneg h1 h2 hN₁ hN₂ (by norm_num), hg]
  norm_num

/-- Sec. 6 & App. H (`app:uncert`): on the non-negative orthant (`W₁, W₂ ≥ 0` and
`W₁ + δ₁, W₂ + δ₂ ≥ 0`) with `α ∈ [0, 1)`, `Z_{α,2D}` satisfies the `ℓ_γ` triangle /
Lipschitz rounding bound `|ΔZ_{α,2D}| ≤ (|δ₁/N₁^α|^γ + |δ₂/N₂^α|^γ)^(1/γ) ≤ |δ₁|/N₁^α + |δ₂|/N₂^α`. -/
private lemma minkowski_two_nonneg {a₁ a₂ b₁ b₂ p : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hp : 1 ≤ p) :
    ((a₁ + b₁) ^ p + (a₂ + b₂) ^ p) ^ (1 / p) ≤
      (a₁ ^ p + a₂ ^ p) ^ (1 / p) + (b₁ ^ p + b₂ ^ p) ^ (1 / p) := by
  have hp_pos : 0 < p := by linarith
  set A : ℝ := (a₁ ^ p + a₂ ^ p) ^ (1 / p)
  set B : ℝ := (b₁ ^ p + b₂ ^ p) ^ (1 / p)
  have hA_nn : 0 ≤ A := Real.rpow_nonneg (by positivity) _
  have hB_nn : 0 ≤ B := Real.rpow_nonneg (by positivity) _
  have hAp : A ^ p = a₁ ^ p + a₂ ^ p := by
    dsimp [A]; rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hp_pos.ne', Real.rpow_one]
  have hBp : B ^ p = b₁ ^ p + b₂ ^ p := by
    dsimp [B]; rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hp_pos.ne', Real.rpow_one]
  rcases eq_or_lt_of_le hA_nn with hA0 | hA_pos
  · have hAp0 : a₁ ^ p + a₂ ^ p = 0 := by rw [← hAp, ← hA0, Real.zero_rpow hp_pos.ne']
    have ha1_0 : a₁ ^ p = 0 := by linarith [Real.rpow_nonneg ha₁ p, Real.rpow_nonneg ha₂ p]
    have ha2_0 : a₂ ^ p = 0 := by linarith [Real.rpow_nonneg ha₁ p, Real.rpow_nonneg ha₂ p]
    have ha1z : a₁ = 0 := (Real.rpow_eq_zero_iff_of_nonneg ha₁).mp ha1_0 |>.1
    have ha2z : a₂ = 0 := (Real.rpow_eq_zero_iff_of_nonneg ha₂).mp ha2_0 |>.1
    simp [ha1z, ha2z, ← hA0, B]
  · rcases eq_or_lt_of_le hB_nn with hB0 | hB_pos
    · have hBp0 : b₁ ^ p + b₂ ^ p = 0 := by rw [← hBp, ← hB0, Real.zero_rpow hp_pos.ne']
      have hb1_0 : b₁ ^ p = 0 := by linarith [Real.rpow_nonneg hb₁ p, Real.rpow_nonneg hb₂ p]
      have hb2_0 : b₂ ^ p = 0 := by linarith [Real.rpow_nonneg hb₁ p, Real.rpow_nonneg hb₂ p]
      have hb1z : b₁ = 0 := (Real.rpow_eq_zero_iff_of_nonneg hb₁).mp hb1_0 |>.1
      have hb2z : b₂ = 0 := (Real.rpow_eq_zero_iff_of_nonneg hb₂).mp hb2_0 |>.1
      simp [hb1z, hb2z, ← hB0, A]
    · have hS : 0 < A + B := add_pos hA_pos hB_pos
      have hconv := convexOn_rpow hp
      have hcoord : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v →
          ((u + v) / (A + B)) ^ p ≤ (A / (A + B)) * (u / A) ^ p + (B / (A + B)) * (v / B) ^ p := by
        intro u v hu hv
        have heq : (u + v) / (A + B) = (A / (A + B)) • (u / A) + (B / (A + B)) • (v / B) := by
          rw [smul_eq_mul, smul_eq_mul]
          field_simp [hA_pos.ne', hB_pos.ne', hS.ne']
        rw [heq]
        exact hconv.2 (show u / A ∈ Ici (0 : ℝ) from div_nonneg hu hA_pos.le)
          (show v / B ∈ Ici (0 : ℝ) from div_nonneg hv hB_pos.le)
          (div_nonneg hA_pos.le hS.le) (div_nonneg hB_pos.le hS.le)
          (by field_simp [hS.ne'])
      have hc1 := hcoord a₁ b₁ ha₁ hb₁
      have hc2 := hcoord a₂ b₂ ha₂ hb₂
      have hsum_le : ((a₁ + b₁) / (A + B)) ^ p + ((a₂ + b₂) / (A + B)) ^ p ≤ 1 := by
        calc ((a₁ + b₁) / (A + B)) ^ p + ((a₂ + b₂) / (A + B)) ^ p
            ≤ ((A / (A + B)) * (a₁ / A) ^ p + (B / (A + B)) * (b₁ / B) ^ p) +
              ((A / (A + B)) * (a₂ / A) ^ p + (B / (A + B)) * (b₂ / B) ^ p) := add_le_add hc1 hc2
          _ = (A / (A + B)) * ((a₁ / A) ^ p + (a₂ / A) ^ p) +
              (B / (A + B)) * ((b₁ / B) ^ p + (b₂ / B) ^ p) := by ring
          _ = (A / (A + B)) * ((a₁ ^ p + a₂ ^ p) / A ^ p) +
              (B / (A + B)) * ((b₁ ^ p + b₂ ^ p) / B ^ p) := by
                rw [Real.div_rpow ha₁ hA_pos.le, Real.div_rpow ha₂ hA_pos.le,
                    Real.div_rpow hb₁ hB_pos.le, Real.div_rpow hb₂ hB_pos.le]
                ring
          _ = (A / (A + B)) * 1 + (B / (A + B)) * 1 := by
                rw [← hAp, div_self (Real.rpow_pos_of_pos hA_pos p).ne',
                    ← hBp, div_self (Real.rpow_pos_of_pos hB_pos p).ne']
          _ = 1 := by field_simp [hS.ne']
      rw [Real.div_rpow (add_nonneg ha₁ hb₁) hS.le, Real.div_rpow (add_nonneg ha₂ hb₂) hS.le,
          ← add_div, div_le_one (Real.rpow_pos_of_pos hS p)] at hsum_le
      have hrpow := Real.rpow_le_rpow (by positivity) hsum_le (one_div_pos.mpr hp_pos).le
      rwa [← Real.rpow_mul hS.le, mul_one_div_cancel hp_pos.ne', Real.rpow_one] at hrpow

theorem app_h_twoway_rounding_bound {W₁ δ₁ N₁ W₂ δ₂ N₂ α : ℝ}
    (h0 : 0 ≤ α) (h1 : α < 1) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (hW₁ : 0 ≤ W₁) (hW₂ : 0 ≤ W₂) (hW₁' : 0 ≤ W₁ + δ₁) (hW₂' : 0 ≤ W₂ + δ₂) :
    |Z_twoway (W₁ + δ₁) N₁ (W₂ + δ₂) N₂ α - Z_twoway W₁ N₁ W₂ N₂ α| ≤
      ((|δ₁| / N₁ ^ α) ^ gamma α + (|δ₂| / N₂ ^ α) ^ gamma α) ^ (1 / gamma α) ∧
    ((|δ₁| / N₁ ^ α) ^ gamma α + (|δ₂| / N₂ ^ α) ^ gamma α) ^ (1 / gamma α) ≤
      |δ₁| / N₁ ^ α + |δ₂| / N₂ ^ α := by
  have hg_ge : 1 ≤ gamma α := one_le_gamma h0 h1
  have hg_pos : 0 < gamma α := by linarith
  have hZ1_nn : 0 ≤ Z_alpha W₁ N₁ α := by unfold Z_alpha; positivity
  have hZ2_nn : 0 ≤ Z_alpha W₂ N₂ α := by unfold Z_alpha; positivity
  have hZ1'_nn : 0 ≤ Z_alpha (W₁ + δ₁) N₁ α := by unfold Z_alpha; positivity
  have hZ2'_nn : 0 ≤ Z_alpha (W₂ + δ₂) N₂ α := by unfold Z_alpha; positivity
  set d₁ : ℝ := |δ₁| / N₁ ^ α
  set d₂ : ℝ := |δ₂| / N₂ ^ α
  have hd1_nn : 0 ≤ d₁ := by positivity
  have hd2_nn : 0 ≤ d₂ := by positivity
  have h1_upper : Z_alpha (W₁ + δ₁) N₁ α ≤ Z_alpha W₁ N₁ α + d₁ := by
    unfold Z_alpha; dsimp [d₁]
    rw [add_div, add_le_add_iff_left]
    exact div_le_div_of_nonneg_right (le_abs_self δ₁) (Real.rpow_pos_of_pos hN₁ α).le
  have h2_upper : Z_alpha (W₂ + δ₂) N₂ α ≤ Z_alpha W₂ N₂ α + d₂ := by
    unfold Z_alpha; dsimp [d₂]
    rw [add_div, add_le_add_iff_left]
    exact div_le_div_of_nonneg_right (le_abs_self δ₂) (Real.rpow_pos_of_pos hN₂ α).le
  have h1_lower : Z_alpha W₁ N₁ α ≤ Z_alpha (W₁ + δ₁) N₁ α + d₁ := by
    unfold Z_alpha; dsimp [d₁]
    rw [add_div, add_assoc, le_add_iff_nonneg_right]
    have : 0 ≤ δ₁ / N₁ ^ α + |δ₁| / N₁ ^ α := by
      rw [← add_div]
      exact div_nonneg (by linarith [neg_abs_le δ₁]) (Real.rpow_pos_of_pos hN₁ α).le
    exact this
  have h2_lower : Z_alpha W₂ N₂ α ≤ Z_alpha (W₂ + δ₂) N₂ α + d₂ := by
    unfold Z_alpha; dsimp [d₂]
    rw [add_div, add_assoc, le_add_iff_nonneg_right]
    have : 0 ≤ δ₂ / N₂ ^ α + |δ₂| / N₂ ^ α := by
      rw [← add_div]
      exact div_nonneg (by linarith [neg_abs_le δ₂]) (Real.rpow_pos_of_pos hN₂ α).le
    exact this
  rw [Z_twoway_both_nonneg hW₁' hW₂' hN₁ hN₂ h1, Z_twoway_both_nonneg hW₁ hW₂ hN₁ hN₂ h1]
  have h_up : (Z_alpha (W₁ + δ₁) N₁ α ^ gamma α + Z_alpha (W₂ + δ₂) N₂ α ^ gamma α) ^ (1 / gamma α) -
      (Z_alpha W₁ N₁ α ^ gamma α + Z_alpha W₂ N₂ α ^ gamma α) ^ (1 / gamma α) ≤
      (d₁ ^ gamma α + d₂ ^ gamma α) ^ (1 / gamma α) := by
    have hm1 : (Z_alpha (W₁ + δ₁) N₁ α ^ gamma α + Z_alpha (W₂ + δ₂) N₂ α ^ gamma α) ^ (1 / gamma α) ≤
        ((Z_alpha W₁ N₁ α + d₁) ^ gamma α + (Z_alpha W₂ N₂ α + d₂) ^ gamma α) ^ (1 / gamma α) := by
      refine Real.rpow_le_rpow (by positivity) (add_le_add
        (Real.rpow_le_rpow hZ1'_nn h1_upper hg_pos.le)
        (Real.rpow_le_rpow hZ2'_nn h2_upper hg_pos.le)) (one_div_pos.mpr hg_pos).le
    linarith [minkowski_two_nonneg hZ1_nn hZ2_nn hd1_nn hd2_nn hg_ge]
  have h_dn : (Z_alpha W₁ N₁ α ^ gamma α + Z_alpha W₂ N₂ α ^ gamma α) ^ (1 / gamma α) -
      (Z_alpha (W₁ + δ₁) N₁ α ^ gamma α + Z_alpha (W₂ + δ₂) N₂ α ^ gamma α) ^ (1 / gamma α) ≤
      (d₁ ^ gamma α + d₂ ^ gamma α) ^ (1 / gamma α) := by
    have hm1 : (Z_alpha W₁ N₁ α ^ gamma α + Z_alpha W₂ N₂ α ^ gamma α) ^ (1 / gamma α) ≤
        ((Z_alpha (W₁ + δ₁) N₁ α + d₁) ^ gamma α + (Z_alpha (W₂ + δ₂) N₂ α + d₂) ^ gamma α) ^ (1 / gamma α) := by
      refine Real.rpow_le_rpow (by positivity) (add_le_add
        (Real.rpow_le_rpow hZ1_nn h1_lower hg_pos.le)
        (Real.rpow_le_rpow hZ2_nn h2_lower hg_pos.le)) (one_div_pos.mpr hg_pos).le
    linarith [minkowski_two_nonneg hZ1'_nn hZ2'_nn hd1_nn hd2_nn hg_ge]
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, ?_⟩
  have hsuper : d₁ ^ gamma α + d₂ ^ gamma α ≤ (d₁ + d₂) ^ gamma α :=
    Real.add_rpow_le_rpow_add hd1_nn hd2_nn hg_ge
  have hrpow := Real.rpow_le_rpow (by positivity) hsuper (one_div_pos.mpr hg_pos).le
  rwa [← Real.rpow_mul (add_nonneg hd1_nn hd2_nn), mul_one_div_cancel hg_pos.ne', Real.rpow_one] at hrpow

/-- App. B (`app:twoway`): for `α ∈ (0, 1/2]` and `W_pitch ≠ 0` (and symmetrically `W_pos ≠ 0`),
`Z_{α,2D}` is not twice Fréchet differentiable on `ℝ²` at `W_k = 0`. -/
theorem Z_twoway_not_twice_fderiv_at_W1_zero {PA W_pitch BF α : ℝ}
    (h0 : 0 < α) (hhalf : α ≤ 1 / 2) (hPA : 0 < PA) (hBF : 0 < BF) (hW₂ : W_pitch ≠ 0) :
    ¬ DifferentiableAt ℝ (fderiv ℝ (fun w : ℝ × ℝ => Z_twoway w.1 PA w.2 BF α)) (0, W_pitch) := by
  intro hdiff
  have hnot := (Z_twoway_not_twice_diff_at_W1_zero h0 hhalf hPA hBF hW₂).1
  apply hnot
  have h1 : α < 1 := by linarith
  have hI0 : I_twoway 0 PA W_pitch BF α ≠ 0 := by
    unfold I_twoway signedPow
    rw [Real.sign_zero, zero_mul, zero_div, zero_add]
    have hBFpow : BF ^ (gamma α - 1) ≠ 0 := (Real.rpow_pos_of_pos hBF _).ne'
    have hs : Real.sign W_pitch ≠ 0 := by
      rcases lt_or_gt_of_ne hW₂ with hneg | hpos
      · rw [Real.sign_of_neg hneg]; norm_num
      · rw [Real.sign_of_pos hpos]; norm_num
    exact div_ne_zero (mul_ne_zero hs (Real.rpow_pos_of_pos (abs_pos.mpr hW₂) _).ne') hBFpow
  have hI_cont : Continuous (fun w : ℝ => I_twoway w PA W_pitch BF α) := by
    unfold I_twoway
    exact ((signedPow_continuous (gamma_pos h1)).div_const _).add continuous_const
  have hev_I_ne : ∀ᶠ w in 𝓝 (0 : ℝ), I_twoway w PA W_pitch BF α ≠ 0 :=
    hI_cont.continuousAt.eventually_ne hI0
  have hev_deriv : (deriv (fun w => Z_twoway w PA W_pitch BF α)) =ᶠ[𝓝 (0 : ℝ)]
      fun w => fderiv ℝ (fun p : ℝ × ℝ => Z_twoway p.1 PA p.2 BF α) (w, W_pitch) (1, 0) := by
    filter_upwards [hev_I_ne] with w hw
    have hfd := Z_twoway_hasFDerivAt h0 h1 hPA hBF hw
    have hpd := Z_twoway_hasDerivAt_W1 h0 h1 hPA hw
    rw [hpd.deriv, hfd.fderiv]
    simp
  have hcomp : DifferentiableAt ℝ
      (fun w : ℝ => fderiv ℝ (fun p : ℝ × ℝ => Z_twoway p.1 PA p.2 BF α) (w, W_pitch) (1, 0)) 0 := by
    have hinj : DifferentiableAt ℝ (fun w : ℝ => (w, W_pitch)) 0 :=
      differentiableAt_id.prodMk (differentiableAt_const W_pitch)
    exact (hdiff.comp 0 hinj).clm_apply (differentiableAt_const (1, 0))
  exact hcomp.congr_of_eventuallyEq hev_deriv

theorem Z_twoway_not_twice_fderiv_at_W2_zero {W_pos PA BF α : ℝ}
    (h0 : 0 < α) (hhalf : α ≤ 1 / 2) (hPA : 0 < PA) (hBF : 0 < BF) (hW₁ : W_pos ≠ 0) :
    ¬ DifferentiableAt ℝ (fderiv ℝ (fun w : ℝ × ℝ => Z_twoway w.1 PA w.2 BF α)) (W_pos, 0) := by
  intro hdiff
  have hnot := (Z_twoway_not_twice_diff_at_W2_zero h0 hhalf hPA hBF hW₁).1
  apply hnot
  have h1 : α < 1 := by linarith
  have hI0 : I_twoway W_pos PA 0 BF α ≠ 0 := by
    unfold I_twoway signedPow
    rw [Real.sign_zero, zero_mul, zero_div, add_zero]
    have hPApow : PA ^ (gamma α - 1) ≠ 0 := (Real.rpow_pos_of_pos hPA _).ne'
    have hs : Real.sign W_pos ≠ 0 := by
      rcases lt_or_gt_of_ne hW₁ with hneg | hpos
      · rw [Real.sign_of_neg hneg]; norm_num
      · rw [Real.sign_of_pos hpos]; norm_num
    exact div_ne_zero (mul_ne_zero hs (Real.rpow_pos_of_pos (abs_pos.mpr hW₁) _).ne') hPApow
  have hI_cont : Continuous (fun w : ℝ => I_twoway W_pos PA w BF α) := by
    unfold I_twoway
    exact continuous_const.add ((signedPow_continuous (gamma_pos h1)).div_const _)
  have hev_I_ne : ∀ᶠ w in 𝓝 (0 : ℝ), I_twoway W_pos PA w BF α ≠ 0 :=
    hI_cont.continuousAt.eventually_ne hI0
  have hev_deriv : (deriv (fun w => Z_twoway W_pos PA w BF α)) =ᶠ[𝓝 (0 : ℝ)]
      fun w => fderiv ℝ (fun p : ℝ × ℝ => Z_twoway p.1 PA p.2 BF α) (W_pos, w) (0, 1) := by
    filter_upwards [hev_I_ne] with w hw
    have hfd := Z_twoway_hasFDerivAt h0 h1 hPA hBF hw
    have hpd := Z_twoway_hasDerivAt_W2 h0 h1 hBF hw
    rw [hpd.deriv, hfd.fderiv]
    simp
  have hcomp : DifferentiableAt ℝ
      (fun w : ℝ => fderiv ℝ (fun p : ℝ × ℝ => Z_twoway p.1 PA p.2 BF α) (W_pos, w) (0, 1)) 0 := by
    have hinj : DifferentiableAt ℝ (fun w : ℝ => (W_pos, w)) 0 :=
      (differentiableAt_const W_pos).prodMk differentiableAt_id
    exact (hdiff.comp 0 hinj).clm_apply (differentiableAt_const (0, 1))
  exact hcomp.congr_of_eventuallyEq hev_deriv

/-- App. B (`app:twoway`): strict anti-monotonicity of `Z_{α,2D}` in positive secondary exposure `N₂`. -/
theorem Z_twoway_pos_strictAnti_exposure {W₁ N₁ W₂ N₂ N₂' α : ℝ}
    (h0 : 0 < α) (h1 : α < 1) (hW₂ : 0 < W₂) (hN₂ : 0 < N₂) (hNlt : N₂ < N₂') :
    Z_twoway W₁ N₁ W₂ N₂' α < Z_twoway W₁ N₁ W₂ N₂ α := by
  have hg : 0 < gamma α := gamma_pos h1
  have hg_sub : 0 < gamma α - 1 := by linarith [one_lt_gamma h0 h1]
  have hinv : 0 < 1 / gamma α := one_div_pos.mpr hg
  apply signedPow_strictMono hinv
  unfold I_twoway
  rw [add_lt_add_iff_left, signedPow_nonneg hW₂.le hg]
  have hnum : 0 < W₂ ^ gamma α := Real.rpow_pos_of_pos hW₂ _
  have hden1 : 0 < N₂ ^ (gamma α - 1) := Real.rpow_pos_of_pos hN₂ _
  have hden2 : N₂ ^ (gamma α - 1) < N₂' ^ (gamma α - 1) :=
    Real.rpow_lt_rpow hN₂.le hNlt hg_sub
  exact div_lt_div_of_pos_left hnum hden1 hden2

/-- App. B (`app:twoway`): one-sided normal tail probability is strictly smaller than the
corresponding two-sided `χ²_1` and `χ²_2` tail probabilities for every `t > 0`, so one-sided
normal calibration shrinks even more strictly (`z_cal_1s < √t_2s < √t`). -/
theorem chi2_one_sided_dominance_gaussian_strict (v : ℝ≥0) (hv : v ≠ 0) {σ t : ℝ}
    (hσ : 0 < σ) (ht : 0 < t) :
    let μ := gaussianReal 0 v
    let μp : Measure (ℝ × ℝ) := μ.prod μ
    μ {z | Real.sqrt t * σ ≤ z} < μp {p | t ≤ p.1 ^ 2 / σ ^ 2} ∧
    μp {p | t ≤ p.1 ^ 2 / σ ^ 2} < μp {p | t ≤ (p.1 ^ 2 + p.2 ^ 2) / σ ^ 2} := by
  intro μ μp
  refine ⟨?_, chi2_dominance_gaussian_strict v hv hσ ht⟩
  let E_pos : Set (ℝ × ℝ) := {p | Real.sqrt t * σ ≤ p.1}
  let E_neg : Set (ℝ × ℝ) := {p | p.1 ≤ -(Real.sqrt t * σ)}
  let E_two : Set (ℝ × ℝ) := {p | t ≤ p.1 ^ 2 / σ ^ 2}
  have hpos_eq : E_pos = (Ici (Real.sqrt t * σ)) ×ˢ Set.univ := by
    ext p; simp [E_pos]
  have hμ_Epos : μp E_pos = μ {z | Real.sqrt t * σ ≤ z} := by
    rw [hpos_eq]
    dsimp [μp]
    rw [Measure.prod_prod, measure_univ, mul_one]
    rfl
  have hE_neg_meas : MeasurableSet E_neg :=
    measurableSet_le measurable_fst measurable_const
  have hdisj : Disjoint E_pos E_neg := by
    refine Set.disjoint_left.mpr fun p hp1 hp2 => ?_
    dsimp [E_pos, E_neg] at hp1 hp2
    have hgt : 0 < Real.sqrt t * σ := mul_pos (Real.sqrt_pos.mpr ht) hσ
    linarith [hp1, hp2]
  have hunion : E_pos ∪ E_neg = E_two := by
    ext p
    simp only [Set.mem_union, Set.mem_setOf_eq, E_pos, E_neg, E_two]
    have hsq_eq : t * σ ^ 2 = (Real.sqrt t * σ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt ht.le]
    rw [le_div_iff₀ (sq_pos_of_pos hσ), hsq_eq, sq_le_sq, abs_of_pos (mul_pos (Real.sqrt_pos.mpr ht) hσ)]
    simpa [or_comm] using (le_abs' (a := Real.sqrt t * σ) (b := p.1)).symm
  have hvol_ac : volume ≪ μ := gaussianReal_absolutelyContinuous' 0 hv
  have hneg_pos : 0 < μp E_neg := by
    let a : ℝ := Real.sqrt t * σ
    let A : Set ℝ := Ioo (-(a + 1)) (-a)
    have hA_sub : A ×ˢ Set.univ ⊆ E_neg := by
      intro ⟨x, y⟩ ⟨hx, _⟩
      exact hx.2.le
    have hA_pos : 0 < μ A := by
      rw [pos_iff_ne_zero]
      intro h0
      have hv0 := hvol_ac h0
      have hvolA : volume A = ENNReal.ofReal (-a - -(a + 1)) := Real.volume_Ioo
      rw [hv0] at hvolA
      norm_num at hvolA
    have hprod_pos : 0 < μp (A ×ˢ Set.univ) := by
      dsimp [μp]
      rw [Measure.prod_prod, measure_univ, mul_one]
      exact hA_pos
    exact hprod_pos.trans_le (measure_mono hA_sub)
  change μ {z | Real.sqrt t * σ ≤ z} < μp E_two
  rw [← hμ_Epos, ← hunion, measure_union hdisj hE_neg_meas]
  exact ENNReal.lt_add_right (measure_ne_top μp E_pos) hneg_pos.ne'

theorem chi2_one_sided_calibration_shrinks (v : ℝ≥0) (hv : v ≠ 0) {σ t t_2s z_1s : ℝ}
    (hσ : 0 < σ) (ht : 0 < t)
    (hmatch_2s : (gaussianReal 0 v).prod (gaussianReal 0 v) {p | t_2s ≤ p.1 ^ 2 / σ ^ 2} =
      (gaussianReal 0 v).prod (gaussianReal 0 v) {p | t ≤ (p.1 ^ 2 + p.2 ^ 2) / σ ^ 2})
    (hmatch_1s : gaussianReal 0 v {z | z_1s * σ ≤ z} =
      (gaussianReal 0 v).prod (gaussianReal 0 v) {p | t ≤ (p.1 ^ 2 + p.2 ^ 2) / σ ^ 2}) :
    z_1s < Real.sqrt t ∧ (0 < t_2s → z_1s < Real.sqrt t_2s ∧ Real.sqrt t_2s < Real.sqrt t) := by
  let μ := gaussianReal 0 v
  let μp := μ.prod μ
  have hdom_t := chi2_one_sided_dominance_gaussian_strict v hv hσ ht
  have h1 : μ {z | Real.sqrt t * σ ≤ z} < μ {z | z_1s * σ ≤ z} := by
    rw [hmatch_1s]
    exact hdom_t.1.trans hdom_t.2
  have hz_lt_t : z_1s < Real.sqrt t := by
    by_contra hge
    have hle : Real.sqrt t * σ ≤ z_1s * σ := mul_le_mul_of_nonneg_right (not_lt.mp hge) hσ.le
    have hmono : μ {z | z_1s * σ ≤ z} ≤ μ {z | Real.sqrt t * σ ≤ z} :=
      measure_mono fun z hz => hle.trans hz
    exact h1.not_ge hmono
  refine ⟨hz_lt_t, fun ht2s => ?_⟩
  have h2s_lt : t_2s < t := chi2_calibration_shrinks v hv hσ ht hmatch_2s
  have hsqrt_2s : Real.sqrt t_2s < Real.sqrt t := Real.sqrt_lt_sqrt ht2s.le h2s_lt
  have hdom_2s := (chi2_one_sided_dominance_gaussian_strict v hv hσ ht2s).1
  have h2 : μ {z | Real.sqrt t_2s * σ ≤ z} < μ {z | z_1s * σ ≤ z} := by
    rw [hmatch_1s, ← hmatch_2s]
    exact hdom_2s
  have hz_lt_2s : z_1s < Real.sqrt t_2s := by
    by_contra hge
    have hle : Real.sqrt t_2s * σ ≤ z_1s * σ := mul_le_mul_of_nonneg_right (not_lt.mp hge) hσ.le
    have hmono : μ {z | z_1s * σ ≤ z} ≤ μ {z | Real.sqrt t_2s * σ ≤ z} :=
      measure_mono fun z hz => hle.trans hz
    exact h2.not_ge hmono
  exact ⟨hz_lt_2s, hsqrt_2s⟩

/-- Sec. 3.4 & 6.3-6.4: exact numerical brackets for `2^(γ(1/4)) = 2^(4/3) ≈ 2.5`,
`2^(1 - 1/5) = 2^0.8 ≈ 1.74` (+74%), `4^(1 - 1/5) = 4^0.8 ≈ 3.03` (≈ 3x),
and `(750/280)^0.2 ≈ 1.22`, `(750/2000)^0.2 ≈ 0.82`. -/
theorem paper_exponent_numerical_bounds :
    ((251 / 100 : ℝ) < (2 : ℝ) ^ gamma (1 / 4) ∧ (2 : ℝ) ^ gamma (1 / 4) < (253 / 100 : ℝ)) ∧
    ((174 / 100 : ℝ) < (2 : ℝ) ^ (1 - (1 / 5 : ℝ)) ∧ (2 : ℝ) ^ (1 - (1 / 5 : ℝ)) < (175 / 100 : ℝ)) ∧
    ((303 / 100 : ℝ) < (4 : ℝ) ^ (1 - (1 / 5 : ℝ)) ∧ (4 : ℝ) ^ (1 - (1 / 5 : ℝ)) < (304 / 100 : ℝ)) ∧
    ((121 / 100 : ℝ) < ((750 : ℝ) / 280) ^ (1 / 5 : ℝ) ∧ ((750 : ℝ) / 280) ^ (1 / 5 : ℝ) < (123 / 100 : ℝ)) ∧
    ((81 / 100 : ℝ) < ((750 : ℝ) / 2000) ^ (1 / 5 : ℝ) ∧ ((750 : ℝ) / 2000) ^ (1 / 5 : ℝ) < (83 / 100 : ℝ)) := by
  have hg4 : gamma (1 / 4 : ℝ) = ((4 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) := by unfold gamma; norm_num
  have h15 : (1 : ℝ) - 1 / 5 = ((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) := by norm_num
  have h15' : (1 / 5 : ℝ) = ((1 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) := by norm_num
  have pow_lt_pow_rpow : ∀ {a b : ℝ} (p q : ℕ), 0 ≤ a → 0 ≤ b → 0 < q →
      a ^ q < b ^ p → a < b ^ ((p : ℝ) / q) := by
    intro a b p q ha hb hq hlt
    have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr hq
    have hr := Real.rpow_lt_rpow (pow_nonneg ha q) hlt (one_div_pos.mpr hq_pos)
    have h1 : (a ^ q) ^ (1 / (q : ℝ)) = a := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha, mul_one_div_cancel hq_pos.ne', Real.rpow_one]
    have h2 : (b ^ p) ^ (1 / (q : ℝ)) = b ^ ((p : ℝ) / q) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb, mul_one_div]
    rwa [h1, h2] at hr
  have pow_lt_pow_rpow' : ∀ {a b : ℝ} (p q : ℕ), 0 ≤ a → 0 ≤ b → 0 < q →
      a ^ p < b ^ q → a ^ ((p : ℝ) / q) < b := by
    intro a b p q ha hb hq hlt
    have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr hq
    have hr := Real.rpow_lt_rpow (pow_nonneg ha p) hlt (one_div_pos.mpr hq_pos)
    have h1 : (a ^ p) ^ (1 / (q : ℝ)) = a ^ ((p : ℝ) / q) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha, mul_one_div]
    have h2 : (b ^ q) ^ (1 / (q : ℝ)) = b := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb, mul_one_div_cancel hq_pos.ne', Real.rpow_one]
    rwa [h1, h2] at hr
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [hg4]; exact pow_lt_pow_rpow 4 3 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · rw [hg4]; exact pow_lt_pow_rpow' 4 3 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · rw [h15]; exact pow_lt_pow_rpow 4 5 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · rw [h15]; exact pow_lt_pow_rpow' 4 5 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · rw [h15]; exact pow_lt_pow_rpow 4 5 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · rw [h15]; exact pow_lt_pow_rpow' 4 5 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · rw [h15']; exact pow_lt_pow_rpow 1 5 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · rw [h15']; exact pow_lt_pow_rpow' 1 5 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · rw [h15']; exact pow_lt_pow_rpow 1 5 (by norm_num) (by norm_num) (by omega) (by norm_num)
  · rw [h15']; exact pow_lt_pow_rpow' 1 5 (by norm_num) (by norm_num) (by omega) (by norm_num)

end ZwarProofs

