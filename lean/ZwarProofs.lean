import Mathlib

/-!
# Formal Verification of Derivations in *From Total WAR to WAR Rate*

This file formalizes and verifies every mathematical proposition, identity,
and inequality in `zwar_paper.tex` against Mathlib (`v4.26.0`), with zero
`sorry`s and only standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`).
-/

open scoped Real BigOperators MeasureTheory ProbabilityTheory Topology
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

/-! ## Section 1: Eq. (1) Endpoints and Weighted Geometric Mean -/

theorem z_alpha_zero (W N : ℝ) : Z_alpha W N 0 = W := by
  simp [Z_alpha]

theorem z_alpha_one (W N : ℝ) : Z_alpha W N 1 = W / N := by
  simp [Z_alpha]

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

theorem prop_alpha_discrete_iff {W N ΔW ΔN α : ℝ}
    (hW : 0 < W) (hN : 0 < N) (hΔN : 0 < ΔN) :
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
    (hZ₁ : 0 < Z₁) (hZ₂ : 0 ≤ Z₂) (hle : Z₂ ≤ Z₁) (_h0 : 0 ≤ α) (h1 : α < 1) :
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

/-! ## Section 7: Proposition 5 (`prop:lagrange`) and Remark (`rem:partition`) -/

theorem prop_lagrange_identity {W_pos PA W_pitch BF : ℝ} (hPA : PA ≠ 0) (hBF : BF ≠ 0)
    (hsum : PA + BF ≠ 0) :
    W_pos ^ 2 / PA + W_pitch ^ 2 / BF - (W_pos + W_pitch) ^ 2 / (PA + BF) =
      (PA * BF / (PA + BF)) * (W_pos / PA - W_pitch / BF) ^ 2 := by
  field_simp [hPA, hBF, hsum]
  ring

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

/-! ## Section 10: Remark (`rem:interp`, Gaussian KL Divergence Identity) -/

theorem kl_gaussian_zwar {W N σ : ℝ} (hN : 0 < N) (hσ : 0 < σ) :
    let r_hat := W / N
    let D_KL := (r_hat - 0) ^ 2 / (2 * (σ ^ 2 / N))
    D_KL = W ^ 2 / (2 * σ ^ 2 * N) ∧
    Real.sign W * σ * Real.sqrt (2 * D_KL) = Z_alpha W N (1 / 2) := by
  intro r_hat D_KL
  have hDKL : D_KL = W ^ 2 / (2 * σ ^ 2 * N) := by
    simp only [D_KL, r_hat, sub_zero]
    field_simp [hN.ne', hσ.ne']
  refine ⟨hDKL, ?_⟩
  rw [hDKL]
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

end ZwarProofs
