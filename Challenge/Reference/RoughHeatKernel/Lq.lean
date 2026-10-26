/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
module

public import Challenge.Reference.RoughHeatKernel.Kernel

@[expose] public section
/-!
# `L^q` norms of the heat kernel

For every `q ∈ [1, ∞]` and `t > 0`,
`‖p_t‖_{L^q(ℝ)} = C_q t^{-(1 - 1/q)/2}`, with the explicit constant
`C_q = (2π)^{-(1-1/q)/2} q^{-1/(2q)}` for finite `q` and `C_∞ = (2π)^{-1/2}`.
The norm is Mathlib's `eLpNorm` against Lebesgue measure; at `q = ∞` it is the essential
supremum, and the exponent uses `∞⁻¹ = 0`.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace RoughHeatKernel

/-- The finite-`q` constant `(2π)^{-(1-1/q)/2} q^{-1/(2q)}`, for real `q`. -/
noncomputable def lqConstReal (q : ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(1 / 2) * (1 - 1 / q)) * q ^ (-(1 / (2 * q)))

private theorem lqConstReal_pos {q : ℝ} (hq : 1 ≤ q) : 0 < lqConstReal q := by
  unfold lqConstReal
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _)
    (Real.rpow_pos_of_pos (by linarith) _)

/-- The constant `C_q` in `‖p_t‖_q = C_q t^{-(1-1/q)/2}`: `(2π)^{-1/2}` at `q = ∞`, and
`(2π)^{-(1-1/q)/2} q^{-1/(2q)}` for finite `q`. -/
noncomputable def heatLqConst (q : ℝ≥0∞) : ℝ :=
  if q = ∞ then (2 * Real.pi) ^ (-(1 : ℝ) / 2) else lqConstReal q.toReal

private theorem one_le_toReal {q : ℝ≥0∞} (hq : 1 ≤ q) (hqt : q ≠ ∞) : 1 ≤ q.toReal := by
  have := ENNReal.toReal_mono hqt hq
  simpa using this

theorem heatLqConst_pos {q : ℝ≥0∞} (hq : 1 ≤ q) : 0 < heatLqConst q := by
  unfold heatLqConst
  split_ifs with hqt
  · exact Real.rpow_pos_of_pos (by positivity) _
  · exact lqConstReal_pos (one_le_toReal hq hqt)

private theorem heatKernel_rpow_eq {q t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatKernel t x ^ q =
      (1 / Real.sqrt (2 * Real.pi * t)) ^ q * Real.exp (-(q / (2 * t)) * x ^ 2) := by
  unfold heatKernel
  have hc : 0 ≤ 1 / Real.sqrt (2 * Real.pi * t) := by positivity
  rw [Real.mul_rpow hc (Real.exp_pos _).le, ← Real.exp_mul]
  congr 2
  ring

private theorem lq_real_identity {q t : ℝ} (hq : 1 ≤ q) (ht : 0 < t) :
    ((1 / Real.sqrt (2 * Real.pi * t)) ^ q * Real.sqrt (Real.pi / (q / (2 * t)))) ^ (1 / q) =
      lqConstReal q * t ^ (-(1 / 2) * (1 - 1 / q)) := by
  have hq0 : 0 < q := by linarith
  have hπ := Real.pi_pos
  have hsq : 0 < Real.sqrt (2 * Real.pi * t) := Real.sqrt_pos.mpr (by positivity)
  have hc : 0 < 1 / Real.sqrt (2 * Real.pi * t) := one_div_pos.mpr hsq
  have hs : 0 < Real.sqrt (Real.pi / (q / (2 * t))) := Real.sqrt_pos.mpr (by positivity)
  have hL : 0 < ((1 / Real.sqrt (2 * Real.pi * t)) ^ q *
      Real.sqrt (Real.pi / (q / (2 * t)))) ^ (1 / q) :=
    Real.rpow_pos_of_pos (mul_pos (Real.rpow_pos_of_pos hc _) hs) _
  have hR : 0 < lqConstReal q * t ^ (-(1 / 2) * (1 - 1 / q)) :=
    mul_pos (lqConstReal_pos hq) (Real.rpow_pos_of_pos ht _)
  apply Real.log_injOn_pos (Set.mem_Ioi.mpr hL) (Set.mem_Ioi.mpr hR)
  unfold lqConstReal
  rw [Real.log_rpow (mul_pos (Real.rpow_pos_of_pos hc _) hs),
    Real.log_mul (Real.rpow_pos_of_pos hc _).ne' hs.ne', Real.log_rpow hc,
    Real.log_sqrt (by positivity), one_div (Real.sqrt _), Real.log_inv,
    Real.log_sqrt (by positivity),
    Real.log_mul (mul_pos (Real.rpow_pos_of_pos (by positivity) _)
      (Real.rpow_pos_of_pos hq0 _)).ne' (Real.rpow_pos_of_pos ht _).ne',
    Real.log_mul (Real.rpow_pos_of_pos (by positivity) _).ne'
      (Real.rpow_pos_of_pos hq0 _).ne',
    Real.log_rpow (by positivity), Real.log_rpow hq0, Real.log_rpow ht,
    Real.log_div hπ.ne' (by positivity), Real.log_div hq0.ne' (by positivity),
    Real.log_mul (by norm_num) ht.ne']
  have e1 : Real.log (2 * t) = Real.log 2 + Real.log t := Real.log_mul (by norm_num) ht.ne'
  have e2 : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num) hπ.ne'
  simp only [e1, e2]
  field_simp
  ring

/-- `‖p_t‖_∞ = (2πt)^{-1/2}`, the essential supremum, attained at the origin. -/
theorem eLpNorm_heatKernel_top {t : ℝ} (ht : 0 < t) :
    eLpNorm (heatKernel t) ∞ volume = ENNReal.ofReal (1 / Real.sqrt (2 * Real.pi * t)) := by
  have hmeas : AEStronglyMeasurable (heatKernel t) volume :=
    (integrable_heatKernel ht).aestronglyMeasurable
  rw [eLpNorm_exponent_top hmeas, eLpNormEssSup]
  have henorm (x : ℝ) : ‖heatKernel t x‖ₑ = ENNReal.ofReal (heatKernel t x) :=
    Real.enorm_eq_ofReal (heatKernel_pos ht x).le
  apply le_antisymm
  · refine essSup_le_iSup.trans (iSup_le fun x => ?_)
    rw [henorm, ← heatKernel_zero]
    exact ENNReal.ofReal_le_ofReal (heatKernel_le_heatKernel_zero ht x)
  · by_contra hlt
    rw [not_le] at hlt
    set M := essSup (fun x => ‖heatKernel t x‖ₑ) volume
    have hcont : Continuous fun x => ‖heatKernel t x‖ₑ := (continuous_heatKernel t).enorm
    have hU : IsOpen {x : ℝ | M < ‖heatKernel t x‖ₑ} := isOpen_lt continuous_const hcont
    have h0U : (0 : ℝ) ∈ {x : ℝ | M < ‖heatKernel t x‖ₑ} := by
      simp only [Set.mem_ofPred_eq, henorm, heatKernel_zero]
      exact hlt
    have hpos := hU.measure_pos volume ⟨0, h0U⟩
    have hae := ENNReal.ae_le_essSup (μ := (volume : Measure ℝ))
      (fun x => ‖heatKernel t x‖ₑ)
    rw [ae_iff] at hae
    simp only [not_le] at hae
    exact hpos.ne' hae

/-- `‖p_t‖_q = C_q t^{-(1-1/q)/2}` for finite `q ≥ 1`. -/
theorem eLpNorm_heatKernel_of_ne_top {q : ℝ≥0∞} (hq : 1 ≤ q) (hqt : q ≠ ∞) {t : ℝ}
    (ht : 0 < t) :
    eLpNorm (heatKernel t) q volume =
      ENNReal.ofReal (heatLqConst q * t ^ (-(1 - q⁻¹.toReal) / 2)) := by
  have hq0 : q ≠ 0 := (lt_of_lt_of_le zero_lt_one hq).ne'
  have hr := one_le_toReal hq hqt
  have hr0 : 0 < q.toReal := by linarith
  have hmeas : AEStronglyMeasurable (heatKernel t) volume :=
    (integrable_heatKernel ht).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt hmeas]
  have hpt (x : ℝ) : ‖heatKernel t x‖ₑ ^ q.toReal =
      ENNReal.ofReal (heatKernel t x ^ q.toReal) := by
    rw [Real.enorm_eq_ofReal (heatKernel_pos ht x).le,
      ENNReal.ofReal_rpow_of_nonneg (heatKernel_pos ht x).le hr0.le]
  rw [lintegral_congr hpt]
  have hform : (fun x => heatKernel t x ^ q.toReal) = fun x =>
      (1 / Real.sqrt (2 * Real.pi * t)) ^ q.toReal *
        Real.exp (-(q.toReal / (2 * t)) * x ^ 2) :=
    funext (heatKernel_rpow_eq ht)
  have hint : Integrable (fun x => heatKernel t x ^ q.toReal) := by
    rw [hform]
    exact (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (heatKernel_pos ht x).le _),
    hform, integral_const_mul, integral_gaussian,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), lq_real_identity hr ht]
  unfold heatLqConst
  simp only [hqt, ↓reduceIte, ENNReal.toReal_inv]
  congr 3
  ring

/-- `(2πt)^{-1/2} = (2π)^{-1/2} t^{-1/2}`. -/
private theorem inv_sqrt_two_pi_mul {t : ℝ} (ht : 0 < t) :
    1 / Real.sqrt (2 * Real.pi * t) = (2 * Real.pi) ^ (-(1 : ℝ) / 2) * t ^ (-(1 : ℝ) / 2) := by
  have hπ := Real.pi_pos
  have hsq : 0 < Real.sqrt (2 * Real.pi * t) := Real.sqrt_pos.mpr (by positivity)
  have hL : 0 < 1 / Real.sqrt (2 * Real.pi * t) := one_div_pos.mpr hsq
  have hR : 0 < (2 * Real.pi) ^ (-(1 : ℝ) / 2) * t ^ (-(1 : ℝ) / 2) :=
    mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos ht _)
  apply Real.log_injOn_pos (Set.mem_Ioi.mpr hL) (Set.mem_Ioi.mpr hR)
  rw [one_div, Real.log_inv, Real.log_sqrt (by positivity),
    Real.log_mul (Real.rpow_pos_of_pos (by positivity) _).ne'
      (Real.rpow_pos_of_pos ht _).ne',
    Real.log_rpow (by positivity), Real.log_rpow ht,
    Real.log_mul (by positivity) ht.ne']
  ring

/-- `‖p_t‖_{L^q(ℝ)} = C_q t^{-(1-1/q)/2}` for every `q ∈ [1, ∞]` and `t > 0`. -/
theorem eLpNorm_heatKernel {q : ℝ≥0∞} (hq : 1 ≤ q) {t : ℝ} (ht : 0 < t) :
    eLpNorm (heatKernel t) q volume =
      ENNReal.ofReal (heatLqConst q * t ^ (-(1 - q⁻¹.toReal) / 2)) := by
  by_cases hqt : q = ∞
  · subst hqt
    rw [eLpNorm_heatKernel_top ht, inv_sqrt_two_pi_mul ht, heatLqConst]
    simp only [↓reduceIte, ENNReal.inv_top, ENNReal.toReal_zero, sub_zero]
  · exact eLpNorm_heatKernel_of_ne_top hq hqt ht

end RoughHeatKernel
