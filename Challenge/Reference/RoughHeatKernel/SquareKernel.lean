/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Challenge.Reference.RoughHeatKernel.ChenDalang
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# The squared kernel and the white-noise convolution bound

The second moment of a Walsh stochastic convolution `∫_0^t ∫ p_{t-s}(x - y) Φ(s, y) W(ds dy)`
is controlled by `∫_0^t ∫ p_{t-s}(x - y)² ‖Φ(s, y)‖² dy ds`. This file supplies the
deterministic facts used to bound that integral when `‖Φ(s, y)‖ ≤ J(s, y)`:

* `p_r(z)² = p_{r/2}(z) / √(4πr)` (`heatKernel_sq_eq`), hence `∫ p_r² = (4πr)^{-1/2}`
  (`integral_heatKernel_sq`);
* the arcsine integral `∫_0^t ds / √(s (t - s)) = π` (`lintegral_arcsine`);
* the white-noise form of the Chen–Dalang estimate,
  `∫_0^t ∫ J(s, y)² p_{t-s}(x - y)² dy ds ≤ √π √t J(2t, x)²`
  (`lintegral_sq_lheatFlow_mul_heatKernel_sq_le`), for every s-finite measure, as lower
  Lebesgue integrals.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace RoughHeatKernel

attribute [local fun_prop] continuous_heatKernel measurable_heatKernel

/-! ### The squared kernel -/

/-- `p_r(z)² = p_{r/2}(z) · (4πr)^{-1/2}` for `r > 0`. -/
theorem heatKernel_sq_eq {r : ℝ} (hr : 0 < r) (z : ℝ) :
    heatKernel r z ^ 2 = heatKernel (r / 2) z * (1 / Real.sqrt (4 * Real.pi * r)) := by
  have hA : 0 < 2 * Real.pi * r := by positivity
  have h1 : Real.sqrt (2 * Real.pi * r) ^ 2 = 2 * Real.pi * r := Real.sq_sqrt hA.le
  have h2 : Real.sqrt (2 * Real.pi * (r / 2)) * Real.sqrt (4 * Real.pi * r) =
      2 * Real.pi * r := by
    rw [← Real.sqrt_mul (by positivity),
      show 2 * Real.pi * (r / 2) * (4 * Real.pi * r) = (2 * Real.pi * r) ^ 2 by ring,
      Real.sqrt_sq hA.le]
  have hr' : r ≠ 0 := hr.ne'
  unfold heatKernel
  rw [mul_pow, div_pow, one_pow, h1, ← Real.exp_nat_mul]
  calc 1 / (2 * Real.pi * r) * Real.exp (↑2 * (-(1 / (2 * r)) * z ^ 2))
      = 1 / (Real.sqrt (2 * Real.pi * (r / 2)) * Real.sqrt (4 * Real.pi * r)) *
          Real.exp (-(1 / (2 * (r / 2))) * z ^ 2) := by
        rw [h2]
        congr 2
        field_simp
    _ = _ := by ring

/-- `∫ p_r(z)² dz = (4πr)^{-1/2}` for `r > 0`. -/
theorem integral_heatKernel_sq {r : ℝ} (hr : 0 < r) :
    ∫ z, heatKernel r z ^ 2 = 1 / Real.sqrt (4 * Real.pi * r) := by
  simp_rw [heatKernel_sq_eq hr]
  rw [integral_mul_const, integral_heatKernel (by positivity), one_mul]

/-! ### The arcsine integral -/

private theorem hasDerivAt_arcsin_affine {t s : ℝ} (ht : 0 < t) (hs : s ∈ Ioo 0 t) :
    HasDerivAt (fun s => Real.arcsin ((2 * s - t) / t)) (1 / Real.sqrt (s * (t - s))) s := by
  obtain ⟨h0, h1⟩ := hs
  have hu1 : (2 * s - t) / t ≠ -1 := by
    rw [ne_eq, div_eq_iff ht.ne']; intro h; linarith
  have hu2 : (2 * s - t) / t ≠ 1 := by
    rw [ne_eq, div_eq_iff ht.ne']; intro h; linarith
  have hlin : HasDerivAt (fun s => (2 * s - t) / t) (2 * 1 / t) s :=
    (((hasDerivAt_id s).const_mul 2).sub_const t).div_const t
  have h := (Real.hasDerivAt_arcsin hu1 hu2).comp s hlin
  refine h.congr_deriv ?_
  have hq : 0 < s * (t - s) := mul_pos h0 (by linarith)
  have hid : 1 - ((2 * s - t) / t) ^ 2 = (2 / t) ^ 2 * (s * (t - s)) := by
    field_simp; ring
  rw [hid, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have : 0 < Real.sqrt (s * (t - s)) := Real.sqrt_pos.mpr hq
  field_simp

/-- The arcsine integral: `∫_0^t ds / √(s (t - s)) = π` for `t > 0`. -/
theorem lintegral_arcsine {t : ℝ} (ht : 0 < t) :
    ∫⁻ s in Ioo 0 t, ENNReal.ofReal (1 / Real.sqrt (s * (t - s))) = ENNReal.ofReal Real.pi := by
  have hcont : ContinuousOn (fun s => Real.arcsin ((2 * s - t) / t)) (Icc 0 t) :=
    (Real.continuous_arcsin.comp (by fun_prop)).continuousOn
  have hder : ∀ s ∈ Ioo 0 t, HasDerivAt (fun s => Real.arcsin ((2 * s - t) / t))
      (1 / Real.sqrt (s * (t - s))) s := fun s hs => hasDerivAt_arcsin_affine ht hs
  have hnn : ∀ s ∈ Ioo 0 t, 0 ≤ 1 / Real.sqrt (s * (t - s)) := fun s _ =>
    one_div_nonneg.mpr (Real.sqrt_nonneg _)
  have hint : IntegrableOn (fun s => 1 / Real.sqrt (s * (t - s))) (Ioc 0 t) :=
    intervalIntegral.integrableOn_deriv_of_nonneg hcont hder hnn
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.le hcont hder
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mpr hint)
  rw [intervalIntegral.integral_of_le ht.le] at hFTC
  have hval : Real.arcsin ((2 * t - t) / t) - Real.arcsin ((2 * 0 - t) / t) = Real.pi := by
    rw [show (2 * t - t) / t = 1 by field_simp; ring,
      show (2 * 0 - t) / t = -1 by field_simp; ring, Real.arcsin_one, Real.arcsin_neg_one]
    ring
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc, ← hval, ← hFTC,
    ofReal_integral_eq_lintegral_ofReal hint]
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun s _ => ?_)
  exact one_div_nonneg.mpr (Real.sqrt_nonneg _)

/-! ### The white-noise convolution bound -/

/-- `∫_0^t (4π(t - s))^{-1/2} s^{-1/2} ds = √π / 2`. -/
private theorem lintegral_h_div_sqrt {t : ℝ} (ht : 0 < t) :
    ∫⁻ s in Ioo 0 t, ENNReal.ofReal (1 / Real.sqrt (4 * Real.pi * (t - s))) *
        ENNReal.ofReal (1 / Real.sqrt s) = ENNReal.ofReal (Real.sqrt Real.pi / 2) := by
  have h4π : Real.sqrt (4 * Real.pi) = 2 * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  calc ∫⁻ s in Ioo 0 t, ENNReal.ofReal (1 / Real.sqrt (4 * Real.pi * (t - s))) *
        ENNReal.ofReal (1 / Real.sqrt s)
      = ∫⁻ s in Ioo 0 t, ENNReal.ofReal (1 / Real.sqrt (4 * Real.pi)) *
          ENNReal.ofReal (1 / Real.sqrt (s * (t - s))) := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
        have hs0 : 0 < s := hs.1
        have hts : 0 < t - s := by linarith [hs.2]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Real.sqrt_mul (by positivity) (t - s), Real.sqrt_mul hs0.le (t - s)]
        have : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
        have : 0 < Real.sqrt (t - s) := Real.sqrt_pos.mpr hts
        have : 0 < Real.sqrt (4 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
        field_simp
    _ = ENNReal.ofReal (1 / Real.sqrt (4 * Real.pi)) * ENNReal.ofReal Real.pi := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_arcsine ht]
    _ = ENNReal.ofReal (Real.sqrt Real.pi / 2) := by
        rw [← ENNReal.ofReal_mul (by positivity), h4π]
        congr 1
        have hsq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
          Real.mul_self_sqrt Real.pi_pos.le
        field_simp
        linarith

/-- The white-noise Chen–Dalang bound: for every s-finite `ν`, `t > 0` and `x`,
`∫_0^t ∫ J(s, y)² p_{t-s}(x - y)² dy ds ≤ √π √t J(2t, x)²`, `J = lheatFlow ν`, as lower
Lebesgue integrals. -/
theorem lintegral_sq_lheatFlow_mul_heatKernel_sq_le (ν : Measure ℝ) [SFinite ν] {t : ℝ}
    (ht : 0 < t) (x : ℝ) :
    ∫⁻ s in Ioo 0 t, ∫⁻ y, lheatFlow ν s y ^ 2 *
        ENNReal.ofReal (heatKernel (t - s) (x - y) ^ 2) ≤
      ENNReal.ofReal (Real.sqrt Real.pi * Real.sqrt t) * lheatFlow ν (2 * t) x ^ 2 := by
  set h : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (1 / Real.sqrt (4 * Real.pi * r))
  have hh : Measurable h := by fun_prop
  have key := lintegral_sq_lheatFlow_conv_le ν ht x hh
  calc ∫⁻ s in Ioo 0 t, ∫⁻ y, lheatFlow ν s y ^ 2 *
        ENNReal.ofReal (heatKernel (t - s) (x - y) ^ 2)
      = ∫⁻ s in Ioo 0 t, ∫⁻ y, lheatFlow ν s y ^ 2 *
          ENNReal.ofReal (heatKernel ((t - s) / 2) (x - y)) * h (t - s) := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => lintegral_congr fun y => ?_
        have hts : 0 < t - s := by linarith [hs.2]
        rw [heatKernel_sq_eq hts, ENNReal.ofReal_mul (heatKernel_pos (by positivity) _).le]
        simp only [h]
        ring
    _ ≤ ENNReal.ofReal (2 * Real.sqrt t) * lheatFlow ν (2 * t) x ^ 2 *
          ∫⁻ s in Ioo 0 t, h (t - s) * ENNReal.ofReal (1 / Real.sqrt s) := key
    _ = ENNReal.ofReal (Real.sqrt Real.pi * Real.sqrt t) * lheatFlow ν (2 * t) x ^ 2 := by
        rw [lintegral_h_div_sqrt ht, mul_right_comm, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

end RoughHeatKernel
