/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Challenge.Reference.RoughHeatKernel.ChenDalang
/-!
# The semigroup property of the heat flow

For every s-finite positive measure `ν` and `0 < s < t`,

`∫ p_{t-s}(x - y) J(s, y) dy = J(t, x)`, where `J = lheatFlow ν`
(`lintegral_heatKernel_mul_lheatFlow`),

and integrating over `s ∈ (0, t)`,

`∫_0^t ∫ p_{t-s}(x - y) J(s, y) dy ds = t J(t, x)`
(`lintegral_lintegral_heatKernel_mul_lheatFlow`).

Both are stated with lower Lebesgue integrals, so they hold for every s-finite `ν`
(including measures whose heat flow is infinite).
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace RoughHeatKernel

attribute [local fun_prop] continuous_heatKernel measurable_heatKernel

/-- The semigroup identity in `y`: `∫ p_{t-s}(x - y) p_s(y - z) dy = p_t(x - z)`. -/
private theorem integral_heatKernel_sub_mul_heatKernel_sub' {s t : ℝ} (hs : 0 < s)
    (hst : s < t) (x z : ℝ) :
    ∫ y, heatKernel (t - s) (x - y) * heatKernel s (y - z) = heatKernel t (x - z) := by
  have hts : 0 < t - s := by linarith
  have h := integral_heatKernel_mul_heatKernel hs hts (x - z)
  rw [← integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun u => heatKernel (t - s) (x - z - u) * heatKernel s u) z] at h
  rw [sub_add_cancel] at h
  rw [← h]
  congr 1
  ext y
  rw [show x - z - (y - z) = x - y by ring]

private theorem integrable_heatKernel_sub_mul_heatKernel_sub' {s t : ℝ} (hs : 0 < s)
    (hst : s < t) (x z : ℝ) :
    Integrable (fun y => heatKernel (t - s) (x - y) * heatKernel s (y - z)) := by
  have hts : 0 < t - s := by linarith
  refine ((integrable_heatKernel_sub_mul_heatKernel hs hts (x - z)).comp_sub_right z).congr
    (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [show x - z - (y - z) = x - y by ring]

/-- The semigroup property of the heat flow: for every s-finite `ν` and `0 < s < t`,
`∫ p_{t-s}(x - y) J(s, y) dy = J(t, x)` with `J = lheatFlow ν`. -/
theorem lintegral_heatKernel_mul_lheatFlow (ν : Measure ℝ) [SFinite ν] {s t : ℝ}
    (hs : 0 < s) (hst : s < t) (x : ℝ) :
    ∫⁻ y, ENNReal.ofReal (heatKernel (t - s) (x - y)) * lheatFlow ν s y =
      lheatFlow ν t x := by
  have hts : 0 < t - s := by linarith
  calc ∫⁻ y, ENNReal.ofReal (heatKernel (t - s) (x - y)) * lheatFlow ν s y
      = ∫⁻ y, ∫⁻ z, ENNReal.ofReal (heatKernel (t - s) (x - y)) *
          ENNReal.ofReal (heatKernel s (y - z)) ∂ν := by
        refine lintegral_congr fun y => ?_
        rw [lheatFlow, lintegral_const_mul _ (by fun_prop)]
    _ = ∫⁻ z, (∫⁻ y, ENNReal.ofReal (heatKernel (t - s) (x - y)) *
          ENNReal.ofReal (heatKernel s (y - z))) ∂ν := by
        have hm : Measurable fun q : ℝ × ℝ => ENNReal.ofReal (heatKernel (t - s) (x - q.1)) *
            ENNReal.ofReal (heatKernel s (q.1 - q.2)) := by fun_prop
        exact lintegral_lintegral_swap (μ := volume) (ν := ν)
          (f := fun y z => ENNReal.ofReal (heatKernel (t - s) (x - y)) *
            ENNReal.ofReal (heatKernel s (y - z))) hm.aemeasurable
    _ = ∫⁻ z, ENNReal.ofReal (heatKernel t (x - z)) ∂ν := by
        refine lintegral_congr fun z => ?_
        simp_rw [← ENNReal.ofReal_mul (heatKernel_pos hts _).le]
        rw [← ofReal_integral_eq_lintegral_ofReal
          (integrable_heatKernel_sub_mul_heatKernel_sub' hs hst x z)
          (Filter.Eventually.of_forall fun y =>
            mul_nonneg (heatKernel_pos hts _).le (heatKernel_pos hs _).le),
          integral_heatKernel_sub_mul_heatKernel_sub' hs hst x z]
    _ = lheatFlow ν t x := rfl

/-- The time-integrated semigroup property: for every s-finite `ν` and real `t`,
`∫_0^t ∫ p_{t-s}(x - y) J(s, y) dy ds = t J(t, x)` with `J = lheatFlow ν` (for `t ≤ 0` both
sides are `0`). -/
theorem lintegral_lintegral_heatKernel_mul_lheatFlow (ν : Measure ℝ) [SFinite ν] (t x : ℝ) :
    ∫⁻ s in Ioo 0 t, ∫⁻ y, ENNReal.ofReal (heatKernel (t - s) (x - y)) * lheatFlow ν s y =
      ENNReal.ofReal t * lheatFlow ν t x := by
  rw [setLIntegral_congr_fun measurableSet_Ioo
    (fun s hs => lintegral_heatKernel_mul_lheatFlow ν hs.1 hs.2 x),
    setLIntegral_const, Real.volume_Ioo, sub_zero, mul_comm]

end RoughHeatKernel
