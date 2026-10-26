/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
module

public import Challenge.Reference.RoughHeatKernel.SquareKernel
public import Challenge.Reference.RoughHeatKernel.FlowSemigroup

public section
/-!
# Doubled-profile bounds

Bounds that compare the heat flow `J = lheatFlow ν` at time `2s` or `t + s` with the doubled
profile `J(2t, ·)`, for `0 < s < t`:

* the Gaussian doubling comparison `p_{t+s}(ξ) ≤ √2 p_{2t}(ξ)` for `0 ≤ s ≤ t`
  (`heatKernel_add_le_sqrt_two_mul`), hence `J(t + s, x) ≤ √2 J(2t, x)`
  (`lheatFlow_add_le_sqrt_two_mul`);
* the doubled semigroup bound `∫ p_{t-s}(x - y) J(2s, y) dy = J(t + s, x) ≤ √2 J(2t, x)`
  (`lintegral_heatKernel_mul_lheatFlow_two_mul`, `lintegral_heatKernel_mul_lheatFlow_two_mul_le`);
* the `s`-resolved quadratic bound
  `∫ p_{t-s}(x - y)² J(2s, y)² dy ≤ (2π)^{-1/2} t^{1/2} (s (t - s))^{-1/2} J(2t, x)²`
  (`lintegral_heatKernel_sq_mul_lheatFlow_two_mul_sq_le`), global in `x`.

All are stated with lower Lebesgue integrals, for every s-finite positive measure `ν`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace RoughHeatKernel

attribute [local fun_prop] continuous_heatKernel measurable_heatKernel

/-! ### Gaussian doubling -/

/-- Gaussian doubling: `p_{t+s}(ξ) ≤ √2 p_{2t}(ξ)` for `t > 0` and `0 ≤ s ≤ t`. -/
theorem heatKernel_add_le_sqrt_two_mul {s t : ℝ} (ht : 0 < t) (hs : 0 ≤ s) (hst : s ≤ t)
    (ξ : ℝ) : heatKernel (t + s) ξ ≤ Real.sqrt 2 * heatKernel (2 * t) ξ := by
  have h := heatKernel_le_sqrt_div_mul (by linarith : 0 < t + s) (by linarith : t + s ≤ 2 * t) ξ
  refine h.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_)
    (heatKernel_pos (by linarith) _).le)
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- `J(t + s, x) ≤ √2 J(2t, x)` for `t > 0` and `0 ≤ s ≤ t`. -/
theorem lheatFlow_add_le_sqrt_two_mul (ν : Measure ℝ) {s t : ℝ} (ht : 0 < t) (hs : 0 ≤ s)
    (hst : s ≤ t) (x : ℝ) :
    lheatFlow ν (t + s) x ≤ ENNReal.ofReal (Real.sqrt 2) * lheatFlow ν (2 * t) x := by
  unfold lheatFlow
  rw [← lintegral_const_mul _ (by fun_prop)]
  refine lintegral_mono fun z => ?_
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
  exact ENNReal.ofReal_le_ofReal (heatKernel_add_le_sqrt_two_mul ht hs hst _)

/-! ### The doubled semigroup bound -/

/-- `∫ p_{t-s}(x - y) J(2s, y) dy = J(t + s, x)` for `0 < s < t`. -/
theorem lintegral_heatKernel_mul_lheatFlow_two_mul (ν : Measure ℝ) [SFinite ν] {s t : ℝ}
    (hs : 0 < s) (hst : s < t) (x : ℝ) :
    ∫⁻ y, ENNReal.ofReal (heatKernel (t - s) (x - y)) * lheatFlow ν (2 * s) y =
      lheatFlow ν (t + s) x := by
  have h := lintegral_heatKernel_mul_lheatFlow ν (by linarith : 0 < 2 * s)
    (by linarith : 2 * s < t + s) x
  rwa [show t + s - 2 * s = t - s by ring] at h

/-- The doubled semigroup bound: `∫ p_{t-s}(x - y) J(2s, y) dy ≤ √2 J(2t, x)` for
`0 < s < t`. -/
theorem lintegral_heatKernel_mul_lheatFlow_two_mul_le (ν : Measure ℝ) [SFinite ν] {s t : ℝ}
    (hs : 0 < s) (hst : s < t) (x : ℝ) :
    ∫⁻ y, ENNReal.ofReal (heatKernel (t - s) (x - y)) * lheatFlow ν (2 * s) y ≤
      ENNReal.ofReal (Real.sqrt 2) * lheatFlow ν (2 * t) x := by
  rw [lintegral_heatKernel_mul_lheatFlow_two_mul ν hs hst x]
  exact lheatFlow_add_le_sqrt_two_mul ν (hs.trans hst) hs.le hst.le x

/-! ### The `s`-resolved quadratic bound -/

private theorem integral_heatKernel_sub_mul_heatKernel_sub'' {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (x m : ℝ) :
    ∫ y, heatKernel a (y - m) * heatKernel b (x - y) = heatKernel (a + b) (x - m) := by
  have h := integral_heatKernel_mul_heatKernel ha hb (x - m)
  rw [← integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun y => heatKernel b (x - m - y) * heatKernel a y) m] at h
  rw [add_comm a b, ← h]
  congr 1
  ext y
  rw [show x - m - (y - m) = x - y by ring, mul_comm]

private theorem integrable_heatKernel_sub_mul_heatKernel_sub'' {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (x m : ℝ) :
    Integrable (fun y => heatKernel a (y - m) * heatKernel b (x - y)) := by
  have h := (integrable_heatKernel_sub_mul_heatKernel ha hb (x - m)).comp_sub_right m
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [show x - m - (y - m) = x - y by ring, mul_comm]

/-- The doubled pointwise step: for `0 < s < t`,
`∫ p_{2s}(y - z₁) p_{2s}(y - z₂) p_{(t-s)/2}(x - y) dy ≤ √(2t/s) p_{2t}(x - z₁) p_{2t}(x - z₂)`. -/
theorem lintegral_heatKernel_two_mul_mul_le {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (x z₁ z₂ : ℝ) :
    ∫⁻ y, ENNReal.ofReal (heatKernel (2 * s) (y - z₁)) *
        ENNReal.ofReal (heatKernel (2 * s) (y - z₂)) *
        ENNReal.ofReal (heatKernel ((t - s) / 2) (x - y)) ≤
      ENNReal.ofReal (Real.sqrt (2 * t / s)) *
        (ENNReal.ofReal (heatKernel (2 * t) (x - z₁)) *
          ENNReal.ofReal (heatKernel (2 * t) (x - z₂))) := by
  have ht : 0 < t := hs.trans hst
  have hts : 0 < (t - s) / 2 := by linarith
  have hs' : 0 < 2 * s / 2 := by positivity
  have hp : ∀ r : ℝ, 0 < r → ∀ u, 0 ≤ heatKernel r u := fun r hr u => (heatKernel_pos hr u).le
  have e : ∀ y, ENNReal.ofReal (heatKernel (2 * s) (y - z₁)) *
      ENNReal.ofReal (heatKernel (2 * s) (y - z₂)) *
      ENNReal.ofReal (heatKernel ((t - s) / 2) (x - y)) =
      ENNReal.ofReal (heatKernel (2 * (2 * s)) (z₁ - z₂)) *
        ENNReal.ofReal (heatKernel (2 * s / 2) (y - (z₁ + z₂) / 2) *
          heatKernel ((t - s) / 2) (x - y)) := by
    intro y
    rw [← ENNReal.ofReal_mul (hp _ (by positivity) _),
      ← ENNReal.ofReal_mul (mul_nonneg (hp _ (by positivity) _) (hp _ (by positivity) _)),
      ← ENNReal.ofReal_mul (hp _ (by positivity) _),
      heatKernel_mul_heatKernel_eq (by positivity : 0 < 2 * s)]
    congr 1
    ring
  simp_rw [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal
      (integrable_heatKernel_sub_mul_heatKernel_sub'' hs' hts x ((z₁ + z₂) / 2))
      (Filter.Eventually.of_forall fun y => mul_nonneg (hp _ hs' _) (hp _ hts _)),
    integral_heatKernel_sub_mul_heatKernel_sub'' hs' hts,
    show 2 * s / 2 + (t - s) / 2 = (t + s) / 2 by ring,
    ← ENNReal.ofReal_mul (hp _ (by positivity) _),
    ← ENNReal.ofReal_mul (hp _ (by positivity) _),
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [heatKernel_mul_heatKernel_eq (by positivity : 0 < 2 * t) x z₁ z₂]
  have k1 := heatKernel_le_sqrt_div_mul (by positivity : 0 < 2 * (2 * s))
    (by linarith : 2 * (2 * s) ≤ 2 * (2 * t)) (z₁ - z₂)
  have k2 := heatKernel_le_sqrt_div_mul (by positivity : 0 < (t + s) / 2)
    (by linarith : (t + s) / 2 ≤ 2 * t / 2) (x - (z₁ + z₂) / 2)
  have hc1 : Real.sqrt (2 * (2 * t) / (2 * (2 * s))) = Real.sqrt (t / s) := by
    congr 1; field_simp
  have hc2 : Real.sqrt (2 * t / 2 / ((t + s) / 2)) ≤ Real.sqrt 2 :=
    Real.sqrt_le_sqrt (by rw [div_le_iff₀ (by positivity)]; linarith)
  have hc : Real.sqrt (t / s) * Real.sqrt 2 = Real.sqrt (2 * t / s) := by
    rw [← Real.sqrt_mul (by positivity)]; congr 1; ring
  rw [hc1] at k1
  calc heatKernel (2 * (2 * s)) (z₁ - z₂) * heatKernel ((t + s) / 2) (x - (z₁ + z₂) / 2)
      ≤ (Real.sqrt (t / s) * heatKernel (2 * (2 * t)) (z₁ - z₂)) *
          (Real.sqrt 2 * heatKernel (2 * t / 2) (x - (z₁ + z₂) / 2)) := by
        refine mul_le_mul k1 (k2.trans (mul_le_mul_of_nonneg_right hc2 (hp _ (by positivity) _)))
          (hp _ (by positivity) _) (mul_nonneg (Real.sqrt_nonneg _) (hp _ (by positivity) _))
    _ = Real.sqrt (2 * t / s) * (heatKernel (2 * (2 * t)) (z₁ - z₂) *
          heatKernel (2 * t / 2) (x - (z₁ + z₂) / 2)) := by rw [← hc]; ring

private theorem lheatFlow_sq_eq' (ν : Measure ℝ) [SFinite ν] (s y : ℝ) :
    lheatFlow ν s y ^ 2 = ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (heatKernel s (y - q.1)) *
      ENNReal.ofReal (heatKernel s (y - q.2)) ∂(ν.prod ν) := by
  rw [sq, lheatFlow]
  exact (lintegral_prod_mul (μ := ν) (ν := ν)
    (f := fun z => ENNReal.ofReal (heatKernel s (y - z)))
    (g := fun z => ENNReal.ofReal (heatKernel s (y - z))) (by fun_prop) (by fun_prop)).symm

/-- `(4π(t - s))^{-1/2} √(2t/s) = (2π)^{-1/2} t^{1/2} (s (t - s))^{-1/2}`. -/
private theorem const_tail_quad {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    1 / Real.sqrt (4 * Real.pi * (t - s)) * Real.sqrt (2 * t / s) =
      1 / Real.sqrt (2 * Real.pi) * (Real.sqrt t / Real.sqrt (s * (t - s))) := by
  have hts : 0 < t - s := by linarith
  have ht : 0 < t := hs.trans hst
  rw [show 4 * Real.pi * (t - s) = 2 * (2 * Real.pi) * (t - s) by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_div' _ hs.le,
    Real.sqrt_mul (by norm_num), Real.sqrt_mul hs.le]
  have h1 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have h3 : 0 < Real.sqrt (t - s) := Real.sqrt_pos.mpr hts
  have h4 : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  field_simp
  rw [mul_comm t 2, Real.sqrt_mul (by norm_num)]

/-- The time-resolved quadratic bound: for every s-finite `ν`,
`0 < s < t` and `x`,
`∫ p_{t-s}(x - y)² J(2s, y)² dy ≤ (2π)^{-1/2} t^{1/2} (s (t - s))^{-1/2} J(2t, x)²`,
`J = lheatFlow ν`. It is global in `x`. -/
theorem lintegral_heatKernel_sq_mul_lheatFlow_two_mul_sq_le (ν : Measure ℝ) [SFinite ν]
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (x : ℝ) :
    ∫⁻ y, ENNReal.ofReal (heatKernel (t - s) (x - y) ^ 2) * lheatFlow ν (2 * s) y ^ 2 ≤
      ENNReal.ofReal (1 / Real.sqrt (2 * Real.pi) * (Real.sqrt t / Real.sqrt (s * (t - s)))) *
        lheatFlow ν (2 * t) x ^ 2 := by
  have hts : 0 < t - s := by linarith
  set k := ENNReal.ofReal (1 / Real.sqrt (4 * Real.pi * (t - s)))
  have hF : Measurable fun q : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (heatKernel (2 * s) (q.1 - q.2.1)) *
        ENNReal.ofReal (heatKernel (2 * s) (q.1 - q.2.2)) *
        ENNReal.ofReal (heatKernel ((t - s) / 2) (x - q.1)) * k := by fun_prop
  calc ∫⁻ y, ENNReal.ofReal (heatKernel (t - s) (x - y) ^ 2) * lheatFlow ν (2 * s) y ^ 2
      = ∫⁻ y, ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (heatKernel (2 * s) (y - q.1)) *
          ENNReal.ofReal (heatKernel (2 * s) (y - q.2)) *
            ENNReal.ofReal (heatKernel ((t - s) / 2) (x - y)) * k ∂(ν.prod ν) := by
        refine lintegral_congr fun y => ?_
        rw [heatKernel_sq_eq hts, ENNReal.ofReal_mul (heatKernel_pos (by positivity) _).le,
          lheatFlow_sq_eq', ← lintegral_const_mul _ (by fun_prop)]
        refine lintegral_congr fun q => ?_
        ring
    _ = ∫⁻ q : ℝ × ℝ, (∫⁻ y : ℝ, ENNReal.ofReal (heatKernel (2 * s) (y - q.1)) *
          ENNReal.ofReal (heatKernel (2 * s) (y - q.2)) *
            ENNReal.ofReal (heatKernel ((t - s) / 2) (x - y)) * k) ∂(ν.prod ν) :=
        lintegral_lintegral_swap hF.aemeasurable
    _ ≤ ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (Real.sqrt (2 * t / s)) *
          (ENNReal.ofReal (heatKernel (2 * t) (x - q.1)) *
            ENNReal.ofReal (heatKernel (2 * t) (x - q.2))) * k ∂(ν.prod ν) := by
        refine lintegral_mono fun q => ?_
        rw [lintegral_mul_const _ (by fun_prop)]
        gcongr
        exact lintegral_heatKernel_two_mul_mul_le hs hst x q.1 q.2
    _ = ENNReal.ofReal (Real.sqrt (2 * t / s)) * k * lheatFlow ν (2 * t) x ^ 2 := by
        rw [lintegral_mul_const _ (by fun_prop), lintegral_const_mul _ (by fun_prop),
          lheatFlow_sq_eq']
        ring
    _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), mul_comm (Real.sqrt _),
          const_tail_quad hs hst]

end RoughHeatKernel
