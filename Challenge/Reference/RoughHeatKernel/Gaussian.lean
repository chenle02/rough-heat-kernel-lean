/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
module

public import Challenge.Reference.RoughHeatKernel.Kernel
public import Mathlib.Probability.Distributions.Gaussian.Real

public section

/-!
# Bridge to Mathlib's Gaussian distribution

The heat kernel is the density of the centred normal law: `heatKernel t = gaussianPDFReal 0 t`
for every real `t` (for `t ≤ 0` both sides are `0`, since `t.toNNReal = 0`). Consequently,
integrating against `gaussianReal x t` is integrating against `heatKernel t (x - ·)`.
This lets results stated for `heatKernel` be used by code written with Mathlib's
`gaussianPDFReal` and `gaussianReal`, and conversely.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace RoughHeatKernel

/-- The heat kernel is the centred Gaussian density with variance `t`, for every real `t`. -/
theorem heatKernel_eq_gaussianPDFReal (t x : ℝ) :
    heatKernel t x = gaussianPDFReal 0 t.toNNReal x := by
  rw [gaussianPDFReal, heatKernel, one_div]
  rcases le_or_gt t 0 with ht | ht
  · have h0 : (t.toNNReal : ℝ) = 0 := by simp [Real.toNNReal_eq_zero.mpr ht]
    have hs : Real.sqrt (2 * Real.pi * t) = 0 :=
      Real.sqrt_eq_zero'.mpr (by nlinarith [Real.pi_pos])
    simp [h0, hs]
  · have h0 : (t.toNNReal : ℝ) = t := Real.coe_toNNReal t ht.le
    rw [h0]
    congr 2
    ring

/-- `gaussianPDFReal x t y = heatKernel t (x - y)` for every `t`: the density of `N(x, t)`
at `y` is the kernel at `x - y` (both sides are `0` when `t = 0`). -/
theorem gaussianPDFReal_eq_heatKernel_sub (x : ℝ) (t : NNReal) (y : ℝ) :
    gaussianPDFReal x t y = heatKernel t (x - y) := by
  rw [gaussianPDFReal, heatKernel, one_div]
  congr 2
  ring

/-- Integration against the normal law `N(x, t)` is integration against
`heatKernel t (x - ·)`. -/
theorem integral_gaussianReal_eq_integral_heatKernel {t : NNReal} (ht : t ≠ 0) (x : ℝ)
    (f : ℝ → ℝ) :
    ∫ y, f y ∂gaussianReal x t = ∫ y, heatKernel t (x - y) * f y := by
  rw [integral_gaussianReal_eq_integral_smul ht]
  simp only [smul_eq_mul, gaussianPDFReal_eq_heatKernel_sub]

end RoughHeatKernel
