/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
module

public import Challenge.Reference.RoughHeatKernel.SquareKernel

public section

/-!
# Heat-kernel identities at a diffusion scale `ν`

The kernel `p_{νt}(x) = heatKernel (ν * t) x` is the fundamental solution of
`∂_t u = (ν/2) ∂_x² u`. For `ν > 0` this file restates two identities of the unit-scale
kernel in that time parametrization:

* the squared kernel
  `p_{νt}(x)² = p_{(ν/2)t}(x) · (4πν)^{-1/2} · t^{-1/2}` for `t > 0`
  (`heatKernel_mul_sq_eq`, from `heatKernel_sq_eq`);
* the semigroup identity
  `∫ p_{ν(t-s)}(x - y) p_{νs}(y) dy = p_{νt}(x)` for `0 < s < t`
  (`integral_heatKernel_mul_sub_mul`, from `integral_heatKernel_mul_heatKernel`).
-/

set_option autoImplicit false

namespace RoughHeatKernel

/-- The squared kernel at scale `ν`: for `ν, t > 0`,
`p_{νt}(x)² = p_{(ν/2)t}(x) · (4πν)^{-1/2} · t^{-1/2}`. -/
theorem heatKernel_mul_sq_eq {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (x : ℝ) :
    heatKernel (ν * t) x ^ 2 =
      heatKernel (ν / 2 * t) x * (1 / Real.sqrt (4 * Real.pi * ν)) * t ^ (-(1 / 2 : ℝ)) := by
  have hr : 0 < ν * t := mul_pos hν ht
  rw [heatKernel_sq_eq hr x, show ν / 2 * t = ν * t / 2 by ring,
    Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow,
    show 4 * Real.pi * (ν * t) = (4 * Real.pi * ν) * t by ring,
    Real.sqrt_mul (by positivity) t]
  field_simp

/-- The semigroup identity at scale `ν`: for `ν > 0` and `0 < s < t`,
`∫ p_{ν(t-s)}(x - y) p_{νs}(y) dy = p_{νt}(x)`. -/
theorem integral_heatKernel_mul_sub_mul {ν s t : ℝ} (hν : 0 < ν) (hs : 0 < s) (hst : s < t)
    (x : ℝ) :
    ∫ y, heatKernel (ν * (t - s)) (x - y) * heatKernel (ν * s) y = heatKernel (ν * t) x := by
  rw [integral_heatKernel_mul_heatKernel (mul_pos hν hs) (mul_pos hν (sub_pos.mpr hst)) x]
  congr 1
  ring

end RoughHeatKernel
