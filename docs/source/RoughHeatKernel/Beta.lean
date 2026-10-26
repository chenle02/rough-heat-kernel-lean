/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

public section

/-!
# The real Beta integral on `[0, t]`

For `a, b, t > 0`,

`∫_0^t s^{a-1} (t - s)^{b-1} ds = t^{a+b-1} Γ(a) Γ(b) / Γ(a + b)`

(`integral_rpow_mul_sub_rpow`; DLMF 5.12.1 after the substitution `s = t u`). Mathlib states
the identity for complex exponents (`Complex.betaIntegral_scaled`); this file transfers it to
real `rpow`. Since the value is positive, the integrand is interval integrable on `[0, t]`
(`intervalIntegrable_rpow_mul_sub_rpow`), even though it is unbounded at an endpoint when
`a < 1` or `b < 1`.
-/

set_option autoImplicit false

namespace RoughHeatKernel

open Real intervalIntegral

/-- The real Beta integral on `[0, t]` (DLMF 5.12.1, scaled): for `a, b, t > 0`,
`∫_0^t s^{a-1} (t - s)^{b-1} ds = t^{a+b-1} Γ(a) Γ(b) / Γ(a + b)`. -/
theorem integral_rpow_mul_sub_rpow {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    ∫ s in (0 : ℝ)..t, s ^ (a - 1) * (t - s) ^ (b - 1) =
      t ^ (a + b - 1) * (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)) := by
  have hC := Complex.betaIntegral_scaled (a : ℂ) (b : ℂ) ht
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using ha) (by simpa using hb)] at hC
  -- On `[0, t]` the complex integrand is the cast of the real one.
  have hcongr : ∫ x in (0 : ℝ)..t, (x : ℂ) ^ ((a : ℂ) - 1) * ((t : ℂ) - x) ^ ((b : ℂ) - 1) =
      ∫ x in (0 : ℝ)..t, ((x ^ (a - 1) * (t - x) ^ (b - 1) : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le ht.le] at hx
    have hx0 : 0 ≤ x := hx.1
    have htx : 0 ≤ t - x := sub_nonneg.mpr hx.2
    simp only [Complex.ofReal_mul]
    rw [Complex.ofReal_cpow hx0, Complex.ofReal_cpow htx]
    push_cast
    ring_nf
  rw [hcongr, intervalIntegral.integral_ofReal] at hC
  have hrhs : (t : ℂ) ^ ((a : ℂ) + b - 1) *
      (Complex.Gamma a * Complex.Gamma b / Complex.Gamma (a + b)) =
      ((t ^ (a + b - 1) * (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_cpow ht.le]
    push_cast
    rw [← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal]
  rw [hrhs] at hC
  exact_mod_cast hC

/-- The Beta integrand `s^{a-1} (t - s)^{b-1}` is interval integrable on `[0, t]` for
`a, b, t > 0`: its interval integral is the positive Beta value, not Lean's junk `0`. -/
theorem intervalIntegrable_rpow_mul_sub_rpow {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht : 0 < t) :
    IntervalIntegrable (fun s => s ^ (a - 1) * (t - s) ^ (b - 1)) MeasureTheory.volume 0 t := by
  refine intervalIntegrable_of_integral_ne_zero ?_
  rw [integral_rpow_mul_sub_rpow ha hb ht]
  have h1 := Real.Gamma_pos_of_pos ha
  have h2 := Real.Gamma_pos_of_pos hb
  have h3 := Real.Gamma_pos_of_pos (add_pos ha hb)
  have h4 : 0 < t ^ (a + b - 1) := Real.rpow_pos_of_pos ht _
  positivity

end RoughHeatKernel
