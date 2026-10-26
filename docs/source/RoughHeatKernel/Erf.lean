/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
module

public import RoughHeatKernel.Beta
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# The error function and the standard normal distribution function

This file defines

* the error function `erf x = (2/√π) ∫_0^x e^{-t²} dt` and `erfc = 1 - erf`;
* the standard normal density `normalDensity y = (2π)^{-1/2} e^{-y²/2}`;
* the standard normal distribution function `normalCDF x = ∫_{-∞}^x (2π)^{-1/2} e^{-y²/2} dy`.

It proves `normalCDF 0 = 1/2`, that `normalCDF` is differentiable with derivative
`normalDensity`, the identity `normalCDF x = (1 + erf (x/√2))/2`, and, for `z ≥ 0`, the
series (DLMF 7.6.2, reindexed)

`Σ_{k ≥ 0} z^k / Γ(k/2 + 1) = e^{z²} (1 + erf z)`.

Even terms are the exponential series of `z²`. For odd terms, the Beta integral
(`integral_rpow_mul_sub_rpow` with `a = 1/2`, `b = m + 1`) and the substitution `s = u²` give
`z^{2m+1}/Γ(m + 3/2) = (2/√π) ∫_0^z (z² - u²)^m/m! du`; summing under the integral
(dominated convergence) yields `(2/√π) ∫_0^z e^{z² - u²} du = e^{z²} erf z`.

Mathlib (at the pinned revision) has neither an error function nor a named Gaussian
distribution function. The material is adapted from a companion formalization of
Chen–Dalang (Ann. Probab. 2015), where these facts enter the resolvent-kernel computation.
-/

set_option autoImplicit false

namespace RoughHeatKernel

open Real MeasureTheory intervalIntegral Set
open scoped Nat

/-- The error function `erf x = (2/√π) ∫_0^x e^{-t²} dt` (an oriented interval integral, so
`erf` is odd). The body is written exactly as TauCeti's
`TauCeti.Analysis.SpecialFunctions.Erf.erf`, so a later bridge to that definition is
definitional. -/
noncomputable def erf (x : ℝ) : ℝ := 2 / Real.sqrt Real.pi * ∫ t in (0 : ℝ)..x, Real.exp (-t ^ 2)

/-- The complementary error function `erfc x = 1 - erf x`. -/
noncomputable def erfc (x : ℝ) : ℝ := 1 - erf x

/-- The standard normal density `(2π)^{-1/2} e^{-y²/2}`. -/
noncomputable def normalDensity (y : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2)

/-- The standard normal distribution function
`normalCDF x = ∫_{(-∞, x]} (2π)^{-1/2} e^{-y²/2} dy`. -/
noncomputable def normalCDF (x : ℝ) : ℝ :=
  ∫ y in Set.Iic x, (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2)

/-! ### The normal density and distribution function -/

/-- `normalCDF x` is the integral of `normalDensity` over `(-∞, x]` (definitionally). -/
theorem normalCDF_eq_integral_normalDensity (x : ℝ) :
    normalCDF x = ∫ y in Set.Iic x, normalDensity y := rfl

/-- The standard normal density is continuous. -/
theorem continuous_normalDensity : Continuous normalDensity := by
  unfold normalDensity; fun_prop

/-- The standard normal density is Lebesgue integrable on `ℝ`. -/
theorem integrable_normalDensity : Integrable normalDensity := by
  have h := (integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)).const_mul
    (Real.sqrt (2 * π))⁻¹
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [normalDensity]
  congr 2
  ring

/-- The Gaussian `e^{-y²/2}` is integrable on `ℝ`. -/
private theorem integrable_exp_neg_sq_div_two :
    Integrable (fun y : ℝ => Real.exp (-y ^ 2 / 2)) := by
  have h := integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only
  congr 1
  ring

/-- `∫_{-∞}^0 e^{-y²/2} dy = √(2π)/2`. -/
private theorem integral_Iic_zero_exp_neg_sq_div_two :
    ∫ y in Iic (0 : ℝ), Real.exp (-y ^ 2 / 2) = Real.sqrt (2 * π) / 2 := by
  have h := integral_comp_neg_Iic (0 : ℝ) (fun y : ℝ => Real.exp (-(1 / 2) * y ^ 2))
  have h2 := integral_gaussian_Ioi (1 / 2)
  simp only [neg_zero, even_two, Even.neg_pow] at h
  rw [h2] at h
  have h3 : π / (1 / 2) = 2 * π := by ring
  rw [h3] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Iic fun y _ => ?_
  congr 1
  ring

/-- `normalCDF 0 = 1/2`. -/
theorem normalCDF_zero : normalCDF 0 = 1 / 2 := by
  unfold normalCDF
  rw [MeasureTheory.integral_const_mul, integral_Iic_zero_exp_neg_sq_div_two]
  have : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  field_simp

/-- `normalCDF x = normalCDF 0 + ∫_0^x normalDensity` (an oriented interval integral). -/
theorem normalCDF_eq_add_integral (x : ℝ) :
    normalCDF x = normalCDF 0 + ∫ y in (0 : ℝ)..x, normalDensity y := by
  rw [normalCDF_eq_integral_normalDensity, normalCDF_eq_integral_normalDensity,
    ← intervalIntegral.integral_Iic_sub_Iic integrable_normalDensity.integrableOn
      integrable_normalDensity.integrableOn]
  ring

/-- The distribution function has derivative the density: `normalCDF' = normalDensity`. -/
theorem hasDerivAt_normalCDF (x : ℝ) : HasDerivAt normalCDF (normalDensity x) x := by
  have h := intervalIntegral.integral_hasDerivAt_right
    (continuous_normalDensity.intervalIntegrable 0 x)
    (continuous_normalDensity.stronglyMeasurableAtFilter _ _)
    continuous_normalDensity.continuousAt
  have hfun : normalCDF = fun x => normalCDF 0 + ∫ y in (0 : ℝ)..x, normalDensity y :=
    funext normalCDF_eq_add_integral
  rw [hfun]
  exact h.const_add _

/-- The standard normal distribution function is continuous. -/
theorem continuous_normalCDF : Continuous normalCDF :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_normalCDF x).continuousAt

/-! ### `normalCDF` and `erf` -/

/-- Substitution `y = √2 u`: `∫_0^x e^{-y²/2} dy = √2 ∫_0^{x/√2} e^{-u²} du`. -/
private theorem integral_exp_neg_sq_div_two (x : ℝ) :
    ∫ y in (0 : ℝ)..x, Real.exp (-y ^ 2 / 2) =
      Real.sqrt 2 * ∫ u in (0 : ℝ)..x / Real.sqrt 2, Real.exp (-u ^ 2) := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h := intervalIntegral.integral_comp_mul_left
    (fun y : ℝ => Real.exp (-y ^ 2 / 2)) (a := 0) (b := x / Real.sqrt 2) hs
  simp only [mul_zero, smul_eq_mul] at h
  rw [mul_div_cancel₀ _ hs] at h
  have hc : ∀ u : ℝ, Real.exp (-(Real.sqrt 2 * u) ^ 2 / 2) = Real.exp (-u ^ 2) := by
    intro u
    congr 1
    rw [mul_pow, hs2]
    ring
  simp only [hc] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]

/-- `normalCDF x = (1 + erf (x/√2))/2`. -/
theorem normalCDF_eq_erf (x : ℝ) : normalCDF x = (1 + erf (x / Real.sqrt 2)) / 2 := by
  have hint : ∀ a : ℝ, IntegrableOn
      (fun y : ℝ => (Real.sqrt (2 * π))⁻¹ * Real.exp (-y ^ 2 / 2)) (Iic a) := fun a =>
    (integrable_exp_neg_sq_div_two.const_mul _).integrableOn
  have hsub := intervalIntegral.integral_Iic_sub_Iic (hint 0) (hint x)
  have hPhi : normalCDF x = normalCDF 0 + ∫ y in (0 : ℝ)..x,
      (Real.sqrt (2 * π))⁻¹ * Real.exp (-y ^ 2 / 2) := by
    unfold normalCDF
    rw [← hsub]
    ring
  rw [hPhi, normalCDF_zero, intervalIntegral.integral_const_mul, integral_exp_neg_sq_div_two]
  unfold erf
  have hpi : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have h2pi : Real.sqrt (2 * π) = Real.sqrt 2 * Real.sqrt π := Real.sqrt_mul (by norm_num) π
  have hs : 0 < Real.sqrt 2 := by positivity
  rw [h2pi]
  field_simp

/-! ### The series `Σ z^k / Γ(k/2 + 1) = e^{z²} (1 + erf z)` -/

/-- The integrand after the substitution `s = u²` in the Beta integral. -/
private theorem rpow_sq_mul_two_mul {u : ℝ} (hu : 0 < u) (c : ℝ) :
    (u ^ 2) ^ (-(1 / 2 : ℝ)) * c * (2 * u) = 2 * c := by
  rw [Real.rpow_neg (sq_nonneg u), ← Real.sqrt_eq_rpow, Real.sqrt_sq hu.le]
  field_simp

/-- For `z ≥ 0` and `m : ℕ`,
`∫_0^z (z² - u²)^m du = z^{2m+1} · √π m! / (2 Γ(m + 3/2))`. -/
theorem integral_sq_sub_sq_pow {z : ℝ} (hz : 0 ≤ z) (m : ℕ) :
    ∫ u in (0 : ℝ)..z, (z ^ 2 - u ^ 2) ^ m =
      z ^ (2 * m + 1) * (Real.sqrt π * (m ! : ℝ) / (2 * Real.Gamma ((m : ℝ) + 3 / 2))) := by
  rcases hz.eq_or_lt with h0 | hz0
  · subst h0
    simp
  set g : ℝ → ℝ := fun s => s ^ (-(1 / 2 : ℝ)) * (z ^ 2 - s) ^ m with hg
  have hB := integral_rpow_mul_sub_rpow (a := 1 / 2) (b := (m : ℝ) + 1)
    (by norm_num) (by positivity) (pow_pos hz0 2)
  have hexp : (1 / 2 : ℝ) - 1 = -(1 / 2) := by norm_num
  simp only [hexp, add_sub_cancel_right, Real.rpow_natCast] at hB
  -- substitution `s = u²`
  have hsubst := intervalIntegral.integral_comp_mul_deriv''' (a := 0) (b := z)
    (f := fun u : ℝ => u ^ 2) (f' := fun u => 2 * u) (g := g)
    (by fun_prop)
    (fun x _ => by
      simpa using ((hasDerivAt_pow 2 x).hasDerivWithinAt (s := Ioi x)))
    (by
      intro s hs
      obtain ⟨u, hu, rfl⟩ := hs
      rw [min_eq_left hz, max_eq_right hz] at hu
      have hu2 : (u ^ 2) ≠ 0 := by have := hu.1; positivity
      refine ContinuousAt.continuousWithinAt ?_
      refine ContinuousAt.mul ?_ (by fun_prop)
      exact Real.continuousAt_rpow_const _ _ (Or.inl hu2))
    (by
      have hI : IntervalIntegrable g volume 0 (z ^ 2) :=
        (intervalIntegral.intervalIntegrable_rpow' (r := -(1 / 2)) (by norm_num)).mul_continuousOn
          (by fun_prop)
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity)] at hI
      refine hI.mono_set ?_
      rintro _ ⟨u, hu, rfl⟩
      rw [uIcc_of_le hz] at hu
      exact ⟨sq_nonneg u, pow_le_pow_left₀ hu.1 hu.2 2⟩)
    (by
      rw [uIcc_of_le hz, integrableOn_Icc_iff_integrableOn_Ioc]
      have hc : IntegrableOn (fun u : ℝ => 2 * (z ^ 2 - u ^ 2) ^ m) (Ioc 0 z) :=
        (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioc_subset_Icc_self
      refine hc.congr_fun (fun u hu => ?_) measurableSet_Ioc
      simp only [hg, Function.comp]
      rw [rpow_sq_mul_two_mul hu.1])
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hsubst
  rw [hB] at hsubst
  have hL : ∫ x in (0 : ℝ)..z, (g ∘ fun u : ℝ => u ^ 2) x * (fun u => 2 * u) x =
      ∫ x in (0 : ℝ)..z, 2 * (z ^ 2 - x ^ 2) ^ m := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun u hu => ?_)
    rw [uIoc_of_le hz] at hu
    simp only [hg, Function.comp]
    rw [rpow_sq_mul_two_mul hu.1]
  rw [hL, intervalIntegral.integral_const_mul] at hsubst
  have hpow : (z ^ 2) ^ ((1 / 2 : ℝ) + ((m : ℝ) + 1) - 1) = z ^ (2 * m + 1) := by
    rw [← Real.rpow_natCast z 2, ← Real.rpow_mul hz, ← Real.rpow_natCast z (2 * m + 1)]
    congr 1
    push_cast
    ring
  have hG : Real.Gamma (1 / 2 + ((m : ℝ) + 1)) = Real.Gamma ((m : ℝ) + 3 / 2) := by
    congr 1
    ring
  rw [hpow, hG, Real.Gamma_one_half_eq, Real.Gamma_nat_eq_factorial] at hsubst
  have hΓ : 0 < Real.Gamma ((m : ℝ) + 3 / 2) := Real.Gamma_pos_of_pos (by positivity)
  field_simp at hsubst ⊢
  linear_combination hsubst

/-- Odd part of the series: `Σ_m z^{2m+1}/Γ(m + 3/2) = e^{z²} erf z` for `z ≥ 0`. -/
theorem hasSum_odd_pow_div_Gamma {z : ℝ} (hz : 0 ≤ z) :
    HasSum (fun m : ℕ => z ^ (2 * m + 1) / Real.Gamma ((m : ℝ) + 3 / 2))
      (Real.exp (z ^ 2) * erf z) := by
  have hDC : HasSum (fun m : ℕ => ∫ u in (0 : ℝ)..z, (z ^ 2 - u ^ 2) ^ m / (m ! : ℝ))
      (∫ u in (0 : ℝ)..z, Real.exp (z ^ 2) * Real.exp (-u ^ 2)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => (z ^ 2) ^ n / (n ! : ℝ))
      (fun n => (Continuous.aestronglyMeasurable (by fun_prop)))
      (fun n => Filter.Eventually.of_forall fun u hu => ?_)
      (Filter.Eventually.of_forall fun u _ => Real.summable_pow_div_factorial _)
      intervalIntegrable_const
      (Filter.Eventually.of_forall fun u _ => ?_)
    · rw [uIoc_of_le hz] at hu
      have h1 : 0 ≤ z ^ 2 - u ^ 2 := sub_nonneg.mpr (pow_le_pow_left₀ hu.1.le hu.2 2)
      have h2 : z ^ 2 - u ^ 2 ≤ z ^ 2 := by nlinarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      gcongr
    · have := NormedSpace.expSeries_div_hasSum_exp (z ^ 2 - u ^ 2)
      rw [← Real.exp_eq_exp_ℝ, sub_eq_add_neg, Real.exp_add] at this
      simpa [sub_eq_add_neg] using this
  have hterm : ∀ m : ℕ, z ^ (2 * m + 1) / Real.Gamma ((m : ℝ) + 3 / 2) =
      2 / Real.sqrt π * ∫ u in (0 : ℝ)..z, (z ^ 2 - u ^ 2) ^ m / (m ! : ℝ) := by
    intro m
    rw [intervalIntegral.integral_div, integral_sq_sub_sq_pow hz m]
    have hpi : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
    have hΓ : 0 < Real.Gamma ((m : ℝ) + 3 / 2) := Real.Gamma_pos_of_pos (by positivity)
    have hf : (0 : ℝ) < m ! := by exact_mod_cast Nat.factorial_pos m
    field_simp
  have := hDC.mul_left (2 / Real.sqrt π)
  rw [intervalIntegral.integral_const_mul] at this
  convert this using 1
  · exact funext hterm
  · unfold erf
    ring

/-- Even part of the series: `Σ_m z^{2m}/Γ(m + 1) = e^{z²}` for every real `z`. -/
theorem hasSum_even_pow_div_Gamma (z : ℝ) :
    HasSum (fun m : ℕ => z ^ (2 * m) / Real.Gamma ((m : ℝ) + 1)) (Real.exp (z ^ 2)) := by
  have := NormedSpace.expSeries_div_hasSum_exp (z ^ 2)
  rw [← Real.exp_eq_exp_ℝ] at this
  convert this using 2 with m
  rw [Real.Gamma_nat_eq_factorial, pow_mul]

/-- The series of DLMF 7.6.2, reindexed: for `z ≥ 0`,
`Σ_{k ≥ 0} z^k / Γ(k/2 + 1) = e^{z²} (1 + erf z)`. -/
theorem hasSum_pow_div_Gamma {z : ℝ} (hz : 0 ≤ z) :
    HasSum (fun k : ℕ => z ^ k / Real.Gamma ((k : ℝ) / 2 + 1))
      (Real.exp (z ^ 2) * (1 + erf z)) := by
  rw [show Real.exp (z ^ 2) * (1 + erf z) = Real.exp (z ^ 2) + Real.exp (z ^ 2) * erf z by ring]
  refine HasSum.even_add_odd ?_ ?_
  · convert hasSum_even_pow_div_Gamma z using 3 with m
    push_cast
    ring_nf
  · convert hasSum_odd_pow_div_Gamma hz using 3 with m
    push_cast
    ring_nf

end RoughHeatKernel
