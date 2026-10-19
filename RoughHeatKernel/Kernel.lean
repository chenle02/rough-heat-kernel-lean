/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Convolution

/-!
# The one-dimensional heat kernel

`heatKernel t x = (2πt)^{-1/2} exp(-x²/(2t))` is the fundamental solution of
`∂_t u = (1/2) ∂_x² u` on `ℝ`. This file proves its basic properties for `t > 0`:
positivity, continuity, the peak value at `0`, integrability, total mass one, and the
semigroup identity `p_t ⋆ p_s = p_{t+s}`, both pointwise as an integral and through
Mathlib's `convolution`.

For `t ≤ 0` the value is a junk value (`heatKernel t x = 0`); every theorem that needs
a positive time assumes it.
-/

set_option autoImplicit false

open MeasureTheory

namespace RoughHeatKernel

/-- The heat kernel `p_t(x) = (2πt)^{-1/2} exp(-x²/(2t))`. -/
noncomputable def heatKernel (t x : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi * t)) * Real.exp (-(1 / (2 * t)) * x ^ 2)

theorem heatKernel_pos {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 < heatKernel t x := by
  unfold heatKernel
  have : 0 < Real.sqrt (2 * Real.pi * t) := Real.sqrt_pos.mpr (by positivity)
  positivity

theorem heatKernel_neg (t x : ℝ) : heatKernel t (-x) = heatKernel t x := by
  simp [heatKernel]

theorem continuous_heatKernel (t : ℝ) : Continuous (heatKernel t) := by
  unfold heatKernel
  fun_prop

theorem heatKernel_zero (t : ℝ) : heatKernel t 0 = 1 / Real.sqrt (2 * Real.pi * t) := by
  simp [heatKernel]

/-- The kernel attains its maximum `(2πt)^{-1/2}` at the origin. -/
theorem heatKernel_le_heatKernel_zero {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatKernel t x ≤ heatKernel t 0 := by
  rw [heatKernel_zero]
  unfold heatKernel
  have hc : 0 < 1 / Real.sqrt (2 * Real.pi * t) :=
    one_div_pos.mpr (Real.sqrt_pos.mpr (by positivity))
  have hb : 0 ≤ (1 / (2 * t)) * x ^ 2 := by positivity
  calc 1 / Real.sqrt (2 * Real.pi * t) * Real.exp (-(1 / (2 * t)) * x ^ 2)
      ≤ 1 / Real.sqrt (2 * Real.pi * t) * 1 := by
        apply mul_le_mul_of_nonneg_left _ hc.le
        rw [Real.exp_le_one_iff]
        linarith
    _ = 1 / Real.sqrt (2 * Real.pi * t) := mul_one _

theorem integrable_heatKernel {t : ℝ} (ht : 0 < t) : Integrable (heatKernel t) := by
  unfold heatKernel
  exact (integrable_exp_neg_mul_sq (by positivity)).const_mul _

/-- The heat kernel has total mass one. -/
theorem integral_heatKernel {t : ℝ} (ht : 0 < t) : ∫ x, heatKernel t x = 1 := by
  unfold heatKernel
  rw [integral_const_mul, integral_gaussian]
  have heq : Real.pi / (1 / (2 * t)) = 2 * Real.pi * t := by
    field_simp
  rw [heq]
  have hs : 0 < Real.sqrt (2 * Real.pi * t) := Real.sqrt_pos.mpr (by positivity)
  simp [hs.ne']

/-- Completing the square: the semigroup integrand is a constant times a Gaussian in
`y` centred at `s x / (t + s)` with precision `(t + s) / (2 t s)`. -/
private theorem heatKernel_sub_mul_heatKernel_eq {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (x y : ℝ) :
    heatKernel t (x - y) * heatKernel s y =
      (1 / Real.sqrt (2 * Real.pi * t) * (1 / Real.sqrt (2 * Real.pi * s)) *
          Real.exp (-(1 / (2 * (t + s))) * x ^ 2)) *
        Real.exp (-((t + s) / (2 * t * s)) * (y - s * x / (t + s)) ^ 2) := by
  unfold heatKernel
  have hts : t + s ≠ 0 := (add_pos ht hs).ne'
  have hexp : -(1 / (2 * t)) * (x - y) ^ 2 + -(1 / (2 * s)) * y ^ 2 =
      -(1 / (2 * (t + s))) * x ^ 2 +
        -((t + s) / (2 * t * s)) * (y - s * x / (t + s)) ^ 2 := by
    field_simp
    ring
  calc _ = 1 / Real.sqrt (2 * Real.pi * t) * (1 / Real.sqrt (2 * Real.pi * s)) *
        Real.exp (-(1 / (2 * t)) * (x - y) ^ 2 + -(1 / (2 * s)) * y ^ 2) := by
          rw [Real.exp_add]; ring
    _ = _ := by rw [hexp, Real.exp_add]; ring

theorem integrable_heatKernel_sub_mul_heatKernel {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (x : ℝ) : Integrable (fun y => heatKernel t (x - y) * heatKernel s y) := by
  have hb : 0 < (t + s) / (2 * t * s) := by positivity
  have h := ((integrable_exp_neg_mul_sq hb).comp_sub_right (s * x / (t + s))).const_mul
    (1 / Real.sqrt (2 * Real.pi * t) * (1 / Real.sqrt (2 * Real.pi * s)) *
      Real.exp (-(1 / (2 * (t + s))) * x ^ 2))
  exact h.congr (Filter.Eventually.of_forall fun y =>
    (heatKernel_sub_mul_heatKernel_eq hs ht x y).symm)

/-- The semigroup identity `∫ p_t(x - y) p_s(y) dy = p_{t+s}(x)`. -/
theorem integral_heatKernel_mul_heatKernel {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x : ℝ) :
    ∫ y, heatKernel t (x - y) * heatKernel s y = heatKernel (t + s) x := by
  have hfun : (fun y => heatKernel t (x - y) * heatKernel s y) = fun y =>
      (1 / Real.sqrt (2 * Real.pi * t) * (1 / Real.sqrt (2 * Real.pi * s)) *
          Real.exp (-(1 / (2 * (t + s))) * x ^ 2)) *
        Real.exp (-((t + s) / (2 * t * s)) * (y - s * x / (t + s)) ^ 2) :=
    funext (heatKernel_sub_mul_heatKernel_eq hs ht x)
  have hshift := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun z : ℝ => Real.exp (-((t + s) / (2 * t * s)) * z ^ 2)) (s * x / (t + s))
  rw [hfun, integral_const_mul, hshift, integral_gaussian]
  have hA : 0 ≤ 1 / (2 * Real.pi * t) := by positivity
  have hB : 0 ≤ 1 / (2 * Real.pi * s) := by positivity
  have hsq (a : ℝ) (ha : 0 < a) : 1 / Real.sqrt a = Real.sqrt (1 / a) := by
    rw [Real.sqrt_div' _ ha.le, Real.sqrt_one]
  have key : 1 / Real.sqrt (2 * Real.pi * t) * (1 / Real.sqrt (2 * Real.pi * s)) *
      Real.sqrt (Real.pi / ((t + s) / (2 * t * s))) =
        1 / Real.sqrt (2 * Real.pi * (t + s)) := by
    rw [hsq _ (by positivity), hsq _ (by positivity), hsq _ (by positivity),
      ← Real.sqrt_mul hA, ← Real.sqrt_mul (mul_nonneg hA hB)]
    congr 1
    have hts : t + s ≠ 0 := (add_pos ht hs).ne'
    field_simp
  unfold heatKernel
  calc _ = (1 / Real.sqrt (2 * Real.pi * t) * (1 / Real.sqrt (2 * Real.pi * s)) *
        Real.sqrt (Real.pi / ((t + s) / (2 * t * s)))) *
          Real.exp (-(1 / (2 * (t + s))) * x ^ 2) := by ring
    _ = _ := by rw [key]

/-- The semigroup identity through Mathlib's `convolution`, at a point. -/
theorem heatKernel_convolution_heatKernel_apply {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (x : ℝ) :
    convolution (heatKernel t) (heatKernel s) (ContinuousLinearMap.lsmul ℝ ℝ)
      (volume : Measure ℝ) x = heatKernel (t + s) x := by
  rw [convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hflip := integral_sub_left_eq_self (μ := (volume : Measure ℝ))
    (fun y => heatKernel t (x - y) * heatKernel s y) x
  simp only [sub_sub_cancel] at hflip
  rw [hflip]
  exact integral_heatKernel_mul_heatKernel hs ht x

/-- The semigroup identity `p_t ⋆ p_s = p_{t+s}` as an equality of functions. -/
theorem heatKernel_convolution_heatKernel {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    convolution (heatKernel t) (heatKernel s) (ContinuousLinearMap.lsmul ℝ ℝ)
      (volume : Measure ℝ) = heatKernel (t + s) :=
  funext (heatKernel_convolution_heatKernel_apply hs ht)

/-! ### Local positive-time Gaussian domination -/

theorem heatKernel_sq_exp {r : ℝ} (hr : 0<r) (z : ℝ) :
    heatKernel r z^2=(1/(2*Real.pi*r))*Real.exp (-z^2/r) := by
  unfold heatKernel
  rw [mul_pow,div_pow,Real.sq_sqrt (by positivity),←Real.exp_nat_mul]
  simp only [one_pow]
  congr 1
  congr 1
  push_cast
  field_simp

/-- Uniform early-time Gaussian domination, with explicit local output neighborhood. -/
theorem heatKernel_sq_le_local {t u s x z y : ℝ}
    (ht : 0<t) (hu0 : 3*t/4≤u) (hu1 : u≤5*t/4)
    (hs0 : 0≤s) (hs1 : s≤t/4) (hx : |x-z|≤1) :
    heatKernel (u-s) (x-y)^2 ≤
      (4*Real.exp (6/t))*heatKernel (2*t-s) (z-y)^2 := by
  have hr : 0<u-s := by linarith
  have hR : 0<2*t-s := by linarith
  have hd : (x-z)^2≤1 := by
    have h := abs_le.mp hx
    nlinarith [sq_nonneg (x-z)]
  have hgap : 4*(u-s)≤3*(2*t-s) := by linarith
  have hlow : t≤2*(u-s) := by linarith
  have hlarge : 2*t-s≤4*(u-s) := by linarith
  have hy : 3/4*(z-y)^2≤(x-y)^2+3*(x-z)^2 := by
    nlinarith [sq_nonneg ((z-y)/2+2*(x-z))]
  have hcross : (u-s)*(z-y)^2≤(2*t-s)*((x-y)^2+3) := by
    have hmul := mul_nonneg (show 0≤3*(2*t-s)-4*(u-s) by linarith) (sq_nonneg (z-y))
    have hy' : 3/4*(z-y)^2≤(x-y)^2+3 := by linarith
    have hh := mul_le_mul_of_nonneg_left hy' hR.le
    nlinarith
  have hfrac : (z-y)^2/(2*t-s)≤((x-y)^2+3)/(u-s) :=
    (div_le_div_iff₀ hR hr).mpr (by nlinarith [hcross])
  have hrem : (3:ℝ)/(u-s)≤6/t :=
    (div_le_div_iff₀ hr ht).mpr (by linarith)
  have hexp : -(x-y)^2/(u-s)≤6/t-(z-y)^2/(2*t-s) := by
    rw [add_div] at hfrac
    rw [neg_div]
    linarith
  have hpre : 1/(2*Real.pi*(u-s))≤4*(1/(2*Real.pi*(2*t-s))) := by
    have hh : (1:ℝ)/(2*Real.pi*(u-s))≤4/(2*Real.pi*(2*t-s)) :=
      (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by nlinarith [Real.pi_pos])
    simpa only [mul_one_div] using hh
  rw [heatKernel_sq_exp hr,heatKernel_sq_exp hR]
  calc _ ≤ (4*(1/(2*Real.pi*(2*t-s))))*Real.exp (6/t-(z-y)^2/(2*t-s)) :=
        mul_le_mul hpre (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by positivity)
       _ = _ := by rw [Real.exp_sub,neg_div,Real.exp_neg]; ring

theorem heatKernel_le_local {t u x z : ℝ} (ht : 0<t)
    (hu0 : 3*t/4≤u) (hu1 : u≤5*t/4) (hx : |x-z|≤1) (y : ℝ) :
    heatKernel u (x-y) ≤
      Real.sqrt (4*Real.exp (6/t))*heatKernel (2*t) (z-y) := by
  have hu : 0<u := by linarith
  have ht2 : 0<2*t := by linarith
  have hC : 0≤4*Real.exp (6/t) := by positivity
  apply (sq_le_sq₀ (heatKernel_pos hu _).le
    (mul_nonneg (Real.sqrt_nonneg _) (heatKernel_pos ht2 _).le)).mp
  calc
    heatKernel u (x-y)^2 ≤ (4*Real.exp (6/t))*heatKernel (2*t) (z-y)^2 := by
      simpa only [sub_zero] using heatKernel_sq_le_local
        (s:=0) ht hu0 hu1 (le_refl 0) (by linarith) hx (y:=y)
    _ = (Real.sqrt (4*Real.exp (6/t))*heatKernel (2*t) (z-y))^2 := by
      rw [mul_pow,Real.sq_sqrt hC]

theorem continuousAt_heatKernel_joint (a : ℝ × ℝ) (ha : 0<a.1) (y : ℝ) :
    ContinuousAt (fun z : ℝ × ℝ => heatKernel z.1 (z.2-y)) a := by
  unfold heatKernel
  fun_prop (disch:=positivity)


end RoughHeatKernel
