/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import RoughHeatKernel.Gaussian
import Mathlib.Probability.Moments.Variance

/-!
# `L¹` bounds for heat-kernel increments

For `t > 0` the heat kernel `p_t` is smooth in both variables, with

* `∂ₓ p_t(x) = -(x / t) p_t(x)` and `∂_t p_t(x) = (x² - t) / (2t²) p_t(x)`;
* `∫ x² p_t(x) dx = t` and `∫ |x| p_t(x) dx ≤ √t`.

From these, a fundamental-theorem-of-calculus and Tonelli argument
(`lintegral_enorm_sub_le_lintegral`) gives the sharp-order increment bounds

* `∫ |p_t(x - y) - p_t(z - y)| dy ≤ min 2 (|x - z| / √t)` (space);
* `∫ |p_{t+ε}(x - y) - p_t(x - y)| dy ≤ min 2 (ε / t)` for `ε ≥ 0` (time).

The constant `2` is the trivial bound `‖p_t‖₁ + ‖p_s‖₁`. The other constants are `1`,
coming from `‖∂ₓ p_t‖₁ ≤ t^{-1/2}` (the exact value is `(2/(πt))^{1/2}`) and
`‖∂_t p_t‖₁ ≤ t⁻¹`. These two derivative bounds are proved inside the increment proofs,
not stated as separate theorems.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace RoughHeatKernel

attribute [local fun_prop] continuous_heatKernel

/-! ### Derivatives -/

/-- The spatial derivative: `∂ₓ p_t(x) = -(x / t) p_t(x)`. -/
theorem hasDerivAt_heatKernel {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (heatKernel t) (-(x / t) * heatKernel t x) x := by
  have h := (((hasDerivAt_pow 2 x).const_mul (-(1 / (2 * t)))).exp).const_mul
    (1 / Real.sqrt (2 * Real.pi * t))
  show HasDerivAt (fun y => 1 / Real.sqrt (2 * Real.pi * t) *
    Real.exp (-(1 / (2 * t)) * y ^ 2)) _ x
  convert h using 1
  simp only [heatKernel]
  have : t ≠ 0 := ht.ne'
  field_simp
  ring

/-- The time derivative: `∂_t p_t(x) = (x² - t) / (2t²) p_t(x)`. -/
theorem hasDerivAt_heatKernel_time {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => heatKernel s x) ((x ^ 2 - t) / (2 * t ^ 2) * heatKernel t x) t := by
  have hpos : 0 < 2 * Real.pi * t := by positivity
  have hsq : 0 < Real.sqrt (2 * Real.pi * t) := Real.sqrt_pos.mpr hpos
  have h1 : HasDerivAt (fun s => Real.sqrt (2 * Real.pi * s))
      (2 * Real.pi * 1 / (2 * Real.sqrt (2 * Real.pi * t))) t :=
    ((hasDerivAt_id t).const_mul (2 * Real.pi)).sqrt hpos.ne'
  have h2 := (hasDerivAt_const t (1 : ℝ)).div h1 hsq.ne'
  have hinv := (hasDerivAt_const t (1 : ℝ)).div ((hasDerivAt_id t).const_mul 2)
    (by simp only [id]; positivity)
  have h3 := ((hinv.neg).mul_const (x ^ 2)).exp
  have h := h2.mul h3
  have h' : HasDerivAt (fun s => heatKernel s x) _ t :=
    h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by
      simp only [heatKernel, Pi.mul_apply, Pi.div_apply, Pi.neg_apply, id])
  convert h' using 1
  simp only [heatKernel, id, Pi.div_apply, Pi.neg_apply]
  have hs2 : Real.sqrt (2 * Real.pi * t) ^ 2 = 2 * Real.pi * t := Real.sq_sqrt hpos.le
  have : t ≠ 0 := ht.ne'
  rw [hs2]
  field_simp
  ring

/-! ### Gaussian moments -/

/-- `x ↦ x p_t(x)` is integrable for `t > 0`. -/
theorem integrable_mul_heatKernel {t : ℝ} (ht : 0 < t) :
    Integrable (fun x => x * heatKernel t x) := by
  have h := (integrable_mul_exp_neg_mul_sq (b := 1 / (2 * t)) (by positivity)).const_mul
    (1 / Real.sqrt (2 * Real.pi * t))
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [heatKernel]
  ring

/-- `x ↦ x² p_t(x)` is integrable for `t > 0`. -/
theorem integrable_sq_mul_heatKernel {t : ℝ} (ht : 0 < t) :
    Integrable (fun x => x ^ 2 * heatKernel t x) := by
  have h := (integrable_rpow_mul_exp_neg_mul_sq (b := 1 / (2 * t)) (by positivity)
    (s := 2) (by norm_num)).const_mul (1 / Real.sqrt (2 * Real.pi * t))
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [heatKernel, Real.rpow_two]
  ring

/-- The second moment: `∫ x² p_t(x) dx = t`. -/
theorem integral_sq_mul_heatKernel {t : ℝ} (ht : 0 < t) :
    ∫ x, x ^ 2 * heatKernel t x = t := by
  have hv : t.toNNReal ≠ 0 := by simpa using ht
  have hvar := variance_fun_id_gaussianReal (μ := 0) (v := t.toNNReal)
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal,
    integral_gaussianReal_eq_integral_heatKernel hv] at hvar
  simp only [Real.coe_toNNReal _ ht.le, zero_sub, heatKernel_neg, sub_zero] at hvar
  calc ∫ x, x ^ 2 * heatKernel t x = ∫ y, heatKernel t y * y ^ 2 := by
        congr 1; ext x; ring
    _ = t := hvar

/-- The first absolute moment: `∫ |x| p_t(x) dx ≤ √t`. -/
theorem integral_abs_mul_heatKernel_le {t : ℝ} (ht : 0 < t) :
    ∫ x, |x| * heatKernel t x ≤ Real.sqrt t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hhalf : t / (2 * Real.sqrt t) = Real.sqrt t / 2 := by
    rw [div_eq_div_iff (by positivity) (by norm_num)]; nlinarith
  have key : ∀ x, |x| * heatKernel t x ≤
      1 / (2 * Real.sqrt t) * (x ^ 2 * heatKernel t x) + Real.sqrt t / 2 * heatKernel t x := by
    intro x
    have hp := (heatKernel_pos ht x).le
    have hx : |x| * (2 * Real.sqrt t) ≤ x ^ 2 + t := by
      nlinarith [sq_nonneg (|x| - Real.sqrt t), sq_abs x]
    have : |x| ≤ (x ^ 2 + t) / (2 * Real.sqrt t) := by
      rw [le_div_iff₀ (by positivity)]; exact hx
    calc |x| * heatKernel t x ≤ (x ^ 2 + t) / (2 * Real.sqrt t) * heatKernel t x :=
          mul_le_mul_of_nonneg_right this hp
      _ = 1 / (2 * Real.sqrt t) * (x ^ 2 * heatKernel t x) +
          Real.sqrt t / 2 * heatKernel t x := by
        rw [add_div, add_mul, hhalf]; ring
  have hR : Integrable (fun x => 1 / (2 * Real.sqrt t) * (x ^ 2 * heatKernel t x) +
      Real.sqrt t / 2 * heatKernel t x) :=
    ((integrable_sq_mul_heatKernel ht).const_mul _).add
      ((integrable_heatKernel ht).const_mul _)
  have hL : Integrable (fun x => |x| * heatKernel t x) := by
    refine hR.mono' ((continuous_abs.mul (continuous_heatKernel t)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg x) (heatKernel_pos ht x).le)]
    exact key x
  calc ∫ x, |x| * heatKernel t x
      ≤ ∫ x, (1 / (2 * Real.sqrt t) * (x ^ 2 * heatKernel t x) +
          Real.sqrt t / 2 * heatKernel t x) := integral_mono hL hR key
    _ = 1 / (2 * Real.sqrt t) * t + Real.sqrt t / 2 * 1 := by
        rw [integral_add ((integrable_sq_mul_heatKernel ht).const_mul _)
          ((integrable_heatKernel ht).const_mul _), integral_const_mul, integral_const_mul,
          integral_sq_mul_heatKernel ht, integral_heatKernel ht]
    _ = t / (2 * Real.sqrt t) + Real.sqrt t / 2 := by ring
    _ = Real.sqrt t := by rw [hhalf]; ring

/-! ### An `L¹` mean-value inequality -/

/-- If `θ ↦ F θ y` has derivative `F' θ y` on `[a, b]` for every `y`, then
`∫ |F b y - F a y| dy ≤ ∫_a^b ∫ |F' θ y| dy dθ` (as lower Lebesgue integrals). -/
theorem lintegral_enorm_sub_le_lintegral {F F' : ℝ → ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ y, ∀ θ ∈ Icc a b, HasDerivAt (fun θ => F θ y) (F' θ y) θ)
    (hF'c : ∀ y, ContinuousOn (fun θ => F' θ y) (Icc a b))
    (hF'm : Measurable (Function.uncurry F')) :
    ∫⁻ y, ‖F b y - F a y‖ₑ ≤ ∫⁻ θ in Ioc a b, ∫⁻ y, ‖F' θ y‖ₑ := by
  have hpt : ∀ y, ‖F b y - F a y‖ₑ ≤ ∫⁻ θ in Ioc a b, ‖F' θ y‖ₑ := by
    intro y
    have hint : IntervalIntegrable (fun θ => F' θ y) volume a b :=
      (hF'c y).intervalIntegrable_of_Icc hab
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun θ hθ => hF y θ (by rwa [uIcc_of_le hab] at hθ)) hint,
      intervalIntegral.integral_of_le hab]
    exact enorm_integral_le_lintegral_enorm _
  calc ∫⁻ y, ‖F b y - F a y‖ₑ ≤ ∫⁻ y, ∫⁻ θ in Ioc a b, ‖F' θ y‖ₑ := lintegral_mono hpt
    _ = ∫⁻ θ in Ioc a b, ∫⁻ y, ‖F' θ y‖ₑ := by
      rw [lintegral_lintegral_swap]
      exact ((hF'm.comp measurable_swap).enorm).aemeasurable

/-! ### Spatial increments -/

private theorem lintegral_ofReal_abs_mul_heatKernel_le {t : ℝ} (ht : 0 < t) :
    ∫⁻ u, ENNReal.ofReal (|u| * heatKernel t u) ≤ ENNReal.ofReal (Real.sqrt t) := by
  have hL : Integrable (fun u => |u| * heatKernel t u) := by
    refine (integrable_mul_heatKernel ht).abs.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [abs_mul, abs_of_pos (heatKernel_pos ht u)]
  rw [← ofReal_integral_eq_lintegral_ofReal hL
    (Filter.Eventually.of_forall fun u => mul_nonneg (abs_nonneg u) (heatKernel_pos ht u).le)]
  exact ENNReal.ofReal_le_ofReal (integral_abs_mul_heatKernel_le ht)

/-- `∫ |p_t(y - h) - p_t(y)| dy ≤ |h| / √t`, as a lower Lebesgue integral. -/
theorem lintegral_enorm_heatKernel_sub_shift_le {t : ℝ} (ht : 0 < t) (h : ℝ) :
    ∫⁻ y, ‖heatKernel t (y - h) - heatKernel t y‖ₑ ≤ ENNReal.ofReal (|h| / Real.sqrt t) := by
  set F : ℝ → ℝ → ℝ := fun θ y => heatKernel t (y - θ * h) with hFdef
  set F' : ℝ → ℝ → ℝ := fun θ y =>
    -((y - θ * h) / t) * heatKernel t (y - θ * h) * -(1 * h) with hF'def
  have hF : ∀ y, ∀ θ ∈ Icc (0 : ℝ) 1, HasDerivAt (fun θ => F θ y) (F' θ y) θ := by
    intro y θ _
    have := (hasDerivAt_heatKernel ht (y - θ * h)).comp θ
      (((hasDerivAt_id θ).mul_const h).const_sub y)
    exact this
  have hcont : Continuous (Function.uncurry F') := by
    simp only [hF'def]
    fun_prop
  have hstep := lintegral_enorm_sub_le_lintegral zero_le_one hF
    (fun y => (hcont.comp (continuous_id.prodMk continuous_const)).continuousOn)
    hcont.measurable
  simp only [hFdef, one_mul, zero_mul, sub_zero] at hstep
  have hinner : ∀ θ, ∫⁻ y, ‖F' θ y‖ₑ ≤ ENNReal.ofReal (|h| / t) * ENNReal.ofReal (Real.sqrt t) := by
    intro θ
    have e : ∀ y, ‖F' θ y‖ₑ =
        ENNReal.ofReal (|h| / t) * ENNReal.ofReal (|y - θ * h| * heatKernel t (y - θ * h)) := by
      intro y
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      simp only [hF'def]
      rw [show -((y - θ * h) / t) * heatKernel t (y - θ * h) * -(1 * h) =
          (h / t) * ((y - θ * h) * heatKernel t (y - θ * h)) by ring,
        abs_mul, abs_mul, abs_div, abs_of_pos ht, abs_of_pos (heatKernel_pos ht _)]
    simp_rw [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_sub_right_eq_self (μ := (volume : Measure ℝ))
        (fun u => ENNReal.ofReal (|u| * heatKernel t u)) (θ * h)]
    gcongr
    exact lintegral_ofReal_abs_mul_heatKernel_le ht
  calc ∫⁻ y, ‖heatKernel t (y - h) - heatKernel t y‖ₑ
      ≤ ∫⁻ θ in Ioc (0 : ℝ) 1, ∫⁻ y, ‖F' θ y‖ₑ := hstep
    _ ≤ ∫⁻ θ in Ioc (0 : ℝ) 1, ENNReal.ofReal (|h| / t) * ENNReal.ofReal (Real.sqrt t) :=
        lintegral_mono fun θ => hinner θ
    _ = ENNReal.ofReal (|h| / Real.sqrt t) := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
        have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
        rw [div_mul_eq_mul_div, div_eq_div_iff ht.ne' hs.ne', mul_assoc, hss]

/-! ### Time increments -/

private theorem lintegral_enorm_heatKernel_time_deriv_le {s : ℝ} (hs : 0 < s) :
    ∫⁻ y, ‖(y ^ 2 - s) / (2 * s ^ 2) * heatKernel s y‖ₑ ≤ ENNReal.ofReal (1 / s) := by
  have hG : Integrable (fun y => 1 / (2 * s ^ 2) * (y ^ 2 * heatKernel s y) +
      1 / (2 * s) * heatKernel s y) :=
    ((integrable_sq_mul_heatKernel hs).const_mul _).add ((integrable_heatKernel hs).const_mul _)
  have hG0 : ∀ y, 0 ≤ 1 / (2 * s ^ 2) * (y ^ 2 * heatKernel s y) +
      1 / (2 * s) * heatKernel s y := fun y => by
    have := (heatKernel_pos hs y).le
    positivity
  calc ∫⁻ y, ‖(y ^ 2 - s) / (2 * s ^ 2) * heatKernel s y‖ₑ
      ≤ ∫⁻ y, ENNReal.ofReal (1 / (2 * s ^ 2) * (y ^ 2 * heatKernel s y) +
          1 / (2 * s) * heatKernel s y) := by
        refine lintegral_mono fun y => ?_
        rw [Real.enorm_eq_ofReal_abs]
        refine ENNReal.ofReal_le_ofReal ?_
        have hp := heatKernel_pos hs y
        rw [abs_mul, abs_div, abs_of_pos hp, abs_of_pos (by positivity : (0 : ℝ) < 2 * s ^ 2)]
        have hab : |y ^ 2 - s| ≤ y ^ 2 + s := by
          rw [abs_le]; constructor <;> nlinarith [sq_nonneg y]
        calc |y ^ 2 - s| / (2 * s ^ 2) * heatKernel s y
            ≤ (y ^ 2 + s) / (2 * s ^ 2) * heatKernel s y := by gcongr
          _ = _ := by field_simp
    _ = ENNReal.ofReal (1 / s) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hG (Filter.Eventually.of_forall hG0),
          integral_add ((integrable_sq_mul_heatKernel hs).const_mul _)
            ((integrable_heatKernel hs).const_mul _), integral_const_mul, integral_const_mul,
          integral_sq_mul_heatKernel hs, integral_heatKernel hs]
        congr 1
        field_simp
        ring

/-- `∫ |p_{t+ε}(y) - p_t(y)| dy ≤ ε / t` for `t > 0`, `ε ≥ 0`, as a lower Lebesgue
integral. -/
theorem lintegral_enorm_heatKernel_add_sub_le {t ε : ℝ} (ht : 0 < t) (hε : 0 ≤ ε) :
    ∫⁻ y, ‖heatKernel (t + ε) y - heatKernel t y‖ₑ ≤ ENNReal.ofReal (ε / t) := by
  set F' : ℝ → ℝ → ℝ := fun s y => (y ^ 2 - s) / (2 * s ^ 2) * heatKernel s y with hF'def
  have hpos : ∀ s ∈ Icc t (t + ε), 0 < s := fun s hs => lt_of_lt_of_le ht hs.1
  have hF : ∀ y, ∀ s ∈ Icc t (t + ε), HasDerivAt (fun s => heatKernel s y) (F' s y) s :=
    fun y s hs => hasDerivAt_heatKernel_time (hpos s hs) y
  have hF'c : ∀ y, ContinuousOn (fun s => F' s y) (Icc t (t + ε)) := by
    intro y s hs
    have hs0 := hpos s hs
    refine ContinuousAt.continuousWithinAt ?_
    exact ((continuousAt_const.sub continuousAt_id).div
      (continuousAt_const.mul (continuousAt_id.pow 2)) (mul_ne_zero two_ne_zero (pow_ne_zero 2 hs0.ne'))).mul
      (hasDerivAt_heatKernel_time hs0 y).continuousAt
  have hF'm : Measurable (Function.uncurry F') := by
    simp only [hF'def, heatKernel]
    fun_prop
  have hstep := lintegral_enorm_sub_le_lintegral (le_add_of_nonneg_right hε) hF hF'c hF'm
  calc ∫⁻ y, ‖heatKernel (t + ε) y - heatKernel t y‖ₑ
      ≤ ∫⁻ s in Ioc t (t + ε), ∫⁻ y, ‖F' s y‖ₑ := hstep
    _ ≤ ∫⁻ s in Ioc t (t + ε), ENNReal.ofReal (1 / t) := by
        refine setLIntegral_mono measurable_const fun s hs => ?_
        have hs0 : 0 < s := lt_trans ht hs.1
        refine (lintegral_enorm_heatKernel_time_deriv_le hs0).trans ?_
        exact ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le ht hs.1.le)
    _ = ENNReal.ofReal (ε / t) := by
        rw [setLIntegral_const, Real.volume_Ioc, add_sub_cancel_left,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-! ### Bochner-integral forms -/

private theorem integral_abs_le_of_lintegral {f : ℝ → ℝ} (hf : Integrable f) {c : ℝ}
    (hc : 0 ≤ c) (h : ∫⁻ y, ‖f y‖ₑ ≤ ENNReal.ofReal c) : ∫ y, |f y| ≤ c := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    hf.abs.aestronglyMeasurable]
  apply ENNReal.toReal_le_of_le_ofReal hc
  simpa only [Real.enorm_eq_ofReal_abs] using h

private theorem integral_abs_sub_le_two {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    (hf0 : ∀ y, 0 ≤ f y) (hg0 : ∀ y, 0 ≤ g y) (hf1 : ∫ y, f y = 1) (hg1 : ∫ y, g y = 1) :
    ∫ y, |f y - g y| ≤ 2 := by
  calc ∫ y, |f y - g y| ≤ ∫ y, (f y + g y) :=
        integral_mono (hf.sub hg).abs (hf.add hg) fun y =>
          abs_sub_le_iff.mpr ⟨by linarith [hg0 y], by linarith [hf0 y]⟩
    _ = 2 := by rw [integral_add hf hg, hf1, hg1]; norm_num

/-- Spatial increment: `∫ |p_t(y - h) - p_t(y)| dy ≤ min 2 (|h| / √t)` for `t > 0`. -/
theorem integral_abs_heatKernel_sub_shift_le {t : ℝ} (ht : 0 < t) (h : ℝ) :
    ∫ y, |heatKernel t (y - h) - heatKernel t y| ≤ min 2 (|h| / Real.sqrt t) := by
  have hi : Integrable (fun y => heatKernel t (y - h)) := (integrable_heatKernel ht).comp_sub_right h
  refine le_min ?_ ?_
  · refine integral_abs_sub_le_two hi (integrable_heatKernel ht)
      (fun y => (heatKernel_pos ht _).le) (fun y => (heatKernel_pos ht _).le) ?_
      (integral_heatKernel ht)
    rw [integral_sub_right_eq_self (μ := (volume : Measure ℝ)) (heatKernel t) h,
      integral_heatKernel ht]
  · exact integral_abs_le_of_lintegral (hi.sub (integrable_heatKernel ht)) (by positivity)
      (lintegral_enorm_heatKernel_sub_shift_le ht h)

/-- Spatial increment in convolution form:
`∫ |p_t(x - y) - p_t(z - y)| dy ≤ min 2 (|x - z| / √t)` for `t > 0`. -/
theorem integral_abs_heatKernel_sub_sub_le {t : ℝ} (ht : 0 < t) (x z : ℝ) :
    ∫ y, |heatKernel t (x - y) - heatKernel t (z - y)| ≤ min 2 (|x - z| / Real.sqrt t) := by
  have e : ∀ y, |heatKernel t (x - y) - heatKernel t (z - y)| =
      (fun u => |heatKernel t (u - (x - z)) - heatKernel t u|) (y - z) := by
    intro y
    simp only
    rw [← heatKernel_neg t (x - y), ← heatKernel_neg t (z - y)]
    congr 3 <;> ring
  simp_rw [e]
  rw [integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun u => |heatKernel t (u - (x - z)) - heatKernel t u|) z]
  exact integral_abs_heatKernel_sub_shift_le ht (x - z)

/-- Time increment in convolution form:
`∫ |p_{t+ε}(x - y) - p_t(x - y)| dy ≤ min 2 (ε / t)` for `t > 0` and `ε ≥ 0`. -/
theorem integral_abs_heatKernel_add_sub_le {t ε : ℝ} (ht : 0 < t) (hε : 0 ≤ ε) (x : ℝ) :
    ∫ y, |heatKernel (t + ε) (x - y) - heatKernel t (x - y)| ≤ min 2 (ε / t) := by
  have htε : 0 < t + ε := by linarith
  rw [integral_sub_left_eq_self (μ := (volume : Measure ℝ))
    (fun u => |heatKernel (t + ε) u - heatKernel t u|) x]
  refine le_min ?_ ?_
  · exact integral_abs_sub_le_two (integrable_heatKernel htε) (integrable_heatKernel ht)
      (fun y => (heatKernel_pos htε _).le) (fun y => (heatKernel_pos ht _).le)
      (integral_heatKernel htε) (integral_heatKernel ht)
  · exact integral_abs_le_of_lintegral
      ((integrable_heatKernel htε).sub (integrable_heatKernel ht)) (by positivity)
      (lintegral_enorm_heatKernel_add_sub_le ht hε)

end RoughHeatKernel
