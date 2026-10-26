/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
module

public import Challenge.Reference.RoughHeatKernel.Kernel

@[expose] public section

/-!
# Heat flow of Gaussian-tempered measures

A positive measure `ν` on `ℝ` is *Gaussian-tempered* if `∫ e^{-a x²} ν(dx) < ∞` for every
`a > 0`. Such measures may have infinite total mass (Lebesgue measure, `e^{a|x|} dx`, …).
For them the heat flow `heatFlow ν t x = ∫ p_t(x - y) ν(dy)` is given by an absolutely
convergent integral, and this file proves, for `t > 0`:

* integrability of `y ↦ p_t(x - y)` against `ν`, and continuity of `x ↦ heatFlow ν t x`;
* the Gaussian growth bound `heatFlow ν t x ≤ (2πt)^{-1/2} M_λ e^{κ x²}`;
* the weighted bound: `x ↦ e^{-a x²} (heatFlow ν t x)^p` is integrable for `a > 0`, `p ≥ 1`;
* the local bound: for `T > 0` and `R`, `√s · heatFlow ν s y` is bounded uniformly in
  `s ∈ (0, T]` and `|y| ≤ R`.

The extended-real flow `lheatFlow` is defined for every measure; for a Gaussian-tempered
measure it is finite and equals `ENNReal.ofReal (heatFlow ν t x)`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace RoughHeatKernel

/-- `ν` is Gaussian-tempered: `∫ e^{-a x²} ν(dx) < ∞` for every `a > 0`. -/
def IsGaussianTempered (ν : Measure ℝ) : Prop :=
  ∀ a : ℝ, 0 < a → ∫⁻ x, ENNReal.ofReal (Real.exp (-a * x ^ 2)) ∂ν < ⊤

/-- The heat flow `∫ p_t(x - y) ν(dy)` of a positive measure. -/
noncomputable def heatFlow (ν : Measure ℝ) (t x : ℝ) : ℝ :=
  ∫ y, heatKernel t (x - y) ∂ν

/-- The extended-real heat flow `∫⁻ p_t(x - y) ν(dy)`, defined for every measure. -/
noncomputable def lheatFlow (ν : Measure ℝ) (t x : ℝ) : ENNReal :=
  ∫⁻ y, ENNReal.ofReal (heatKernel t (x - y)) ∂ν

/-! ### The class -/

namespace IsGaussianTempered

variable {ν ν' : Measure ℝ}

theorem integrable_exp_neg_mul_sq (hν : IsGaussianTempered ν) {a : ℝ} (ha : 0 < a) :
    Integrable (fun y : ℝ => Real.exp (-a * y ^ 2)) ν := by
  refine ⟨(by fun_prop : Continuous fun y : ℝ => Real.exp (-a * y ^ 2)).aestronglyMeasurable,
    ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => (Real.exp_pos _).le)]
  exact hν a ha

theorem add (hν : IsGaussianTempered ν) (hν' : IsGaussianTempered ν') :
    IsGaussianTempered (ν + ν') := fun a ha => by
  rw [lintegral_add_measure]
  exact ENNReal.add_lt_top.mpr ⟨hν a ha, hν' a ha⟩

theorem mono (hν : IsGaussianTempered ν) (h : ν' ≤ ν) : IsGaussianTempered ν' :=
  fun a ha => lt_of_le_of_lt (lintegral_mono' h le_rfl) (hν a ha)

end IsGaussianTempered

theorem isGaussianTempered_of_isFiniteMeasure (ν : Measure ℝ) [IsFiniteMeasure ν] :
    IsGaussianTempered ν := fun a _ => by
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (-a * x ^ 2)) ∂ν
      ≤ ∫⁻ _, 1 ∂ν := by
        apply lintegral_mono
        intro x
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        rw [Real.exp_le_one_iff]
        nlinarith [sq_nonneg x]
    _ = ν Set.univ := by rw [lintegral_one]
    _ < ⊤ := measure_lt_top _ _

theorem isGaussianTempered_dirac (x₀ : ℝ) : IsGaussianTempered (Measure.dirac x₀) :=
  isGaussianTempered_of_isFiniteMeasure _

/-- Lebesgue measure is Gaussian-tempered, although its total mass is infinite. -/
theorem isGaussianTempered_volume : IsGaussianTempered (volume : Measure ℝ) := fun a ha => by
  rw [← hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => (Real.exp_pos _).le)]
  exact (integrable_exp_neg_mul_sq ha).hasFiniteIntegral

/-! ### Well-definedness and continuity -/

/-- From `-(x-y)² ≤ -y²/2 + x²`: `p_t(x - y) ≤ (2πt)^{-1/2} e^{x²/(2t)} e^{-y²/(4t)}`. -/
private theorem heatKernel_sub_le_gaussian {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    heatKernel t (x - y) ≤
      1 / Real.sqrt (2 * Real.pi * t) * Real.exp (x ^ 2 / (2 * t)) *
        Real.exp (-(1 / (4 * t)) * y ^ 2) := by
  unfold heatKernel
  have hc : 0 ≤ 1 / Real.sqrt (2 * Real.pi * t) := by positivity
  have hexp : Real.exp (-(1 / (2 * t)) * (x - y) ^ 2) ≤
      Real.exp (x ^ 2 / (2 * t)) * Real.exp (-(1 / (4 * t)) * y ^ 2) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have key : -(1 / (2 * t)) * (x - y) ^ 2 - (x ^ 2 / (2 * t) + -(1 / (4 * t)) * y ^ 2) =
        -((2 * x - y) ^ 2) / (4 * t) := by
      field_simp
      ring
    have hneg : -((2 * x - y) ^ 2) / (4 * t) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
    linarith
  calc 1 / Real.sqrt (2 * Real.pi * t) * Real.exp (-(1 / (2 * t)) * (x - y) ^ 2)
      ≤ 1 / Real.sqrt (2 * Real.pi * t) *
          (Real.exp (x ^ 2 / (2 * t)) * Real.exp (-(1 / (4 * t)) * y ^ 2)) :=
        mul_le_mul_of_nonneg_left hexp hc
    _ = _ := by ring

private theorem heatKernel_sub_le_gaussian_of_abs_le {t R x : ℝ} (ht : 0 < t)
    (hx : |x| ≤ R) (y : ℝ) :
    heatKernel t (x - y) ≤
      1 / Real.sqrt (2 * Real.pi * t) * Real.exp (R ^ 2 / (2 * t)) *
        Real.exp (-(1 / (4 * t)) * y ^ 2) := by
  refine (heatKernel_sub_le_gaussian ht x y).trans ?_
  have hc : 0 ≤ 1 / Real.sqrt (2 * Real.pi * t) := by positivity
  have hx2 : x ^ 2 ≤ R ^ 2 := sq_le_sq' (neg_le_of_abs_le hx) (le_of_abs_le hx)
  gcongr

/-- `y ↦ p_t(x - y)` is integrable against a Gaussian-tempered measure. -/
theorem IsGaussianTempered.integrable_heatKernel_sub {ν : Measure ℝ}
    (hν : IsGaussianTempered ν) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable (fun y => heatKernel t (x - y)) ν := by
  have hg := (hν.integrable_exp_neg_mul_sq (a := 1 / (4 * t)) (by positivity)).const_mul
    (1 / Real.sqrt (2 * Real.pi * t) * Real.exp (x ^ 2 / (2 * t)))
  refine hg.mono' ((continuous_heatKernel t).comp
    (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (heatKernel_pos ht _)]
  exact heatKernel_sub_le_gaussian ht x y

theorem heatFlow_nonneg (ν : Measure ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 ≤ heatFlow ν t x :=
  integral_nonneg fun _ => (heatKernel_pos ht _).le

/-- `x ↦ heatFlow ν t x` is continuous for a Gaussian-tempered `ν` and `t > 0`. -/
theorem continuous_heatFlow {ν : Measure ℝ} (hν : IsGaussianTempered ν) {t : ℝ}
    (ht : 0 < t) : Continuous (heatFlow ν t) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  set R := |x₀| + 1
  have hcont : Continuous fun p : ℝ × ℝ => heatKernel t (p.1 - p.2) :=
    (continuous_heatKernel t).comp (continuous_fst.sub continuous_snd)
  refine continuousAt_of_dominated (bound := fun y =>
      1 / Real.sqrt (2 * Real.pi * t) * Real.exp (R ^ 2 / (2 * t)) *
        Real.exp (-(1 / (4 * t)) * y ^ 2)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun x =>
      ((continuous_heatKernel t).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · have hnear : ∀ᶠ x in 𝓝 x₀, |x| ≤ R := by
      have := Metric.ball_mem_nhds x₀ (zero_lt_one : (0 : ℝ) < 1)
      filter_upwards [this] with x hx
      have hd : |x - x₀| < 1 := by simpa [Real.dist_eq] using hx
      have := abs_sub_abs_le_abs_sub x x₀
      simp only [R]
      linarith
    filter_upwards [hnear] with x hx
    exact Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (heatKernel_pos ht _)]
      exact heatKernel_sub_le_gaussian_of_abs_le ht hx y
  · exact (hν.integrable_exp_neg_mul_sq (a := 1 / (4 * t)) (by positivity)).const_mul _
  · exact Eventually.of_forall fun y =>
      (hcont.comp (continuous_id.prodMk continuous_const)).continuousAt

/-- Joint continuity of the heat flow at every strictly positive time. No finite-mass assumption. -/
theorem continuousAt_heatFlow_joint {ν : Measure ℝ}
    (hν : IsGaussianTempered ν) (a : ℝ × ℝ) (ha : 0<a.1) :
    ContinuousAt (fun z : ℝ × ℝ => RoughHeatKernel.heatFlow ν z.1 z.2) a := by
  refine continuousAt_of_dominated (bound:=fun y =>
      Real.sqrt (4*Real.exp (6/a.1))*heatKernel (2*a.1) (a.2-y)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun z => ((continuous_heatKernel z.1).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  · have htnear : ∀ᶠ z : ℝ × ℝ in 𝓝 a, z.1∈Set.Ioo (3*a.1/4) (5*a.1/4) :=
      continuous_fst.continuousAt.eventually (Ioo_mem_nhds (by linarith) (by linarith))
    have hxnear : ∀ᶠ z : ℝ × ℝ in 𝓝 a, z.2∈Set.Ioo (a.2-1) (a.2+1) :=
      continuous_snd.continuousAt.eventually (Ioo_mem_nhds (by linarith) (by linarith))
    filter_upwards [htnear,hxnear] with z hz hx
    exact Eventually.of_forall fun y => by
      have hu : 0<z.1 := by linarith [hz.1]
      rw [Real.norm_eq_abs,abs_of_pos (heatKernel_pos hu _)]
      apply heatKernel_le_local ha hz.1.le hz.2.le
      exact abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
  · exact (hν.integrable_heatKernel_sub (by linarith : 0<2*a.1) a.2).const_mul _
  · exact Eventually.of_forall fun y => continuousAt_heatKernel_joint a ha y


/-- For a Gaussian-tempered `ν`, the extended-real flow is the real flow. -/
theorem ofReal_heatFlow {ν : Measure ℝ} (hν : IsGaussianTempered ν) {t : ℝ} (ht : 0 < t)
    (x : ℝ) : ENNReal.ofReal (heatFlow ν t x) = lheatFlow ν t x :=
  ofReal_integral_eq_lintegral_ofReal (hν.integrable_heatKernel_sub ht x)
    (Eventually.of_forall fun _ => (heatKernel_pos ht _).le)

theorem lheatFlow_lt_top {ν : Measure ℝ} (hν : IsGaussianTempered ν) {t : ℝ} (ht : 0 < t)
    (x : ℝ) : lheatFlow ν t x < ⊤ := by
  rw [← ofReal_heatFlow hν ht x]
  exact ENNReal.ofReal_lt_top

/-- For every measure and every real `t`, the extended-real flow is the prefactor
`(2πt)^{-1/2}` times the lower integral of the Gaussian weight `exp(-(x-y)²/(2t))`. -/
theorem lheatFlow_eq_ofReal_mul_lintegral (ν : Measure ℝ) (t x : ℝ) :
    lheatFlow ν t x =
      ENNReal.ofReal (1 / Real.sqrt (2 * Real.pi * t)) *
        ∫⁻ y, ENNReal.ofReal (Real.exp (-(x - y) ^ 2 / (2 * t))) ∂ν := by
  have hc : 0 ≤ 1 / Real.sqrt (2 * Real.pi * t) := one_div_nonneg.mpr (Real.sqrt_nonneg _)
  unfold lheatFlow heatKernel
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun y => ?_
  rw [← ENNReal.ofReal_mul hc]
  congr 3
  ring

theorem toReal_lheatFlow {ν : Measure ℝ} (hν : IsGaussianTempered ν) {t : ℝ} (ht : 0 < t)
    (x : ℝ) : (lheatFlow ν t x).toReal = heatFlow ν t x := by
  rw [← ofReal_heatFlow hν ht x, ENNReal.toReal_ofReal (heatFlow_nonneg ν ht x)]

/-- For a Gaussian-tempered `ν` and `t > 0`, `x ↦ (lheatFlow ν t x).toReal` is continuous. -/
theorem continuous_toReal_lheatFlow {ν : Measure ℝ} (hν : IsGaussianTempered ν) {t : ℝ}
    (ht : 0 < t) : Continuous fun x => (lheatFlow ν t x).toReal := by
  have hfun : (fun x => (lheatFlow ν t x).toReal) = heatFlow ν t :=
    funext (toReal_lheatFlow hν ht)
  rw [hfun]
  exact continuous_heatFlow hν ht

/-! ### Gaussian growth and the weighted bound -/

/-- The completed square: with `κ = λ/(1-2λt)`,
`p_t(x - z) ≤ (2πt)^{-1/2} e^{κ x²} e^{-λ z²}` whenever `2λt < 1`. -/
theorem heatKernel_sub_le_exp_mul_exp {t l : ℝ} (ht : 0 < t) (hlt : 2 * l * t < 1)
    (x z : ℝ) :
    heatKernel t (x - z) ≤
      1 / Real.sqrt (2 * Real.pi * t) * Real.exp (l / (1 - 2 * l * t) * x ^ 2) *
        Real.exp (-l * z ^ 2) := by
  unfold heatKernel
  have hc : 0 ≤ 1 / Real.sqrt (2 * Real.pi * t) := by positivity
  have hd : 0 < 1 - 2 * l * t := by linarith
  have hA : 0 ≤ 1 / (2 * t) - l := by
    rw [sub_nonneg, le_div_iff₀ (by positivity)]
    linarith
  have hd' : 1 - 2 * l * t ≠ 0 := hd.ne'
  have ht' : t ≠ 0 := ht.ne'
  have key : -(1 / (2 * t)) * (x - z) ^ 2 =
      l / (1 - 2 * l * t) * x ^ 2 - (1 / (2 * t) - l) * (z - x / (1 - 2 * l * t)) ^ 2
        - l * z ^ 2 := by
    obtain ⟨w, rfl⟩ : ∃ w, x = w * (1 - 2 * l * t) :=
      ⟨x / (1 - 2 * l * t), (div_mul_cancel₀ x hd').symm⟩
    rw [mul_div_cancel_right₀ w hd']
    have hκx : l / (1 - 2 * l * t) * (w * (1 - 2 * l * t)) ^ 2 =
        l * w ^ 2 * (1 - 2 * l * t) := by
      rw [div_mul_eq_mul_div, div_eq_iff hd']
      ring
    rw [hκx]
    field_simp
    ring
  have hexp : Real.exp (-(1 / (2 * t)) * (x - z) ^ 2) ≤
      Real.exp (l / (1 - 2 * l * t) * x ^ 2) * Real.exp (-l * z ^ 2) := by
    rw [← Real.exp_add, Real.exp_le_exp, key]
    nlinarith [mul_nonneg hA (sq_nonneg (z - x / (1 - 2 * l * t)))]
  calc 1 / Real.sqrt (2 * Real.pi * t) * Real.exp (-(1 / (2 * t)) * (x - z) ^ 2)
      ≤ 1 / Real.sqrt (2 * Real.pi * t) *
          (Real.exp (l / (1 - 2 * l * t) * x ^ 2) * Real.exp (-l * z ^ 2)) :=
        mul_le_mul_of_nonneg_left hexp hc
    _ = _ := by ring

/-- `heatFlow ν t x ≤ (2πt)^{-1/2} M_λ e^{κ x²}`, `M_λ = ∫ e^{-λ z²} ν(dz)`, `κ = λ/(1-2λt)`. -/
theorem heatFlow_le_gaussian_growth {ν : Measure ℝ} (hν : IsGaussianTempered ν) {t l : ℝ}
    (ht : 0 < t) (hl : 0 < l) (hlt : 2 * l * t < 1) (x : ℝ) :
    heatFlow ν t x ≤
      1 / Real.sqrt (2 * Real.pi * t) * Real.exp (l / (1 - 2 * l * t) * x ^ 2) *
        ∫ z, Real.exp (-l * z ^ 2) ∂ν := by
  unfold heatFlow
  rw [← integral_const_mul]
  exact integral_mono (hν.integrable_heatKernel_sub ht x)
    ((hν.integrable_exp_neg_mul_sq hl).const_mul _)
    fun z => heatKernel_sub_le_exp_mul_exp ht hlt x z

/-- For `a, t > 0` and `p ≥ 1`, `x ↦ e^{-a x²} (heatFlow ν t x)^p` is integrable on `ℝ`. -/
theorem integrable_exp_mul_heatFlow_rpow {ν : Measure ℝ} (hν : IsGaussianTempered ν)
    {a t p : ℝ} (ha : 0 < a) (ht : 0 < t) (hp : 1 ≤ p) :
    Integrable (fun x => Real.exp (-a * x ^ 2) * (heatFlow ν t x) ^ p) := by
  have hp0 : 0 < p := by linarith
  set l := min (1 / (4 * t)) (a / (4 * p)) with hl_def
  have hl : 0 < l := lt_min (by positivity) (by positivity)
  have hl1 : l ≤ 1 / (4 * t) := min_le_left _ _
  have hl2 : l ≤ a / (4 * p) := min_le_right _ _
  have hlt4 : 4 * l * t ≤ 1 := by
    have := (le_div_iff₀ (by positivity : (0:ℝ) < 4 * t)).mp hl1
    linarith
  have hlt : 2 * l * t < 1 := by nlinarith
  have hd : 0 < 1 - 2 * l * t := by linarith
  set κ := l / (1 - 2 * l * t) with hκ_def
  have hκ : κ ≤ 2 * l := by
    rw [hκ_def, div_le_iff₀ hd]
    nlinarith
  have hpl : p * l ≤ a / 4 := by
    have := (le_div_iff₀ (by positivity : (0:ℝ) < 4 * p)).mp hl2
    linarith
  have hpκ : p * κ ≤ a / 2 := by nlinarith
  set B := 1 / Real.sqrt (2 * Real.pi * t) * ∫ z, Real.exp (-l * z ^ 2) ∂ν
  have hB : 0 ≤ B := by
    have : 0 ≤ ∫ z, Real.exp (-l * z ^ 2) ∂ν := integral_nonneg fun z => (Real.exp_pos _).le
    positivity
  have hgrowth (x : ℝ) : heatFlow ν t x ≤ B * Real.exp (κ * x ^ 2) := by
    have := heatFlow_le_gaussian_growth hν ht hl hlt x
    calc heatFlow ν t x ≤ _ := this
      _ = B * Real.exp (κ * x ^ 2) := by ring
  have hdom : Integrable (fun x : ℝ => B ^ p * Real.exp (-(a / 2) * x ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  refine hdom.mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact ((by fun_prop : Continuous fun x : ℝ => Real.exp (-a * x ^ 2)).mul
      ((continuous_heatFlow hν ht).rpow_const fun _ => Or.inr hp0.le)).aestronglyMeasurable
  · have hJ := heatFlow_nonneg ν ht x
    have hpow : (heatFlow ν t x) ^ p ≤ B ^ p * Real.exp (p * κ * x ^ 2) := by
      calc (heatFlow ν t x) ^ p ≤ (B * Real.exp (κ * x ^ 2)) ^ p :=
            Real.rpow_le_rpow hJ (hgrowth x) hp0.le
        _ = B ^ p * Real.exp (p * κ * x ^ 2) := by
            rw [Real.mul_rpow hB (Real.exp_pos _).le, ← Real.exp_mul]
            congr 2
            ring
    have hval : 0 ≤ Real.exp (-a * x ^ 2) * (heatFlow ν t x) ^ p :=
      mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hJ _)
    rw [Real.norm_eq_abs, abs_of_nonneg hval]
    have hexp : Real.exp (-a * x ^ 2) * Real.exp (p * κ * x ^ 2) ≤
        Real.exp (-(a / 2) * x ^ 2) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      nlinarith [sq_nonneg x]
    calc Real.exp (-a * x ^ 2) * (heatFlow ν t x) ^ p
        ≤ Real.exp (-a * x ^ 2) * (B ^ p * Real.exp (p * κ * x ^ 2)) :=
          mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
      _ = B ^ p * (Real.exp (-a * x ^ 2) * Real.exp (p * κ * x ^ 2)) := by ring
      _ ≤ B ^ p * Real.exp (-(a / 2) * x ^ 2) :=
          mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hB _)

/-! ### The local bound -/

private theorem sqrt_mul_heatKernel {s : ℝ} (hs : 0 < s) (w : ℝ) :
    Real.sqrt s * heatKernel s w =
      1 / Real.sqrt (2 * Real.pi) * Real.exp (-(1 / (2 * s)) * w ^ 2) := by
  unfold heatKernel
  have h2π : 0 ≤ 2 * Real.pi := by positivity
  have hs' : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  rw [Real.sqrt_mul h2π s]
  field_simp

/-- For `0 < s ≤ T` and `|y| ≤ R`: `e^{-(y-z)²/(2s)} ≤ e^{4R²} e^{-z²} + e^{-z²/(8T)}`. -/
private theorem local_gaussian_le {R T s y : ℝ} (hs : 0 < s) (hsT : s ≤ T)
    (hy : |y| ≤ R) (z : ℝ) :
    Real.exp (-(1 / (2 * s)) * (y - z) ^ 2) ≤
      Real.exp (4 * R ^ 2) * Real.exp (-1 * z ^ 2) + Real.exp (-(1 / (8 * T)) * z ^ 2) := by
  have hT : 0 < T := lt_of_lt_of_le hs hsT
  have h1 : 0 ≤ Real.exp (4 * R ^ 2) * Real.exp (-1 * z ^ 2) := by positivity
  have h2 : 0 ≤ Real.exp (-(1 / (8 * T)) * z ^ 2) := (Real.exp_pos _).le
  by_cases hz : |z| ≤ 2 * R
  · have hz2 : z ^ 2 ≤ 4 * R ^ 2 := by
      have := sq_le_sq' (neg_le_of_abs_le hz) (le_of_abs_le hz)
      nlinarith
    have hle1 : Real.exp (-(1 / (2 * s)) * (y - z) ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ (1 / (2 * s)) * (y - z) ^ 2 := by positivity
      linarith
    have hge1 : 1 ≤ Real.exp (4 * R ^ 2) * Real.exp (-1 * z ^ 2) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      linarith
    linarith
  · rw [not_le] at hz
    have hyz : |z| / 2 < |y - z| := by
      have := abs_sub_abs_le_abs_sub z y
      rw [abs_sub_comm] at this
      linarith
    have hsq : z ^ 2 / 4 ≤ (y - z) ^ 2 := by
      have h0 : 0 ≤ |z| / 2 := by positivity
      have := mul_self_le_mul_self h0 hyz.le
      rw [← sq_abs (y - z), ← sq_abs z]
      nlinarith
    have hexp : Real.exp (-(1 / (2 * s)) * (y - z) ^ 2) ≤
        Real.exp (-(1 / (8 * T)) * z ^ 2) := by
      rw [Real.exp_le_exp]
      have hsT' : 1 / (8 * T) ≤ 1 / (8 * s) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have e1 : (1 / (8 * s)) * z ^ 2 ≤ (1 / (2 * s)) * (y - z) ^ 2 := by
        rw [show (1 / (8 * s)) * z ^ 2 = (1 / (2 * s)) * (z ^ 2 / 4) by ring]
        exact mul_le_mul_of_nonneg_left hsq (by positivity)
      have e2 : (1 / (8 * T)) * z ^ 2 ≤ (1 / (8 * s)) * z ^ 2 :=
        mul_le_mul_of_nonneg_right hsT' (sq_nonneg z)
      linarith
    linarith

/-- For `T > 0` and any `R`, there is `C` with `√s · heatFlow ν s y ≤ C` for all
`s ∈ (0, T]` and `|y| ≤ R`. -/
theorem exists_sqrt_mul_heatFlow_le {ν : Measure ℝ} (hν : IsGaussianTempered ν) {T : ℝ}
    (hT : 0 < T) (R : ℝ) :
    ∃ C : ℝ, ∀ s ∈ Set.Ioc 0 T, ∀ y : ℝ, |y| ≤ R → Real.sqrt s * heatFlow ν s y ≤ C := by
  set g : ℝ → ℝ := fun z => Real.exp (4 * R ^ 2) * Real.exp (-1 * z ^ 2) +
    Real.exp (-(1 / (8 * T)) * z ^ 2)
  have hg : Integrable g ν :=
    ((hν.integrable_exp_neg_mul_sq one_pos).const_mul _).add
      (hν.integrable_exp_neg_mul_sq (by positivity))
  refine ⟨1 / Real.sqrt (2 * Real.pi) * ∫ z, g z ∂ν, ?_⟩
  rintro s ⟨hs, hsT⟩ y hy
  unfold heatFlow
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_mono ((hν.integrable_heatKernel_sub hs y).const_mul _)
    (hg.const_mul _) fun z => ?_
  rw [sqrt_mul_heatKernel hs]
  exact mul_le_mul_of_nonneg_left (local_gaussian_le hs hsT hy z) (by positivity)

end RoughHeatKernel
