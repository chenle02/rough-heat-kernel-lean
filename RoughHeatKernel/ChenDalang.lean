/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
module

public import RoughHeatKernel.Tempered

public section

/-!
# The Chen–Dalang convolution estimate

For a positive measure `ν` on `ℝ`, write `J(s, y) = ∫ p_s(y - z) ν(dz)` (`lheatFlow`).
For `t > 0` and a measurable `h ≥ 0`,

`∫_0^t ∫ J(s, y)² p_{(t-s)/2}(x - y) h(t - s) dy ds ≤ 2√t · J(2t, x)² · ∫_0^t h(t - s)/√s ds`.

This is the `a = 2` Gaussian case of Chen–Dalang (Ann. Probab. 2015), Lemma 3.9, (3.11).
Everything is stated with lower Lebesgue integrals in `[0, ∞]`, so no integrability
hypothesis is needed and the inequality holds for every s-finite `ν` (both sides may be
`∞`). The ingredients are:

* the Gaussian product identity
  `p_s(y - z₁) p_s(y - z₂) = p_{2s}(z₁ - z₂) p_{s/2}(y - (z₁ + z₂)/2)`
  (`heatKernel_mul_heatKernel_eq`);
* the kernel comparison `p_a ≤ √(b/a) p_b` for `0 < a ≤ b` (`heatKernel_le_sqrt_div_mul`);
* the semigroup identity in `y`, and Tonelli over `ν ⊗ ν`.

Gaussian-tempered measures are locally finite (`IsGaussianTempered.isLocallyFiniteMeasure`),
hence σ-finite, so the estimate applies to them.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace RoughHeatKernel

theorem measurable_heatKernel (t : ℝ) : Measurable (heatKernel t) :=
  (continuous_heatKernel t).measurable

attribute [local fun_prop] continuous_heatKernel measurable_heatKernel

/-! ### Gaussian identities -/

/-- Kernel comparison: `p_a(x) ≤ √(b/a) p_b(x)` for `0 < a ≤ b`. -/
theorem heatKernel_le_sqrt_div_mul {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (x : ℝ) :
    heatKernel a x ≤ Real.sqrt (b / a) * heatKernel b x := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h2π : 0 < 2 * Real.pi := by positivity
  have hpre : 1 / Real.sqrt (2 * Real.pi * a) =
      Real.sqrt (b / a) * (1 / Real.sqrt (2 * Real.pi * b)) := by
    rw [Real.sqrt_div hb.le, Real.sqrt_mul h2π.le, Real.sqrt_mul h2π.le]
    have : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
    have : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
    have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h2π
    field_simp
  unfold heatKernel
  rw [hpre, mul_assoc]
  have hc : 0 < Real.sqrt (b / a) := Real.sqrt_pos.mpr (div_pos hb ha)
  have hd : 0 < 1 / Real.sqrt (2 * Real.pi * b) :=
    one_div_pos.mpr (Real.sqrt_pos.mpr (by positivity))
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hd.le) hc.le
  refine Real.exp_le_exp.mpr ?_
  have hab' : 1 / (2 * b) ≤ 1 / (2 * a) := one_div_le_one_div_of_le (by positivity) (by linarith)
  nlinarith [sq_nonneg x]

/-- The Gaussian product identity:
`p_t(y - z₁) p_t(y - z₂) = p_{2t}(z₁ - z₂) p_{t/2}(y - (z₁ + z₂)/2)` for `t > 0`. -/
theorem heatKernel_mul_heatKernel_eq {t : ℝ} (ht : 0 < t) (y z₁ z₂ : ℝ) :
    heatKernel t (y - z₁) * heatKernel t (y - z₂) =
      heatKernel (2 * t) (z₁ - z₂) * heatKernel (t / 2) (y - (z₁ + z₂) / 2) := by
  have hA : 0 < 2 * Real.pi * t := by positivity
  have h1 : Real.sqrt (2 * Real.pi * t) * Real.sqrt (2 * Real.pi * t) = 2 * Real.pi * t :=
    Real.mul_self_sqrt hA.le
  have h2 : Real.sqrt (2 * Real.pi * (2 * t)) * Real.sqrt (2 * Real.pi * (t / 2)) =
      2 * Real.pi * t := by
    rw [← Real.sqrt_mul (by positivity),
      show 2 * Real.pi * (2 * t) * (2 * Real.pi * (t / 2)) = (2 * Real.pi * t) ^ 2 by ring,
      Real.sqrt_sq hA.le]
  unfold heatKernel
  have ht' : t ≠ 0 := ht.ne'
  calc 1 / Real.sqrt (2 * Real.pi * t) * Real.exp (-(1 / (2 * t)) * (y - z₁) ^ 2) *
        (1 / Real.sqrt (2 * Real.pi * t) * Real.exp (-(1 / (2 * t)) * (y - z₂) ^ 2))
      = 1 / (Real.sqrt (2 * Real.pi * t) * Real.sqrt (2 * Real.pi * t)) *
          Real.exp (-(1 / (2 * t)) * (y - z₁) ^ 2 + -(1 / (2 * t)) * (y - z₂) ^ 2) := by
        rw [Real.exp_add]; ring
    _ = 1 / (Real.sqrt (2 * Real.pi * (2 * t)) * Real.sqrt (2 * Real.pi * (t / 2))) *
          Real.exp (-(1 / (2 * (2 * t))) * (z₁ - z₂) ^ 2 +
            -(1 / (2 * (t / 2))) * (y - (z₁ + z₂) / 2) ^ 2) := by
        rw [h1, h2]
        congr 2
        field_simp
        ring
    _ = _ := by rw [Real.exp_add]; ring

/-- `y ↦ p_a(y - m) p_b(x - y)` is integrable for `a, b > 0`. -/
theorem integrable_heatKernel_sub_mul_heatKernel_sub {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (x m : ℝ) :
    Integrable (fun y => heatKernel a (y - m) * heatKernel b (x - y)) := by
  have h := (integrable_heatKernel_sub_mul_heatKernel ha hb (x - m)).comp_sub_right m
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [show x - m - (y - m) = x - y by ring, mul_comm]

/-- The semigroup identity with shifted arguments:
`∫ p_a(y - m) p_b(x - y) dy = p_{a+b}(x - m)` for `a, b > 0`. -/
theorem integral_heatKernel_sub_mul_heatKernel_sub {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (x m : ℝ) :
    ∫ y, heatKernel a (y - m) * heatKernel b (x - y) = heatKernel (a + b) (x - m) := by
  have h := integral_heatKernel_mul_heatKernel ha hb (x - m)
  rw [← integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun y => heatKernel b (x - m - y) * heatKernel a y) m] at h
  rw [add_comm a b, ← h]
  congr 1
  ext y
  rw [show x - m - (y - m) = x - y by ring, mul_comm]

/-- The pointwise step: for `0 < s < t`,
`∫ p_s(y - z₁) p_s(y - z₂) p_{(t-s)/2}(x - y) dy ≤ 2√(t/s) p_{2t}(x - z₁) p_{2t}(x - z₂)`. -/
theorem lintegral_heatKernel_mul_mul_le {s t : ℝ} (hs : 0 < s) (hst : s < t) (x z₁ z₂ : ℝ) :
    ∫⁻ y, ENNReal.ofReal (heatKernel s (y - z₁)) * ENNReal.ofReal (heatKernel s (y - z₂)) *
        ENNReal.ofReal (heatKernel ((t - s) / 2) (x - y)) ≤
      ENNReal.ofReal (2 * Real.sqrt (t / s)) *
        (ENNReal.ofReal (heatKernel (2 * t) (x - z₁)) *
          ENNReal.ofReal (heatKernel (2 * t) (x - z₂))) := by
  have ht : 0 < t := hs.trans hst
  have hts : 0 < (t - s) / 2 := by linarith
  have hs2 : 0 < s / 2 := by positivity
  have hp : ∀ r : ℝ, 0 < r → ∀ u, 0 ≤ heatKernel r u := fun r hr u => (heatKernel_pos hr u).le
  have e : ∀ y, ENNReal.ofReal (heatKernel s (y - z₁)) * ENNReal.ofReal (heatKernel s (y - z₂)) *
      ENNReal.ofReal (heatKernel ((t - s) / 2) (x - y)) =
      ENNReal.ofReal (heatKernel (2 * s) (z₁ - z₂)) *
        ENNReal.ofReal (heatKernel (s / 2) (y - (z₁ + z₂) / 2) *
          heatKernel ((t - s) / 2) (x - y)) := by
    intro y
    rw [← ENNReal.ofReal_mul (hp s hs _),
      ← ENNReal.ofReal_mul (mul_nonneg (hp s hs _) (hp s hs _)),
      ← ENNReal.ofReal_mul (hp _ (by positivity) _), heatKernel_mul_heatKernel_eq hs]
    congr 1
    ring
  simp_rw [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal
      (integrable_heatKernel_sub_mul_heatKernel_sub hs2 hts x ((z₁ + z₂) / 2))
      (Filter.Eventually.of_forall fun y => mul_nonneg (hp _ hs2 _) (hp _ hts _)),
    integral_heatKernel_sub_mul_heatKernel_sub hs2 hts,
    show s / 2 + (t - s) / 2 = t / 2 by ring,
    ← ENNReal.ofReal_mul (hp _ (by positivity) _),
    ← ENNReal.ofReal_mul (hp _ (by positivity) _),
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [heatKernel_mul_heatKernel_eq (by positivity : 0 < 2 * t) x z₁ z₂]
  have k1 := heatKernel_le_sqrt_div_mul (by positivity : 0 < 2 * s)
    (by linarith : 2 * s ≤ 2 * (2 * t)) (z₁ - z₂)
  have k2 := heatKernel_le_sqrt_div_mul (by positivity : 0 < t / 2)
    (by linarith : t / 2 ≤ 2 * t / 2) (x - (z₁ + z₂) / 2)
  have hsq : Real.sqrt (2 * (2 * t) / (2 * s)) * Real.sqrt (2 * t / 2 / (t / 2)) =
      2 * Real.sqrt (t / s) := by
    rw [← Real.sqrt_mul (by positivity),
      show 2 * (2 * t) / (2 * s) * (2 * t / 2 / (t / 2)) = 2 ^ 2 * (t / s) by
        field_simp; try ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  calc heatKernel (2 * s) (z₁ - z₂) * heatKernel (t / 2) (x - (z₁ + z₂) / 2)
      ≤ (Real.sqrt (2 * (2 * t) / (2 * s)) * heatKernel (2 * (2 * t)) (z₁ - z₂)) *
          (Real.sqrt (2 * t / 2 / (t / 2)) * heatKernel (2 * t / 2) (x - (z₁ + z₂) / 2)) :=
        mul_le_mul k1 k2 (hp _ (by positivity) _)
          (mul_nonneg (Real.sqrt_nonneg _) (hp _ (by positivity) _))
    _ = 2 * Real.sqrt (t / s) * (heatKernel (2 * (2 * t)) (z₁ - z₂) *
          heatKernel (2 * t / 2) (x - (z₁ + z₂) / 2)) := by rw [← hsq]; ring

/-! ### The estimate -/

/-- `J(s, y)² = ∫∫ p_s(y - z₁) p_s(y - z₂) ν(dz₁) ν(dz₂)` for `J = lheatFlow ν`. -/
theorem lheatFlow_sq_eq (ν : Measure ℝ) [SFinite ν] (s y : ℝ) :
    lheatFlow ν s y ^ 2 = ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (heatKernel s (y - q.1)) *
      ENNReal.ofReal (heatKernel s (y - q.2)) ∂(ν.prod ν) := by
  rw [sq, lheatFlow]
  exact (lintegral_prod_mul (μ := ν) (ν := ν)
    (f := fun z => ENNReal.ofReal (heatKernel s (y - z)))
    (g := fun z => ENNReal.ofReal (heatKernel s (y - z))) (by fun_prop) (by fun_prop)).symm

/-- The pointwise-in-time step of `lintegral_sq_lheatFlow_conv_le`: for `0 < r < R`,
`∫ J(r, y)² p_{(R-r)/2}(x - y) dy ≤ 2√(R/r) J(2R, x)²`, where `J = lheatFlow ν`. -/
theorem lintegral_sq_lheatFlow_mul_le (ν : Measure ℝ) [SFinite ν] {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) (x : ℝ) :
    ∫⁻ y, lheatFlow ν r y ^ 2 * ENNReal.ofReal (heatKernel ((R - r) / 2) (x - y)) ≤
      ENNReal.ofReal (2 * Real.sqrt (R / r)) * lheatFlow ν (2 * R) x ^ 2 := by
  have hF : Measurable fun q : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (heatKernel r (q.1 - q.2.1)) * ENNReal.ofReal (heatKernel r (q.1 - q.2.2)) *
        ENNReal.ofReal (heatKernel ((R - r) / 2) (x - q.1)) := by
    fun_prop
  have hk : Measurable fun q : ℝ × ℝ =>
      ENNReal.ofReal (heatKernel (2 * R) (x - q.1)) *
        ENNReal.ofReal (heatKernel (2 * R) (x - q.2)) := by
    fun_prop
  calc ∫⁻ y, lheatFlow ν r y ^ 2 * ENNReal.ofReal (heatKernel ((R - r) / 2) (x - y))
      = ∫⁻ y, ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (heatKernel r (y - q.1)) *
          ENNReal.ofReal (heatKernel r (y - q.2)) *
            ENNReal.ofReal (heatKernel ((R - r) / 2) (x - y)) ∂(ν.prod ν) := by
        refine lintegral_congr fun y => ?_
        rw [lheatFlow_sq_eq, ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ q : ℝ × ℝ, (∫⁻ y : ℝ, ENNReal.ofReal (heatKernel r (y - q.1)) *
          ENNReal.ofReal (heatKernel r (y - q.2)) *
            ENNReal.ofReal (heatKernel ((R - r) / 2) (x - y))) ∂(ν.prod ν) :=
        lintegral_lintegral_swap hF.aemeasurable
    _ ≤ ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (heatKernel (2 * R) (x - q.1)) *
          ENNReal.ofReal (heatKernel (2 * R) (x - q.2)) *
            ENNReal.ofReal (2 * Real.sqrt (R / r)) ∂(ν.prod ν) := by
        refine lintegral_mono fun q => ?_
        rw [mul_comm]
        exact lintegral_heatKernel_mul_mul_le hr hrR x q.1 q.2
    _ = ENNReal.ofReal (2 * Real.sqrt (R / r)) * lheatFlow ν (2 * R) x ^ 2 := by
        rw [lintegral_mul_const _ hk, lheatFlow_sq_eq, mul_comm]

/-- `ENNReal.ofReal (∫ f dμ) ≤ ∫⁻ ENNReal.ofReal f dμ` for nonnegative `f`, with no
integrability hypothesis (a non-integrable `f` has Bochner integral `0`). -/
theorem ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    ENNReal.ofReal (∫ a, f a ∂μ) ≤ ∫⁻ a, ENNReal.ofReal (f a) ∂μ := by
  calc ENNReal.ofReal (∫ a, f a ∂μ) ≤ ‖∫ a, f a ∂μ‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ∫⁻ a, ‖f a‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ a, ENNReal.ofReal (f a) ∂μ :=
        lintegral_congr fun a => Real.enorm_eq_ofReal (hf a)

/-- The Chen–Dalang convolution estimate (`a = 2`, Gaussian case), for every s-finite
positive measure `ν`, `t > 0`, `x ∈ ℝ` and measurable `h : ℝ → [0, ∞]`:
`∫_0^t ∫ J(s, y)² p_{(t-s)/2}(x - y) h(t - s) dy ds ≤ 2√t J(2t, x)² ∫_0^t h(t - s)/√s ds`,
where `J = lheatFlow ν`. -/
theorem lintegral_sq_lheatFlow_conv_le (ν : Measure ℝ) [SFinite ν] {t : ℝ} (ht : 0 < t)
    (x : ℝ) {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ s in Ioo 0 t, ∫⁻ y, lheatFlow ν s y ^ 2 *
        ENNReal.ofReal (heatKernel ((t - s) / 2) (x - y)) * h (t - s) ≤
      ENNReal.ofReal (2 * Real.sqrt t) * lheatFlow ν (2 * t) x ^ 2 *
        ∫⁻ s in Ioo 0 t, h (t - s) * ENNReal.ofReal (1 / Real.sqrt s) := by
  have hpt : ∀ s ∈ Ioo 0 t, ∫⁻ y, lheatFlow ν s y ^ 2 *
      ENNReal.ofReal (heatKernel ((t - s) / 2) (x - y)) * h (t - s) ≤
      ENNReal.ofReal (2 * Real.sqrt t) * lheatFlow ν (2 * t) x ^ 2 *
        (h (t - s) * ENNReal.ofReal (1 / Real.sqrt s)) := by
    intro s hs
    obtain ⟨hs0, hst⟩ := hs
    set k := h (t - s)
    have hF : Measurable fun q : ℝ × (ℝ × ℝ) =>
        ENNReal.ofReal (heatKernel s (q.1 - q.2.1)) * ENNReal.ofReal (heatKernel s (q.1 - q.2.2)) *
          ENNReal.ofReal (heatKernel ((t - s) / 2) (x - q.1)) * k := by fun_prop
    calc ∫⁻ y, lheatFlow ν s y ^ 2 * ENNReal.ofReal (heatKernel ((t - s) / 2) (x - y)) * k
        = ∫⁻ y, ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (heatKernel s (y - q.1)) *
            ENNReal.ofReal (heatKernel s (y - q.2)) *
              ENNReal.ofReal (heatKernel ((t - s) / 2) (x - y)) * k ∂(ν.prod ν) := by
          refine lintegral_congr fun y => ?_
          rw [lheatFlow_sq_eq, ← lintegral_mul_const _ (by fun_prop),
            ← lintegral_mul_const _ (by fun_prop)]
      _ = ∫⁻ q : ℝ × ℝ, (∫⁻ y : ℝ, ENNReal.ofReal (heatKernel s (y - q.1)) *
            ENNReal.ofReal (heatKernel s (y - q.2)) *
              ENNReal.ofReal (heatKernel ((t - s) / 2) (x - y)) * k) ∂(ν.prod ν) :=
          lintegral_lintegral_swap hF.aemeasurable
      _ ≤ ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (2 * Real.sqrt (t / s)) *
            (ENNReal.ofReal (heatKernel (2 * t) (x - q.1)) *
              ENNReal.ofReal (heatKernel (2 * t) (x - q.2))) * k ∂(ν.prod ν) := by
          refine lintegral_mono fun q => ?_
          rw [lintegral_mul_const _ (by fun_prop)]
          gcongr
          exact lintegral_heatKernel_mul_mul_le hs0 hst x q.1 q.2
      _ = ENNReal.ofReal (2 * Real.sqrt (t / s)) * lheatFlow ν (2 * t) x ^ 2 * k := by
          rw [lintegral_mul_const _ (by fun_prop), lintegral_const_mul _ (by fun_prop),
            lheatFlow_sq_eq]
      _ = ENNReal.ofReal (2 * Real.sqrt t) * lheatFlow ν (2 * t) x ^ 2 *
            (k * ENNReal.ofReal (1 / Real.sqrt s)) := by
          rw [show 2 * Real.sqrt (t / s) = 2 * Real.sqrt t * (1 / Real.sqrt s) by
              rw [Real.sqrt_div ht.le]; ring,
            ENNReal.ofReal_mul (by positivity)]
          ring
  calc ∫⁻ s in Ioo 0 t, ∫⁻ y, lheatFlow ν s y ^ 2 *
        ENNReal.ofReal (heatKernel ((t - s) / 2) (x - y)) * h (t - s)
      ≤ ∫⁻ s in Ioo 0 t, ENNReal.ofReal (2 * Real.sqrt t) * lheatFlow ν (2 * t) x ^ 2 *
          (h (t - s) * ENNReal.ofReal (1 / Real.sqrt s)) :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).mpr
          (Filter.Eventually.of_forall hpt))
    _ = _ := lintegral_const_mul _ (by fun_prop)

/-! ### Gaussian-tempered measures are locally finite -/

/-- A Gaussian-tempered measure is finite on bounded sets, hence locally finite (and so
σ-finite, by Mathlib's instance for second-countable spaces). -/
theorem IsGaussianTempered.isLocallyFiniteMeasure {ν : Measure ℝ} (hν : IsGaussianTempered ν) :
    IsLocallyFiniteMeasure ν := by
  refine ⟨fun x => ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩⟩
  set R := |x| + 1
  have hsub : Metric.ball x 1 ⊆ {y | ENNReal.ofReal (Real.exp (-1 * R ^ 2)) ≤
      ENNReal.ofReal (Real.exp (-1 * y ^ 2))} := by
    intro y hy
    rw [Metric.mem_ball, Real.dist_eq] at hy
    simp only [Set.mem_ofPred_eq]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have h1 : |y| ≤ R := by
      have := abs_sub_abs_le_abs_sub y x
      simp only [R]; linarith
    nlinarith [sq_abs y, abs_nonneg y]
  have hε : ENNReal.ofReal (Real.exp (-1 * R ^ 2)) ≠ 0 := by
    simp [Real.exp_pos]
  have hm := mul_meas_ge_le_lintegral₀ (μ := ν)
    (f := fun y => ENNReal.ofReal (Real.exp (-1 * y ^ 2))) (by fun_prop)
    (ENNReal.ofReal (Real.exp (-1 * R ^ 2)))
  calc ν (Metric.ball x 1) ≤ ν {y | ENNReal.ofReal (Real.exp (-1 * R ^ 2)) ≤
        ENNReal.ofReal (Real.exp (-1 * y ^ 2))} := measure_mono hsub
    _ < ⊤ := ENNReal.lt_top_of_mul_ne_top_right
        (ne_top_of_le_ne_top (hν 1 one_pos).ne hm) hε

end RoughHeatKernel
