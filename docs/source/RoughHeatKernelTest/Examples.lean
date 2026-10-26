module

public import RoughHeatKernel
public import RoughHeatKernelTest.Counterexamples

public section

/-! Usage examples, compiled by `verify.sh`. -/

open RoughHeatKernel MeasureTheory
open scoped ENNReal

-- The heat flow of Lebesgue measure (infinite total mass) is identically `1`.
example {t : ℝ} (ht : 0 < t) (x : ℝ) : RoughMeasure.lebesgue.heatFlow t x = 1 :=
  RoughMeasure.heatFlow_lebesgue ht x

-- A finite measure is Gaussian-tempered, so its heat flow is continuous in `x`.
example (ν : Measure ℝ) [IsFiniteMeasure ν] {t : ℝ} (ht : 0 < t) :
    Continuous (heatFlow ν t) :=
  continuous_heatFlow (isGaussianTempered_of_isFiniteMeasure ν) ht

-- The extended-real flow in "prefactor × Gaussian weight" form, for every measure.
example (ν : Measure ℝ) (t x : ℝ) :
    lheatFlow ν t x = ENNReal.ofReal (1 / Real.sqrt (2 * Real.pi * t)) *
      ∫⁻ y, ENNReal.ofReal (Real.exp (-(x - y) ^ 2 / (2 * t))) ∂ν :=
  lheatFlow_eq_ofReal_mul_lintegral ν t x

-- Integrating against `N(x, t)` is integrating against the kernel.
example {t : NNReal} (ht : t ≠ 0) (x : ℝ) (f : ℝ → ℝ) :
    ∫ y, f y ∂ProbabilityTheory.gaussianReal x t = ∫ y, heatKernel t (x - y) * f y :=
  integral_gaussianReal_eq_integral_heatKernel ht x f

-- The `L²` norm of the kernel, from the general `L^q` formula.
example {t : ℝ} (ht : 0 < t) :
    eLpNorm (heatKernel t) 2 volume =
      ENNReal.ofReal (heatLqConst 2 * t ^ (-(1 - (2 : ℝ≥0∞)⁻¹.toReal) / 2)) :=
  eLpNorm_heatKernel (by norm_num) ht

-- Spatial increment of the kernel, with the trivial bound 2 and the derivative bound.
example {t : ℝ} (ht : 0 < t) (x z : ℝ) :
    ∫ y, |heatKernel t (x - y) - heatKernel t (z - y)| ≤ min 2 (|x - z| / Real.sqrt t) :=
  integral_abs_heatKernel_sub_sub_le ht x z

-- Time increment of the kernel.
example {t ε : ℝ} (ht : 0 < t) (hε : 0 ≤ ε) (x : ℝ) :
    ∫ y, |heatKernel (t + ε) (x - y) - heatKernel t (x - y)| ≤ min 2 (ε / t) :=
  integral_abs_heatKernel_add_sub_le ht hε x

-- The second moment of the kernel is its variance `t`.
example {t : ℝ} (ht : 0 < t) : ∫ x, x ^ 2 * heatKernel t x = t :=
  integral_sq_mul_heatKernel ht

-- The Chen–Dalang estimate for a Gaussian-tempered measure (possibly of infinite mass):
-- tempered measures are locally finite, hence σ-finite, so Tonelli applies.
example (ν : Measure ℝ) (hν : IsGaussianTempered ν) {t : ℝ} (ht : 0 < t) (x : ℝ)
    {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ s in Set.Ioo 0 t, ∫⁻ y, lheatFlow ν s y ^ 2 *
        ENNReal.ofReal (heatKernel ((t - s) / 2) (x - y)) * h (t - s) ≤
      ENNReal.ofReal (2 * Real.sqrt t) * lheatFlow ν (2 * t) x ^ 2 *
        ∫⁻ s in Set.Ioo 0 t, h (t - s) * ENNReal.ofReal (1 / Real.sqrt s) := by
  haveI := hν.isLocallyFiniteMeasure
  exact lintegral_sq_lheatFlow_conv_le ν ht x hh

-- The Gaussian product identity.
example {t : ℝ} (ht : 0 < t) (y z₁ z₂ : ℝ) :
    heatKernel t (y - z₁) * heatKernel t (y - z₂) =
      heatKernel (2 * t) (z₁ - z₂) * heatKernel (t / 2) (y - (z₁ + z₂) / 2) :=
  heatKernel_mul_heatKernel_eq ht y z₁ z₂

-- The arcsine integral.
example {t : ℝ} (ht : 0 < t) :
    ∫⁻ s in Set.Ioo 0 t, ENNReal.ofReal (1 / Real.sqrt (s * (t - s))) =
      ENNReal.ofReal Real.pi :=
  lintegral_arcsine ht

-- The white-noise bound for a Gaussian-tempered measure.
example (ν : Measure ℝ) (hν : IsGaussianTempered ν) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ∫⁻ s in Set.Ioo 0 t, ∫⁻ y, lheatFlow ν s y ^ 2 *
        ENNReal.ofReal (heatKernel (t - s) (x - y) ^ 2) ≤
      ENNReal.ofReal (Real.sqrt Real.pi * Real.sqrt t) * lheatFlow ν (2 * t) x ^ 2 := by
  have := hν.isLocallyFiniteMeasure
  exact lintegral_sq_lheatFlow_mul_heatKernel_sq_le ν ht x

-- The semigroup property of the heat flow, integrated in time: `∫_0^t ∫ p_{t-s} J(s) = t J(t)`.
example (ν : Measure ℝ) [SFinite ν] (t x : ℝ) :
    ∫⁻ s in Set.Ioo 0 t, ∫⁻ y, ENNReal.ofReal (heatKernel (t - s) (x - y)) * lheatFlow ν s y =
      ENNReal.ofReal t * lheatFlow ν t x :=
  lintegral_lintegral_heatKernel_mul_lheatFlow ν t x

-- The time-resolved quadratic bound against the doubled heat-flow profile.
example (ν : Measure ℝ) [SFinite ν] {s t : ℝ} (hs : 0 < s) (hst : s < t) (x : ℝ) :
    ∫⁻ y, ENNReal.ofReal (heatKernel (t - s) (x - y) ^ 2) * lheatFlow ν (2 * s) y ^ 2 ≤
      ENNReal.ofReal (1 / Real.sqrt (2 * Real.pi) * (Real.sqrt t / Real.sqrt (s * (t - s)))) *
        lheatFlow ν (2 * t) x ^ 2 :=
  lintegral_heatKernel_sq_mul_lheatFlow_two_mul_sq_le ν hs hst x

-- The signed datum is genuinely nonzero: its heat flow is negative at x = 1.
example {t : ℝ} (ht : 0 < t) :
    RoughMeasure.diracZeroSubDiracOne.heatFlow t 1 < 0 :=
  RoughMeasure.heatFlow_diracZeroSubDiracOne_one_neg ht

-- The SAME concrete datum has infinite total variation and a nonzero finite heat flow.
example {t : ℝ} (ht : 0 < t) (x : ℝ) :
    RoughMeasure.lebesgue.totalVariation Set.univ = ⊤ ∧
      RoughMeasure.lebesgue.heatFlow t x = 1 :=
  ⟨RoughMeasure.lebesgue_totalVariation_univ, RoughMeasure.heatFlow_lebesgue ht x⟩

-- Finite signed input preserves Mathlib's own total variation.
example (s : SignedMeasure ℝ) :
    (RoughMeasure.ofSignedMeasure s).totalVariation = s.totalVariation :=
  RoughMeasure.totalVariation_ofSignedMeasure s

-- Arbitrary positive Gaussian-tempered data: joint time-space continuity.
example (ν : Measure ℝ) (hν : IsGaussianTempered ν) (a : ℝ × ℝ) (ha : 0 < a.1) :
    ContinuousAt (fun z : ℝ × ℝ => heatFlow ν z.1 z.2) a :=
  continuousAt_heatFlow_joint hν a ha

-- Zero data, a translated Dirac mass, and genuinely signed data use the same API.
example (a : ℝ × ℝ) (ha : 0 < a.1) :
    ContinuousAt (fun z : ℝ × ℝ => heatFlow (0 : Measure ℝ) z.1 z.2) a :=
  continuousAt_heatFlow_joint (isGaussianTempered_of_isFiniteMeasure _) a ha

example (y : ℝ) (a : ℝ × ℝ) (ha : 0 < a.1) :
    ContinuousAt (fun z : ℝ × ℝ => (RoughMeasure.dirac y).heatFlow z.1 z.2) a :=
  RoughMeasure.continuousAt_heatFlow_joint _ a ha

example (a : ℝ × ℝ) (ha : 0 < a.1) :
    ContinuousAt (fun z : ℝ × ℝ => RoughMeasure.diracZeroSubDiracOne.heatFlow z.1 z.2) a :=
  RoughMeasure.continuousAt_heatFlow_joint _ a ha

-- The same concrete infinite-TV datum has a jointly continuous heat flow.
example (a : ℝ × ℝ) (ha : 0 < a.1) :
    RoughMeasure.lebesgue.totalVariation Set.univ = ⊤ ∧
      ContinuousAt (fun z : ℝ × ℝ => RoughMeasure.lebesgue.heatFlow z.1 z.2) a :=
  ⟨RoughMeasure.lebesgue_totalVariation_univ,
    RoughMeasure.continuousAt_heatFlow_joint _ a ha⟩

-- The same universal numerical constant works for every time and translated pair.
example {r : ℝ} (hr : 0 < r) (x z y : ℝ) :
    |heatKernel r (x-y)-heatKernel r (z-y)| ≤
      (2*Real.exp 1)*|x-z|^(1/4:ℝ)*r^(-(1/8:ℝ))*
        (heatKernel (2*r) (x-y)+heatKernel (2*r) (z-y)) := by
  simpa only [show (x-y)-(z-y)=x-z by ring] using
    SpatialEnvelope.quarter_increment hr (x-y) (z-y)

-- Nontrivial spatial increment: reuse the existing concrete Gaussian witness.
example : 0 < |heatKernel 1 0-heatKernel 1 1| ∧
    |heatKernel 1 0-heatKernel 1 1| ≤
      (2*Real.exp 1)*|0-1|^(1/4:ℝ)*(1:ℝ)^(-(1/8:ℝ))*
        (heatKernel (2*1) 0+heatKernel (2*1) 1) := by
  exact ⟨abs_pos.mpr (sub_ne_zero.mpr
    (ne_of_gt RoughHeatKernelTest.Counterexamples.off_center_strict)),
    SpatialEnvelope.quarter_increment (by norm_num) 0 1⟩

-- Setting the envelope's universal coefficient to zero is genuinely false.
example : ¬ (∀ r : ℝ, 0 < r → ∀ u v : ℝ,
    |heatKernel r u-heatKernel r v| ≤
      (0:ℝ)*|u-v|^(1/4:ℝ)*r^(-(1/8:ℝ))*
        (heatKernel (2*r) u+heatKernel (2*r) v)) := by
  intro h
  have hb := h 1 (by norm_num) 0 1
  norm_num only [zero_mul] at hb
  have hp : 0 < |heatKernel 1 0-heatKernel 1 1| :=
    abs_pos.mpr (sub_ne_zero.mpr
      (ne_of_gt RoughHeatKernelTest.Counterexamples.off_center_strict))
  exact (not_le_of_gt hp) hb

-- Beta integral with `a = b = 1/2` on `[0, 1]`: the arcsine value `Γ(1/2)² / Γ(1) = π`.
example : ∫ s in (0 : ℝ)..1, s ^ ((1 / 2 : ℝ) - 1) * (1 - s) ^ ((1 / 2 : ℝ) - 1) = Real.pi := by
  rw [integral_rpow_mul_sub_rpow (by norm_num) (by norm_num) one_pos]
  norm_num [Real.Gamma_one_half_eq, Real.sq_sqrt Real.pi_pos.le]
  rw [← sq, Real.sq_sqrt Real.pi_pos.le]

-- The median of the standard normal law is `0`, and `erf 0 = 0`.
example : normalCDF 0 = 1 / 2 ∧ erf 0 = 0 := by
  refine ⟨normalCDF_zero, ?_⟩
  simp [erf]

-- The series at `z = 0` sums to `1 = e^0 (1 + erf 0)`.
example : HasSum (fun k : ℕ => (0 : ℝ) ^ k / Real.Gamma ((k : ℝ) / 2 + 1)) 1 := by
  have h := hasSum_pow_div_Gamma (z := 0) le_rfl
  simpa [erf] using h
