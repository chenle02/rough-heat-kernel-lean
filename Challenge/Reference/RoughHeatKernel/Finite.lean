/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Challenge.Reference.RoughHeatKernel.RoughMeasure
import Challenge.Reference.RoughHeatKernel.Lq
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

/-!
# Finite measures and the Dirac mass

Every finite signed measure, given by its Jordan decomposition, is a rough measure with
no further hypothesis. For finite `μ`, `|heatFlow μ t x| ≤ (2πt)^{-1/2} |μ|(ℝ)` for every
`x`. For `μ = δ_{x₀}`, the heat flow is `p_t(· - x₀)`; its supremum `(2πt)^{-1/2}` is
attained, and its `L^q` norm is that of the kernel for every `q ∈ [1, ∞]`.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace RoughHeatKernel

namespace RoughMeasure

/-- A finite signed measure, given by its Jordan pair, is a rough measure. -/
noncomputable def ofFinite (pos neg : Measure ℝ) [IsFiniteMeasure pos] [IsFiniteMeasure neg]
    (h : pos ⟂ₘ neg) : RoughMeasure where
  pos := pos
  neg := neg
  mutuallySingular := h
  pos_tempered := isGaussianTempered_of_isFiniteMeasure pos
  neg_tempered := isGaussianTempered_of_isFiniteMeasure neg

theorem ofFinite_totalVariation_lt_top (pos neg : Measure ℝ) [IsFiniteMeasure pos]
    [IsFiniteMeasure neg] (h : pos ⟂ₘ neg) :
    (ofFinite pos neg h).totalVariation Set.univ < ⊤ :=
  measure_lt_top (pos + neg) _

/-- For finite `μ`: `|heatFlow μ t x| ≤ (2πt)^{-1/2} |μ|(ℝ)` for every `x`. -/
theorem abs_heatFlow_le_of_isFiniteMeasure (μ : RoughMeasure)
    [IsFiniteMeasure μ.totalVariation] {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |μ.heatFlow t x| ≤ 1 / Real.sqrt (2 * Real.pi * t) * (μ.totalVariation Set.univ).toReal := by
  refine (abs_heatFlow_le μ ht x).trans ?_
  have hbound : RoughHeatKernel.heatFlow μ.totalVariation t x ≤
      ∫ _ : ℝ, 1 / Real.sqrt (2 * Real.pi * t) ∂μ.totalVariation :=
    integral_mono (μ.totalVariation_tempered.integrable_heatKernel_sub ht x)
      (integrable_const _) fun y => by
        rw [← heatKernel_zero]
        exact heatKernel_le_heatKernel_zero ht _
  rw [integral_const, smul_eq_mul, Measure.real] at hbound
  linarith

theorem heatFlow_dirac_eq (x₀ t : ℝ) :
    (dirac x₀).heatFlow t = fun x => heatKernel t (x - x₀) :=
  funext (heatFlow_dirac x₀ t)

/-- `sup_x |heatFlow δ_{x₀} t x| = (2πt)^{-1/2}`, attained at `x₀`. -/
theorem iSup_abs_heatFlow_dirac {t : ℝ} (ht : 0 < t) (x₀ : ℝ) :
    (⨆ x, |(dirac x₀).heatFlow t x|) = 1 / Real.sqrt (2 * Real.pi * t) := by
  have hval (x : ℝ) : |(dirac x₀).heatFlow t x| = heatKernel t (x - x₀) := by
    rw [heatFlow_dirac, abs_of_pos (heatKernel_pos ht _)]
  simp only [hval]
  have hpeak : heatKernel t (x₀ - x₀) = 1 / Real.sqrt (2 * Real.pi * t) := by
    rw [sub_self, heatKernel_zero]
  have hle (x : ℝ) : heatKernel t (x - x₀) ≤ 1 / Real.sqrt (2 * Real.pi * t) := by
    rw [← heatKernel_zero]
    exact heatKernel_le_heatKernel_zero ht _
  apply le_antisymm
  · exact ciSup_le hle
  · rw [← hpeak]
    have hbdd : BddAbove (Set.range fun x => heatKernel t (x - x₀)) := by
      refine ⟨1 / Real.sqrt (2 * Real.pi * t), ?_⟩
      rintro _ ⟨x, rfl⟩
      exact hle x
    exact le_ciSup (f := fun x => heatKernel t (x - x₀)) hbdd x₀

/-- The `L^q` norm of the heat flow of `δ_{x₀}` is that of the kernel, for `q ∈ [1, ∞]`. -/
theorem eLpNorm_heatFlow_dirac {q : ℝ≥0∞} (hq : 1 ≤ q) {t : ℝ} (ht : 0 < t) (x₀ : ℝ) :
    eLpNorm ((dirac x₀).heatFlow t) q volume =
      ENNReal.ofReal (heatLqConst q * t ^ (-(1 - q⁻¹.toReal) / 2)) := by
  rw [heatFlow_dirac_eq]
  have htrans : eLpNorm (fun x => heatKernel t (x - x₀)) q volume =
      eLpNorm (heatKernel t) q volume :=
    eLpNorm_comp_measurePreserving (integrable_heatKernel ht).aestronglyMeasurable
      (measurePreserving_sub_right volume x₀)
  rw [htrans, eLpNorm_heatKernel hq ht]

/-! ### Bridge to Mathlib's `SignedMeasure` -/

/-- A finite signed measure from Mathlib, as a rough measure via its Jordan decomposition. -/
noncomputable def ofSignedMeasure (s : SignedMeasure ℝ) : RoughMeasure :=
  ofFinite s.toJordanDecomposition.posPart s.toJordanDecomposition.negPart
    s.toJordanDecomposition.mutuallySingular

/-- The total variation of `ofSignedMeasure s` is Mathlib's `s.totalVariation`. -/
theorem totalVariation_ofSignedMeasure (s : SignedMeasure ℝ) :
    (ofSignedMeasure s).totalVariation = s.totalVariation :=
  rfl

instance (s : SignedMeasure ℝ) : IsFiniteMeasure (ofSignedMeasure s).pos :=
  inferInstanceAs (IsFiniteMeasure s.toJordanDecomposition.posPart)

instance (s : SignedMeasure ℝ) : IsFiniteMeasure (ofSignedMeasure s).neg :=
  inferInstanceAs (IsFiniteMeasure s.toJordanDecomposition.negPart)

/-- `ofSignedMeasure` recovers `s`: its positive part minus its negative part, as signed
measures, is `s` itself. -/
theorem toSignedMeasure_ofSignedMeasure (s : SignedMeasure ℝ) :
    (ofSignedMeasure s).pos.toSignedMeasure - (ofSignedMeasure s).neg.toSignedMeasure = s :=
  s.toSignedMeasure_toJordanDecomposition

/-- The heat flow of `ofSignedMeasure s` integrates against the Jordan parts of `s`. -/
theorem heatFlow_ofSignedMeasure (s : SignedMeasure ℝ) (t x : ℝ) :
    (ofSignedMeasure s).heatFlow t x =
      ∫ y, heatKernel t (x - y) ∂s.toJordanDecomposition.posPart -
        ∫ y, heatKernel t (x - y) ∂s.toJordanDecomposition.negPart :=
  rfl

/-- For a finite signed measure `s`: `|heatFlow t x| ≤ (2πt)^{-1/2} |s|(ℝ)`, with Mathlib's
`s.totalVariation`. -/
theorem abs_heatFlow_ofSignedMeasure_le (s : SignedMeasure ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |(ofSignedMeasure s).heatFlow t x| ≤
      1 / Real.sqrt (2 * Real.pi * t) * (s.totalVariation Set.univ).toReal := by
  have : IsFiniteMeasure (ofSignedMeasure s).totalVariation := by
    rw [totalVariation_ofSignedMeasure]
    infer_instance
  have h := (ofSignedMeasure s).abs_heatFlow_le_of_isFiniteMeasure ht x
  rwa [totalVariation_ofSignedMeasure] at h

/-! ### A genuinely signed example: `δ₀ - δ₁` -/

theorem dirac_zero_mutuallySingular_dirac_one :
    Measure.dirac (0 : ℝ) ⟂ₘ Measure.dirac (1 : ℝ) := by
  refine ⟨{0}ᶜ, (measurableSet_singleton 0).compl, ?_, ?_⟩
  · simp
  · simp

/-- The signed measure `δ₀ - δ₁`. -/
noncomputable def diracZeroSubDiracOne : RoughMeasure :=
  ofFinite (Measure.dirac 0) (Measure.dirac 1) dirac_zero_mutuallySingular_dirac_one

theorem heatFlow_diracZeroSubDiracOne (t x : ℝ) :
    diracZeroSubDiracOne.heatFlow t x = heatKernel t x - heatKernel t (x - 1) := by
  simp [diracZeroSubDiracOne, ofFinite, heatFlow, RoughHeatKernel.heatFlow, integral_dirac]

/-- The heat flow of `δ₀ - δ₁` takes negative values, so the example is genuinely signed. -/
theorem heatFlow_diracZeroSubDiracOne_one_neg {t : ℝ} (ht : 0 < t) :
    diracZeroSubDiracOne.heatFlow t 1 < 0 := by
  rw [heatFlow_diracZeroSubDiracOne, sub_self, heatKernel_zero, sub_neg]
  unfold heatKernel
  have hc : 0 < 1 / Real.sqrt (2 * Real.pi * t) :=
    one_div_pos.mpr (Real.sqrt_pos.mpr (by positivity))
  calc 1 / Real.sqrt (2 * Real.pi * t) * Real.exp (-(1 / (2 * t)) * 1 ^ 2)
      < 1 / Real.sqrt (2 * Real.pi * t) * 1 := by
        apply mul_lt_mul_of_pos_left _ hc
        have hpos : 0 < 1 / (2 * t) := by positivity
        have hneg : -(1 / (2 * t)) * (1 : ℝ) ^ 2 < 0 := by nlinarith
        calc Real.exp (-(1 / (2 * t)) * 1 ^ 2) < Real.exp 0 := Real.exp_lt_exp.mpr hneg
          _ = 1 := Real.exp_zero
    _ = 1 / Real.sqrt (2 * Real.pi * t) := mul_one _

end RoughMeasure

end RoughHeatKernel
