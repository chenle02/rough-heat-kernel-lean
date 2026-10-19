/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Challenge.Reference.RoughHeatKernel.Tempered

/-!
# Rough signed initial data

A rough measure is a signed Borel measure `μ = μ₊ - μ₋` on `ℝ` whose total variation
`|μ| = μ₊ + μ₋` is Gaussian-tempered. Such a `μ` may have infinite total variation, so
it is recorded through its Jordan decomposition: two mutually singular positive measures,
each Gaussian-tempered. (Mathlib's `SignedMeasure` is finite-valued and cannot represent
these.) Mutual singularity is what makes `μ₊ + μ₋` the total variation.

The heat flow of `μ` is `heatFlow μ₊ - heatFlow μ₋`. It is continuous in `x` for `t > 0`,
and bounded in absolute value by the heat flow of `|μ|`.
-/

set_option autoImplicit false

open MeasureTheory

namespace RoughHeatKernel

/-- A signed measure on `ℝ` with Gaussian-tempered total variation, given by its Jordan
decomposition `pos - neg`. -/
structure RoughMeasure where
  /-- The positive part `μ₊`. -/
  pos : Measure ℝ
  /-- The negative part `μ₋`. -/
  neg : Measure ℝ
  /-- Jordan decomposition: the parts are mutually singular. -/
  mutuallySingular : pos ⟂ₘ neg
  pos_tempered : IsGaussianTempered pos
  neg_tempered : IsGaussianTempered neg

namespace RoughMeasure

/-- The total variation `|μ| = μ₊ + μ₋`. -/
def totalVariation (μ : RoughMeasure) : Measure ℝ := μ.pos + μ.neg

theorem totalVariation_tempered (μ : RoughMeasure) : IsGaussianTempered μ.totalVariation :=
  μ.pos_tempered.add μ.neg_tempered

/-- The heat flow `∫ p_t(x - y) μ(dy) = heatFlow μ₊ t x - heatFlow μ₋ t x`. -/
noncomputable def heatFlow (μ : RoughMeasure) (t x : ℝ) : ℝ :=
  RoughHeatKernel.heatFlow μ.pos t x - RoughHeatKernel.heatFlow μ.neg t x

theorem continuous_heatFlow (μ : RoughMeasure) {t : ℝ} (ht : 0 < t) :
    Continuous (μ.heatFlow t) :=
  (RoughHeatKernel.continuous_heatFlow μ.pos_tempered ht).sub
    (RoughHeatKernel.continuous_heatFlow μ.neg_tempered ht)

/-- Joint positive-time continuity for signed Gaussian-tempered Jordan data. -/
theorem continuousAt_heatFlow_joint (μ : RoughMeasure) (a : ℝ × ℝ) (ha : 0 < a.1) :
    ContinuousAt (fun z : ℝ × ℝ => μ.heatFlow z.1 z.2) a := by
  exact (RoughHeatKernel.continuousAt_heatFlow_joint μ.pos_tempered a ha).sub
    (RoughHeatKernel.continuousAt_heatFlow_joint μ.neg_tempered a ha)

theorem heatFlow_totalVariation (μ : RoughMeasure) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    RoughHeatKernel.heatFlow μ.totalVariation t x =
      RoughHeatKernel.heatFlow μ.pos t x + RoughHeatKernel.heatFlow μ.neg t x :=
  integral_add_measure (μ.pos_tempered.integrable_heatKernel_sub ht x)
    (μ.neg_tempered.integrable_heatKernel_sub ht x)

/-- `|heatFlow μ t x| ≤ heatFlow |μ| t x`. -/
theorem abs_heatFlow_le (μ : RoughMeasure) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |μ.heatFlow t x| ≤ RoughHeatKernel.heatFlow μ.totalVariation t x := by
  rw [heatFlow_totalVariation μ ht x]
  have hp := heatFlow_nonneg μ.pos ht x
  have hn := heatFlow_nonneg μ.neg ht x
  unfold heatFlow
  rw [abs_le]
  constructor <;> linarith

/-- A Jordan pair whose total variation `pos + neg` is Gaussian-tempered is a rough
measure. This is the single-condition form of the class. -/
def ofTempered (pos neg : Measure ℝ) (h : pos ⟂ₘ neg)
    (hE : IsGaussianTempered (pos + neg)) : RoughMeasure where
  pos := pos
  neg := neg
  mutuallySingular := h
  pos_tempered := hE.mono (Measure.le_add_right le_rfl)
  neg_tempered := hE.mono (Measure.le_add_left le_rfl)

theorem totalVariation_ofTempered (pos neg : Measure ℝ) (h : pos ⟂ₘ neg)
    (hE : IsGaussianTempered (pos + neg)) :
    (ofTempered pos neg h hE).totalVariation = pos + neg :=
  rfl

/-- A Gaussian-tempered positive measure, as a rough measure with zero negative part. -/
def ofPositive (ν : Measure ℝ) (hν : IsGaussianTempered ν) : RoughMeasure where
  pos := ν
  neg := 0
  mutuallySingular := Measure.MutuallySingular.zero_right
  pos_tempered := hν
  neg_tempered _ _ := by simp

theorem heatFlow_ofPositive (ν : Measure ℝ) (hν : IsGaussianTempered ν) (t x : ℝ) :
    (ofPositive ν hν).heatFlow t x = RoughHeatKernel.heatFlow ν t x := by
  simp [heatFlow, ofPositive, RoughHeatKernel.heatFlow]

/-- The Dirac mass `δ_{x₀}`. -/
noncomputable def dirac (x₀ : ℝ) : RoughMeasure :=
  ofPositive (Measure.dirac x₀) (isGaussianTempered_dirac x₀)

/-- The heat flow of `δ_{x₀}` is `p_t(· - x₀)`. -/
theorem heatFlow_dirac (x₀ t x : ℝ) : (dirac x₀).heatFlow t x = heatKernel t (x - x₀) := by
  simp [dirac, heatFlow_ofPositive, RoughHeatKernel.heatFlow, integral_dirac]

/-- Lebesgue measure, a rough measure of infinite total variation. -/
noncomputable def lebesgue : RoughMeasure :=
  ofPositive volume isGaussianTempered_volume

theorem lebesgue_totalVariation_univ : lebesgue.totalVariation Set.univ = ⊤ := by
  simp [totalVariation, lebesgue, ofPositive]

/-- The heat flow of Lebesgue measure is identically `1`. -/
theorem heatFlow_lebesgue {t : ℝ} (ht : 0 < t) (x : ℝ) : lebesgue.heatFlow t x = 1 := by
  rw [lebesgue, heatFlow_ofPositive, RoughHeatKernel.heatFlow,
    integral_sub_left_eq_self (μ := (volume : Measure ℝ)) (heatKernel t) x]
  exact integral_heatKernel ht

end RoughMeasure

end RoughHeatKernel
