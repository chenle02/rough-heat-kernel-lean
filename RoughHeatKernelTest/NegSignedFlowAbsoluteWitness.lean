/- Copyright (c) 2026 Le Chen. Apache-2.0. -/
module

public import RoughHeatKernel

public section
noncomputable section
set_option autoImplicit false
open RoughHeatKernel MeasureTheory
open scoped ENNReal
namespace RoughHeatKernelTest.NegSignedFlowAbsolute

theorem signed_cancellation {t : ℝ} (ht : 0<t) :
    RoughMeasure.diracZeroSubDiracOne.heatFlow t (1/2)=0 ∧
      0<RoughHeatKernel.heatFlow RoughMeasure.diracZeroSubDiracOne.totalVariation t (1/2) := by
  have hs : heatKernel t ((1/2:ℝ)-1)=heatKernel t (1/2) := by
    rw [show (1/2:ℝ)-1= -(1/2:ℝ) by ring,heatKernel_neg]
  constructor
  · change RoughMeasure.diracZeroSubDiracOne.heatFlow t (1/2)=0
    rw [RoughMeasure.heatFlow_diracZeroSubDiracOne,hs,sub_self]
  · change 0<RoughHeatKernel.heatFlow RoughMeasure.diracZeroSubDiracOne.totalVariation t (1/2)
    rw [RoughMeasure.heatFlow_totalVariation RoughMeasure.diracZeroSubDiracOne ht (1/2)]
    simp only [RoughMeasure.diracZeroSubDiracOne,RoughMeasure.ofFinite,
      RoughHeatKernel.heatFlow,integral_dirac,sub_zero]
    rw [hs]
    linarith [heatKernel_pos ht (1/2)]

theorem correct_signed_joint (μ : RoughMeasure) (a : ℝ × ℝ) (ha : 0 < a.1) :
    ContinuousAt (fun z : ℝ × ℝ => μ.heatFlow z.1 z.2) a :=
  RoughMeasure.continuousAt_heatFlow_joint μ a ha

theorem mutated_claim_iff_false :
    (∀ μ : RoughMeasure, ∀ t : ℝ, 0 < t → ∀ x : ℝ,
      μ.heatFlow t x = RoughHeatKernel.heatFlow μ.totalVariation t x) ↔ False := by
  constructor
  · intro h
    have hc := signed_cancellation (by norm_num : (0 : ℝ) < 1)
    have he := h RoughMeasure.diracZeroSubDiracOne 1 (by norm_num) (1/2)
    linarith [hc.1, hc.2]
  · exact False.elim
end RoughHeatKernelTest.NegSignedFlowAbsolute
