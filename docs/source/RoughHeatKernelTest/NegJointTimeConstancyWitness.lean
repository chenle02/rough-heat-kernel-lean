/- Copyright (c) 2026 Le Chen. Apache-2.0. -/
module

public import RoughHeatKernel

public section
noncomputable section
set_option autoImplicit false
open RoughHeatKernel MeasureTheory
open scoped ENNReal
namespace RoughHeatKernelTest.NegJointTimeConstancy

theorem dirac_nonzero_time_increment :
    (RoughMeasure.dirac 0).heatFlow 4 0 = (1/2:ℝ)*(RoughMeasure.dirac 0).heatFlow 1 0 ∧
      (RoughMeasure.dirac 0).heatFlow 4 0 ≠ (RoughMeasure.dirac 0).heatFlow 1 0 := by
  have he : Real.sqrt (2*Real.pi*4)=2*Real.sqrt (2*Real.pi*1) := by
    rw [show 2*Real.pi*4=4*(2*Real.pi*1) by ring,Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
    rw [show Real.sqrt (4 : ℝ) = 2 from
      (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)]
  have hhalf : heatKernel 4 0=(1/2:ℝ)*heatKernel 1 0 := by
    rw [heatKernel_zero,heatKernel_zero,he]
    ring
  have h4 : (RoughMeasure.dirac 0).heatFlow 4 0=heatKernel 4 0 := by
    simpa only [sub_zero] using RoughMeasure.heatFlow_dirac 0 4 0
  have h1 : (RoughMeasure.dirac 0).heatFlow 1 0=heatKernel 1 0 := by
    simpa only [sub_zero] using RoughMeasure.heatFlow_dirac 0 1 0
  rw [h4,h1]
  refine ⟨hhalf,?_⟩
  intro h
  linarith [heatKernel_pos (by norm_num : (0:ℝ)<1) 0]

theorem correct_joint (μ : RoughMeasure) (a : ℝ × ℝ) (ha : 0 < a.1) :
    ContinuousAt (fun z : ℝ × ℝ => μ.heatFlow z.1 z.2) a :=
  RoughMeasure.continuousAt_heatFlow_joint μ a ha

theorem mutated_claim_iff_false :
    (∀ μ : RoughMeasure, ∀ t : ℝ, 0 < t → ∀ x : ℝ, μ.heatFlow t x = μ.heatFlow 1 x) ↔ False := by
  constructor
  · intro h
    exact dirac_nonzero_time_increment.2 (h (RoughMeasure.dirac 0) 4 (by norm_num) 0)
  · exact False.elim
end RoughHeatKernelTest.NegJointTimeConstancy
