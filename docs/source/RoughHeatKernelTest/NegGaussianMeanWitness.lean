/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
module

public import RoughHeatKernelTest.Counterexamples

public section

open RoughHeatKernel MeasureTheory RoughHeatKernelTest.Counterexamples
open scoped ENNReal
namespace RoughHeatKernelTest.NegGaussianMean

theorem correct_gaussian_mean (t x : ℝ) :
    heatKernel t x = ProbabilityTheory.gaussianPDFReal 0 t.toNNReal x :=
  heatKernel_eq_gaussianPDFReal t x

-- The original universally quantified false mutation has a concrete counterexample.
theorem mutated_claim_iff_false : (∀ (t x : ℝ), heatKernel t x = ProbabilityTheory.gaussianPDFReal 1 t.toNNReal x) ↔ False := by
  constructor
  · intro h
    have h1 := h 1 0
    rw [gaussianPDFReal_eq_heatKernel_sub] at h1
    norm_num only [Real.toNNReal_one, NNReal.coe_one, sub_zero] at h1
    exact (ne_of_gt off_center_strict) h1
  · exact False.elim

end RoughHeatKernelTest.NegGaussianMean
