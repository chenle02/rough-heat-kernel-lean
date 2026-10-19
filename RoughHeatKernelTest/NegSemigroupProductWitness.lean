/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import RoughHeatKernelTest.Counterexamples

open RoughHeatKernel MeasureTheory RoughHeatKernelTest.Counterexamples
open scoped ENNReal
namespace RoughHeatKernelTest.NegSemigroupProduct

theorem correct_semigroup {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x : ℝ) :
    (∫ y, heatKernel t (x-y) * heatKernel s y) = heatKernel (t+s) x :=
  integral_heatKernel_mul_heatKernel hs ht x

-- The original universally quantified false mutation has a concrete counterexample.
theorem mutated_claim_iff_false : (∀ (s t : ℝ), 0 < s → 0 < t → ∀ x : ℝ, (∫ y, heatKernel t (x - y) * heatKernel s y) = heatKernel (t * s) x) ↔ False := by
  constructor
  · intro h
    have h1 := h 1 1 (by norm_num) (by norm_num) 0
    rw [integral_heatKernel_mul_heatKernel (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1)] at h1
    norm_num only [one_add_one_eq_two, one_mul] at h1
    exact (ne_of_lt (peak_strict_antitone (by norm_num) (by norm_num : (1 : ℝ) < 2))) h1
  · exact False.elim

end RoughHeatKernelTest.NegSemigroupProduct
