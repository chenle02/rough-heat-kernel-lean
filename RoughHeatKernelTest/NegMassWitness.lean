/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import RoughHeatKernelTest.Counterexamples

open RoughHeatKernel MeasureTheory RoughHeatKernelTest.Counterexamples
open scoped ENNReal
namespace RoughHeatKernelTest.NegMass

theorem correct_mass {t : ℝ} (ht : 0 < t) : ∫ x, heatKernel t x = 1 :=
  integral_heatKernel ht

-- The original universally quantified false mutation has a concrete counterexample.
theorem mutated_claim_iff_false : (∀ (t : ℝ), 0 < t → ∫ x, heatKernel t x = 2) ↔ False := by
  constructor
  · intro h
    have h1 := h 1 (by norm_num)
    rw [integral_heatKernel (by norm_num : (0 : ℝ) < 1)] at h1
    norm_num at h1
  · exact False.elim

end RoughHeatKernelTest.NegMass
