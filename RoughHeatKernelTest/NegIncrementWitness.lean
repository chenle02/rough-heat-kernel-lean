/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import RoughHeatKernelTest.Counterexamples

open RoughHeatKernel MeasureTheory RoughHeatKernelTest.Counterexamples
open scoped ENNReal
namespace RoughHeatKernelTest.NegIncrement

theorem correct_time_increment {t ε : ℝ} (ht : 0 < t) (hε : 0 ≤ ε) (x : ℝ) :
    (∫ y, |heatKernel (t+ε) (x-y) - heatKernel t (x-y)|) ≤ min 2 (ε/t) :=
  integral_abs_heatKernel_add_sub_le ht hε x

-- The original universally quantified false mutation has a concrete counterexample.
theorem mutated_claim_iff_false : (∀ (t : ℝ), 0 < t → (∫ y : ℝ, |heatKernel (t + 1) (0 - y) - heatKernel t (0 - y)|) ≤ 0) ↔ False := by
  constructor
  · intro h
    have h1 := h 1 (by norm_num)
    norm_num only [one_add_one_eq_two] at h1
    exact (not_le_of_gt time_increment_positive) h1
  · exact False.elim

end RoughHeatKernelTest.NegIncrement
