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
namespace RoughHeatKernelTest.NegArcsine

theorem correct_arcsine {t : ℝ} (ht : 0 < t) :
    (∫⁻ s in Set.Ioo 0 t, ENNReal.ofReal (1 / Real.sqrt (s * (t - s)))) = ENNReal.ofReal Real.pi :=
  lintegral_arcsine ht

-- The original universally quantified false mutation has a concrete counterexample.
theorem mutated_claim_iff_false : (∀ (t : ℝ), 0 < t → (∫⁻ s in Set.Ioo 0 t, ENNReal.ofReal (1 / Real.sqrt (s * (t - s)))) = ENNReal.ofReal (Real.pi / 2)) ↔ False := by
  constructor
  · intro h
    have h1 := h 1 (by norm_num)
    rw [lintegral_arcsine (by norm_num : (0 : ℝ) < 1)] at h1
    have hp := congrArg ENNReal.toReal h1
    simp only [ENNReal.toReal_ofReal Real.pi_pos.le,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi / 2)] at hp
    linarith [Real.pi_pos]
  · exact False.elim

end RoughHeatKernelTest.NegArcsine
