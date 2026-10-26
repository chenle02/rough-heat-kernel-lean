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
namespace RoughHeatKernelTest.NegFlowSemigroup

theorem correct_flow_semigroup (ν : Measure ℝ) [SFinite ν] (t x : ℝ) :
    (∫⁻ s in Set.Ioo 0 t, ∫⁻ y, ENNReal.ofReal (heatKernel (t-s) (x-y)) * lheatFlow ν s y) =
      ENNReal.ofReal t * lheatFlow ν t x :=
  lintegral_lintegral_heatKernel_mul_lheatFlow ν t x

-- The original universally quantified false mutation has a concrete counterexample.
theorem mutated_claim_iff_false : (∀ (ν : Measure ℝ) [SFinite ν] (t x : ℝ), (∫⁻ s in Set.Ioo 0 t, ∫⁻ y, ENNReal.ofReal (heatKernel (t-s) (x-y)) * lheatFlow ν s y) = lheatFlow ν t x) ↔ False := by
  constructor
  · intro h
    have h1 := h (Measure.dirac 0) 2 0
    rw [lintegral_lintegral_heatKernel_mul_lheatFlow] at h1
    rw [lheatFlow_dirac_zero] at h1
    have hp := congrArg ENNReal.toReal h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.toReal_ofReal (heatKernel_pos (by norm_num : (0 : ℝ) < 2) 0).le] at hp
    linarith [heatKernel_pos (by norm_num : (0 : ℝ) < 2) 0]
  · exact False.elim

end RoughHeatKernelTest.NegFlowSemigroup
