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
namespace RoughHeatKernelTest.NegDoubledSemigroup

theorem correct_doubled_semigroup (ν : Measure ℝ) [SFinite ν] {s t : ℝ}
    (hs : 0 < s) (hst : s < t) (x : ℝ) :
    (∫⁻ y, ENNReal.ofReal (heatKernel (t-s) (x-y)) * lheatFlow ν (2*s) y) = lheatFlow ν (t+s) x :=
  lintegral_heatKernel_mul_lheatFlow_two_mul ν hs hst x

-- The original universally quantified false mutation has a concrete counterexample.
theorem mutated_claim_iff_false : (∀ (ν : Measure ℝ) [SFinite ν] (s t : ℝ), 0 < s → s < t → ∀ x : ℝ, (∫⁻ y, ENNReal.ofReal (heatKernel (t-s) (x-y)) * lheatFlow ν (2*s) y) = lheatFlow ν (2*t) x) ↔ False := by
  constructor
  · intro h
    have h1 := h (Measure.dirac 0) 1 2 (by norm_num) (by norm_num) 0
    rw [lintegral_heatKernel_mul_lheatFlow_two_mul (Measure.dirac 0)
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)] at h1
    simp only [lheatFlow_dirac_zero] at h1
    have hp := congrArg ENNReal.toReal h1
    simp only [ENNReal.toReal_ofReal (heatKernel_pos (by norm_num : (0 : ℝ) < 2+1) 0).le,
      ENNReal.toReal_ofReal (heatKernel_pos (by norm_num : (0 : ℝ) < 2*2) 0).le] at hp
    norm_num only [show (2:ℝ)+1=3 by norm_num, show (2:ℝ)*2=4 by norm_num] at hp
    exact (ne_of_gt (peak_strict_antitone (by norm_num) (by norm_num : (3 : ℝ) < 4))) hp
  · exact False.elim

end RoughHeatKernelTest.NegDoubledSemigroup
