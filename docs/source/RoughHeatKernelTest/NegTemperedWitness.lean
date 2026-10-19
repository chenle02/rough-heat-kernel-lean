/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import RoughHeatKernelTest.Counterexamples

open RoughHeatKernel MeasureTheory RoughHeatKernelTest.Counterexamples
open scoped ENNReal
namespace RoughHeatKernelTest.NegTempered

theorem correct_tempered_finite (ν : Measure ℝ) [IsFiniteMeasure ν] : IsGaussianTempered ν :=
  isGaussianTempered_of_isFiniteMeasure ν

theorem correct_tempered_infinite_mass : IsGaussianTempered (volume : Measure ℝ) :=
  isGaussianTempered_volume

-- The original universally quantified false mutation has a concrete counterexample.
theorem mutated_claim_iff_false : (∀ ν : Measure ℝ, IsGaussianTempered ν) ↔ False := by
  constructor
  · intro h
    have h1 := h ((⊤ : ℝ≥0∞) • Measure.dirac (0 : ℝ)) 1 (by norm_num)
    simp [lintegral_smul_measure] at h1
  · exact False.elim

end RoughHeatKernelTest.NegTempered
