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
namespace RoughHeatKernelTest.NegProductIdentity

theorem correct_product {t : ℝ} (ht : 0 < t) (y z₁ z₂ : ℝ) :
    heatKernel t (y-z₁) * heatKernel t (y-z₂) =
      heatKernel (2*t) (z₁-z₂) * heatKernel (t/2) (y-(z₁+z₂)/2) :=
  heatKernel_mul_heatKernel_eq ht y z₁ z₂

-- The original universally quantified false mutation has a concrete counterexample.
theorem mutated_claim_iff_false : (∀ (t : ℝ), 0 < t → ∀ y z₁ z₂ : ℝ, heatKernel t (y-z₁) * heatKernel t (y-z₂) = heatKernel t (z₁-z₂) * heatKernel (t/2) (y-(z₁+z₂)/2)) ↔ False := by
  constructor
  · intro h
    have h1 := h 1 (by norm_num) 0 0 0
    rw [heatKernel_mul_heatKernel_eq (by norm_num : (0 : ℝ) < 1)] at h1
    norm_num only [sub_zero, zero_add, zero_div, mul_one] at h1
    have hc : heatKernel 2 0 = heatKernel 1 0 :=
      mul_right_cancel₀ (heatKernel_pos (by norm_num : (0 : ℝ) < 1/2) 0).ne' h1
    exact (ne_of_lt (peak_strict_antitone (by norm_num) (by norm_num : (1 : ℝ) < 2))) hc
  · exact False.elim

end RoughHeatKernelTest.NegProductIdentity
