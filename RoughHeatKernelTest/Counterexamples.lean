/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
module

public import RoughHeatKernel

public section

open RoughHeatKernel MeasureTheory
open scoped ENNReal
namespace RoughHeatKernelTest.Counterexamples

theorem peak_strict_antitone {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    heatKernel t 0 < heatKernel s 0 := by
  rw [heatKernel_zero, heatKernel_zero]
  exact one_div_lt_one_div_of_lt (Real.sqrt_pos.mpr (by positivity))
    (Real.sqrt_lt_sqrt (by positivity) (by nlinarith [Real.pi_pos]))

theorem off_center_strict : heatKernel 1 1 < heatKernel 1 0 := by
  rw [heatKernel_zero]
  unfold heatKernel
  have hc : 0 < 1 / Real.sqrt (2 * Real.pi * 1) := by positivity
  have he : Real.exp (-(1 / (2 * (1 : ℝ))) * 1 ^ 2) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  nlinarith

theorem lheatFlow_dirac_zero (t x : ℝ) :
    lheatFlow (Measure.dirac (0 : ℝ)) t x = ENNReal.ofReal (heatKernel t x) := by
  simp [lheatFlow]

theorem time_increment_positive :
    0 < ∫ y : ℝ, |heatKernel 2 (0 - y) - heatKernel 1 (0 - y)| := by
  apply integral_pos_of_integrable_nonneg_nonzero (x := (0 : ℝ))
    (((continuous_heatKernel 2).comp (continuous_const.sub continuous_id)).sub
      ((continuous_heatKernel 1).comp (continuous_const.sub continuous_id))).abs
    (((integrable_heatKernel (by norm_num : (0 : ℝ) < 2)).comp_sub_left 0).sub
      ((integrable_heatKernel (by norm_num : (0 : ℝ) < 1)).comp_sub_left 0)).abs
    (fun _ => abs_nonneg _)
  have h := peak_strict_antitone (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)
  simpa using abs_ne_zero.mpr (sub_ne_zero.mpr (ne_of_lt h))

end RoughHeatKernelTest.Counterexamples
