/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
module

public import RoughHeatKernelChallenge.Reference.RoughHeatKernel.CausalHeatKernel
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Weighted continuity of the causal heat kernel

A Gaussian comparison controls nearby output kernels by a fixed later-output
kernel outside a compact input rectangle. Finite weighted variance at that
later output and a finite bound on the weight inside the rectangle imply
joint weighted L² continuity at every positive output time.

The weight takes values in the extended nonnegative reals and may be infinite
outside the active integration region. Its required almost-everywhere finiteness
is derived from the finite future variance and strict Gaussian positivity.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace RoughHeatKernel.WeightedCausalHeatKernel

open Real MeasureTheory Filter Set CausalHeatKernel
open scoped ENNReal Topology

private theorem heatKernel_sq_le_of_scalar_margin {ν r R d e : ℝ}
    (hν : 0 < ν) (hr : 0 < r) (hR : 0 < R)
    (hrR : r ≤ 4 * R / 7)
    (hde : 3 * d ^ 2 / 4 - 3 ≤ e ^ 2)
    (hlarge : ν * R ≤ 5 * d ^ 2 / 28 - 3) :
    RoughHeatKernel.heatKernel (ν * r) e ^ 2 ≤
      RoughHeatKernel.heatKernel (ν * R) d ^ 2 := by
  let A := (5 * d ^ 2 / 28 - 3) / ν
  have hRA : R ≤ A := by
    dsimp only [A]
    exact (le_div_iff₀ hν).mpr (by nlinarith [hlarge])
  have hnum : r * d ^ 2 - R * e ^ 2 + R * (5 * d ^ 2 / 28 - 3) ≤ 0 := by
    nlinarith [mul_nonneg (show 0 ≤ 4 * R - 7 * r by linarith) (sq_nonneg d),
      mul_le_mul_of_nonneg_left hde hR.le]
  have hidentity :
      -e ^ 2 / (ν * r) - (-d ^ 2 / (ν * R) - A / r) =
        (r * d ^ 2 - R * e ^ 2 + R * (5 * d ^ 2 / 28 - 3)) / (ν * r * R) := by
    dsimp only [A]
    field_simp; ring
  have hexponent : -e ^ 2 / (ν * r) ≤ -d ^ 2 / (ν * R) - A / r := by
    have hq := div_nonpos_of_nonpos_of_nonneg hnum (by positivity : 0 ≤ ν * r * R)
    rw [← hidentity] at hq
    linarith
  have hratio : R / r * Real.exp (-A / r) ≤ 1 := by
    calc
      R / r * Real.exp (-A / r) ≤ A / r * Real.exp (-(A / r)) := by
        rw [neg_div]
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hRA hr.le) (Real.exp_pos _).le
      _ ≤ Real.exp (-1) := Real.mul_exp_neg_le_exp_neg_one _
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  rw [RoughHeatKernel.heatKernel_sq_exp (mul_pos hν hr),
    RoughHeatKernel.heatKernel_sq_exp (mul_pos hν hR)]
  calc
    1 / (2 * π * (ν * r)) * Real.exp (-e ^ 2 / (ν * r)) ≤
        1 / (2 * π * (ν * r)) *
          (Real.exp (-d ^ 2 / (ν * R)) * Real.exp (-A / r)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by
        simpa only [neg_div, sub_eq_add_neg] using hexponent)
    _ = (1 / (2 * π * (ν * R)) * Real.exp (-d ^ 2 / (ν * R))) *
        (R / r * Real.exp (-A / r)) := by
      field_simp
    _ ≤ (1 / (2 * π * (ν * R)) * Real.exp (-d ^ 2 / (ν * R))) * 1 :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := mul_one _

/-- Far-space Gaussian domination for nearby output points. The diffusivity
is unchanged and the dominating kernel has the fixed later output time `2*t`.
All constants are derived from the displayed hypotheses. -/
theorem heatKernel_sq_le_future_of_far {ν t t' x x' s y : ℝ}
    (hν : 0 < ν) (ht : 0 < t)
    (_ht'lo : 3 * t / 4 ≤ t') (ht'hi : t' ≤ 5 * t / 4)
    (hx : |x' - x| ≤ 1) (hslo : t / 4 ≤ s) (hshi : s < t')
    (hy : |x| + 8 * (1 + ν * t) ≤ |y|) :
    RoughHeatKernel.heatKernel (ν * (t' - s)) (x' - y) ^ 2 ≤
      RoughHeatKernel.heatKernel (ν * (2 * t - s)) (x - y) ^ 2 := by
  have hs : 0 ≤ s := by linarith
  have hr : 0 < t' - s := sub_pos.mpr hshi
  have hR : 0 < 2 * t - s := by linarith
  have hrR : t' - s ≤ 4 * (2 * t - s) / 7 := by linarith
  have hδ : (x' - x) ^ 2 ≤ 1 := by
    have hh := (sq_le_sq₀ (abs_nonneg (x' - x)) (by norm_num : (0 : ℝ) ≤ 1)).mpr hx
    simpa only [sq_abs, one_pow] using hh
  have hde : 3 * (x - y) ^ 2 / 4 - 3 ≤ (x' - y) ^ 2 := by
    nlinarith [sq_nonneg ((x - y) / 2 + 2 * (x' - x))]
  have habs : |y| ≤ |x| + |x - y| := by
    calc
      |y| = |x + (y - x)| := by congr 1; ring
      _ ≤ |x| + |y - x| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm]
  have hrad : 8 * (1 + ν * t) ≤ |x - y| := by linarith
  have hνt : 0 ≤ ν * t := (mul_pos hν ht).le
  have hrad2 : (8 * (1 + ν * t)) ^ 2 ≤ (x - y) ^ 2 := by
    have hh := (sq_le_sq₀ (by positivity : 0 ≤ 8 * (1 + ν * t))
      (abs_nonneg (x - y))).mpr hrad
    simpa only [sq_abs] using hh
  have hlarge : ν * (2 * t - s) ≤ 5 * (x - y) ^ 2 / 28 - 3 := by
    have hleft : ν * (2 * t - s) ≤ 2 * ν * t := by nlinarith
    nlinarith [sq_nonneg (ν * t)]
  exact heatKernel_sq_le_of_scalar_margin hν hr hR hrR hde hlarge


private theorem heatK_sq_le_future_early {ν t t' x x' s y : ℝ}
    (hν : 0 < ν) (ht : 0 < t)
    (htlo : 3 * t / 4 ≤ t') (hthi : t' ≤ 5 * t / 4)
    (hx : |x' - x| ≤ 1) (_hslo : 0 ≤ s) (hshi : s ≤ t / 4) :
    heatK ν t' x' s y ^ 2 ≤
      (4 * Real.exp (6 / (ν * t))) * heatK ν (2 * t) x s y ^ 2 := by
  by_cases hs : 0 < s
  · have hst' : s < t' := by linarith
    have hst : s < 2 * t := by linarith
    rw [heatK_of ⟨hs, hst'⟩, heatK_of ⟨hs, hst⟩]
    have h := RoughHeatKernel.heatKernel_sq_le_local
      (t := ν * t) (u := ν * t') (s := ν * s) (x := x') (z := x) (y := y)
      (mul_pos hν ht) (by nlinarith) (by nlinarith) (by positivity) (by nlinarith) hx
    simpa only [show ν * t' - ν * s = ν * (t' - s) by ring,
      show 2 * (ν * t) - ν * s = ν * (2 * t - s) by ring] using h
  · rw [heatK_causal ν t' x' s y (Or.inl (not_lt.mp hs)),
      zero_pow two_ne_zero]
    positivity

private theorem heatK_sq_le_future_offCompact {ν t t' x x' s y : ℝ}
    (hν : 0 < ν) (ht : 0 < t)
    (htlo : 3 * t / 4 ≤ t') (hthi : t' ≤ 5 * t / 4)
    (hx : |x' - x| ≤ 1)
    (hoff : (s, y) ∉ Icc (t / 4) (5 * t / 4) ×ˢ
      Icc (-(|x| + 8 * (1 + ν * t))) (|x| + 8 * (1 + ν * t))) :
    heatK ν t' x' s y ^ 2 ≤
      (4 * Real.exp (6 / (ν * t))) * heatK ν (2 * t) x s y ^ 2 := by
  by_cases hs : 0 < s
  · by_cases hst' : s < t'
    · by_cases hearly : s ≤ t / 4
      · exact heatK_sq_le_future_early hν ht htlo hthi hx hs.le hearly
      · have hfar : |x| + 8 * (1 + ν * t) ≤ |y| := by
          by_contra h
          have hy : |y| ≤ |x| + 8 * (1 + ν * t) := (lt_of_not_ge h).le
          exact hoff ⟨⟨(not_le.mp hearly).le, by linarith⟩, abs_le.mp hy⟩
        have hst : s < 2 * t := by linarith
        have hm := heatKernel_sq_le_future_of_far hν ht htlo hthi hx
          (not_le.mp hearly).le hst' hfar
        have hkernel : heatK ν t' x' s y ^ 2 ≤ heatK ν (2 * t) x s y ^ 2 := by
          simpa only [heatK_of ⟨hs, hst'⟩, heatK_of ⟨hs, hst⟩] using hm
        have hC : (1 : ℝ) ≤ 4 * Real.exp (6 / (ν * t)) := by
          have hh : 1 ≤ Real.exp (6 / (ν * t)) := Real.one_le_exp_iff.mpr (by positivity)
          linarith
        exact hkernel.trans (by nlinarith [sq_nonneg (heatK ν (2 * t) x s y)])
    · rw [heatK_causal ν t' x' s y (Or.inr (not_lt.mp hst')), zero_pow two_ne_zero]
      positivity
  · rw [heatK_causal ν t' x' s y (Or.inl (not_lt.mp hs)), zero_pow two_ne_zero]
    positivity

/-- Finite future variance and a finite bound on the displayed compact input
rectangle imply joint weighted kernel continuity at a positive output point.
The weight may be infinite elsewhere; its needed a.e. finiteness is derived. -/
theorem tendsto_weighted_sq_difference {ν t x : ℝ}
    (hν : 0 < ν) (ht : 0 < t) (w : ℝ × ℝ → ℝ≥0∞) (hw : Measurable w)
    (hfuture : (∫⁻ q : ℝ × ℝ,
      ENNReal.ofReal (heatK ν (2 * t) x q.1 q.2 ^ 2) * w q ∂positiveTimeSpaceVolume) < ⊤)
    (hcompact : ∃ B : ℝ≥0∞, B < ⊤ ∧
      ∀ q ∈ Icc (t / 4) (5 * t / 4) ×ˢ
        Icc (-(|x| + 8 * (1 + ν * t))) (|x| + 8 * (1 + ν * t)), w q ≤ B) :
    Tendsto (fun z : ℝ × ℝ => ∫⁻ q : ℝ × ℝ,
      ENNReal.ofReal ((heatK ν z.1 z.2 q.1 q.2 - heatK ν t x q.1 q.2) ^ 2) * w q
        ∂positiveTimeSpaceVolume) (𝓝 (t, x)) (𝓝 0) := by
  classical
  let K : Set (ℝ × ℝ) := Icc (t / 4) (5 * t / 4) ×ˢ
    Icc (-(|x| + 8 * (1 + ν * t))) (|x| + 8 * (1 + ν * t))
  let d := fun (z q : ℝ × ℝ) =>
    ENNReal.ofReal ((heatK ν z.1 z.2 q.1 q.2 - heatK ν t x q.1 q.2) ^ 2)
  let f := fun (z q : ℝ × ℝ) => d z q * w q
  let A := fun q : ℝ × ℝ => ENNReal.ofReal (heatK ν (2 * t) x q.1 q.2 ^ 2) * w q
  let C : ℝ := 4 * Real.exp (6 / (ν * t))
  let D : ℝ≥0∞ := ENNReal.ofReal (4 * C)
  have hKm : MeasurableSet K := measurableSet_Icc.prod measurableSet_Icc
  have hdm (z : ℝ × ℝ) : Measurable (d z) :=
    (((measurable_heatK_section ν z.1 z.2).sub
      (measurable_heatK_section ν t x)).pow_const 2).ennreal_ofReal
  have hfm (z : ℝ × ℝ) : Measurable (f z) := (hdm z).mul hw
  have hAm : Measurable A :=
    (((measurable_heatK_section ν (2 * t) x).pow_const 2).ennreal_ofReal).mul hw
  obtain ⟨B, hB, hBbound⟩ := hcompact
  have hKbound (z : ℝ × ℝ) :
      (∫⁻ q, K.indicator (f z) q ∂positiveTimeSpaceVolume) ≤
        B * ∫⁻ q, d z q ∂positiveTimeSpaceVolume := by
    calc
      _ ≤ ∫⁻ q, B * d z q ∂positiveTimeSpaceVolume := by
        apply lintegral_mono
        intro q
        by_cases hq : q ∈ K
        · rw [Set.indicator_of_mem hq]
          change d z q * w q ≤ B * d z q
          exact (mul_le_mul le_rfl (hBbound q hq) bot_le bot_le).trans_eq (mul_comm _ _)
        · rw [Set.indicator_of_notMem hq]
          exact bot_le
      _ = _ := lintegral_const_mul _ (hdm z)
  have hKlim : Tendsto (fun z : ℝ × ℝ => ∫⁻ q, K.indicator (f z) q ∂positiveTimeSpaceVolume)
      (𝓝 (t, x)) (𝓝 0) := by
    have hup : Tendsto (fun z : ℝ × ℝ => B * ∫⁻ q, d z q ∂positiveTimeSpaceVolume)
        (𝓝 (t, x)) (𝓝 0) := by
      simpa only [mul_zero] using
        ENNReal.Tendsto.const_mul (tendsto_heatK_sq hν (t, x)) (Or.inr hB.ne)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun _ => bot_le) hKbound
  have hev : ∀ᶠ z : ℝ × ℝ in 𝓝 (t, x),
      3 * t / 4 ≤ z.1 ∧ z.1 ≤ 5 * t / 4 ∧ |z.2 - x| ≤ 1 := by
    have htime : ∀ᶠ z : ℝ × ℝ in 𝓝 (t, x), z.1 ∈ Icc (3 * t / 4) (5 * t / 4) :=
      (continuous_fst.tendsto (t, x)).eventually
        (Icc_mem_nhds (by linarith) (by linarith))
    have hspace : ∀ᶠ z : ℝ × ℝ in 𝓝 (t, x), |z.2 - x| ≤ 1 := by
      have hh : ∀ᶠ r in 𝓝 x, |r - x| ≤ 1 := by
        filter_upwards [Metric.closedBall_mem_nhds x one_pos] with r hr
        simpa only [Metric.mem_closedBall, Real.dist_eq] using hr
      exact (continuous_snd.tendsto (t, x)).eventually hh
    filter_upwards [htime, hspace] with z hz hx
    exact ⟨hz.1, hz.2, hx⟩
  have hOffbound : ∀ᶠ z : ℝ × ℝ in 𝓝 (t, x),
      ∀ᵐ q ∂positiveTimeSpaceVolume, Kᶜ.indicator (f z) q ≤ D * A q := by
    filter_upwards [hev] with z hz
    refine Eventually.of_forall fun q => ?_
    by_cases hq : q ∈ K
    · rw [Set.indicator_of_notMem (show q ∉ Kᶜ from fun hc => hc hq)]
      exact bot_le
    · rw [Set.indicator_of_mem (show q ∈ Kᶜ from hq)]
      have hnew := heatK_sq_le_future_offCompact (s := q.1) (y := q.2)
        hν ht hz.1 hz.2.1 hz.2.2 hq
      have hold := heatK_sq_le_future_offCompact (t' := t) (x' := x)
        (s := q.1) (y := q.2) hν ht (by linarith) (by linarith) (by simp) hq
      have hdiff : (heatK ν z.1 z.2 q.1 q.2 - heatK ν t x q.1 q.2) ^ 2 ≤
          (4 * C) * heatK ν (2 * t) x q.1 q.2 ^ 2 := by
        dsimp only [C]
        nlinarith [sq_nonneg (heatK ν z.1 z.2 q.1 q.2 + heatK ν t x q.1 q.2)]
      change d z q * w q ≤ D * A q
      calc
        _ ≤ ENNReal.ofReal ((4 * C) * heatK ν (2 * t) x q.1 q.2 ^ 2) * w q :=
          mul_le_mul (ENNReal.ofReal_le_ofReal hdiff) le_rfl bot_le bot_le
        _ = _ := by
          rw [ENNReal.ofReal_mul (show 0 ≤ 4 * C by positivity)]
          exact mul_assoc _ _ _
  have hAfinite : ∀ᵐ q ∂positiveTimeSpaceVolume, A q < ⊤ := ae_lt_top hAm hfuture.ne
  have htimeNe : ∀ᵐ q : ℝ × ℝ ∂positiveTimeSpaceVolume, q.1 ≠ t := by
    change ∀ᵐ q : ℝ × ℝ ∂(volume.restrict (Ioi (0 : ℝ))).prod volume, q.1 ≠ t
    exact Measure.quasiMeasurePreserving_fst.ae
      (ae_restrict_of_ae ((volume : Measure ℝ).ae_ne t))
  have hOfflim : Tendsto (fun z : ℝ × ℝ => ∫⁻ q, Kᶜ.indicator (f z) q ∂positiveTimeSpaceVolume)
      (𝓝 (t, x)) (𝓝 0) := by
    have hzero : (∫⁻ _ : ℝ × ℝ, (0 : ℝ≥0∞) ∂positiveTimeSpaceVolume) = 0 := lintegral_zero
    rw [← hzero]
    refine tendsto_lintegral_filter_of_dominated_convergence (fun q => D * A q)
      (Eventually.of_forall fun z => (hfm z).indicator hKm.compl) hOffbound ?_ ?_
    · rw [lintegral_const_mul _ hAm]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfuture.ne
    · filter_upwards [hAfinite, htimeNe] with q hqfin hqne
      by_cases hq : q ∈ K
      · simp only [Set.indicator_of_notMem (show q ∉ Kᶜ from fun hc => hc hq)]
        exact tendsto_const_nhds
      · simp only [Set.indicator_of_mem (show q ∈ Kᶜ from hq)]
        by_cases hs0 : q.1 ≤ 0
        · have heq (z : ℝ × ℝ) : f z q = 0 := by
            simp only [f, d, heatK_causal ν _ _ q.1 q.2 (Or.inl hs0),
              sub_self, zero_pow two_ne_zero, ENNReal.ofReal_zero, zero_mul]
          simp only [heq]
          exact tendsto_const_nhds
        · by_cases hshi : 5 * t / 4 ≤ q.1
          · have hst : t < q.1 := by linarith
            have hcut : ∀ᶠ z : ℝ × ℝ in 𝓝 (t, x), z.1 < q.1 :=
              (continuous_fst.tendsto (t, x)).eventually (gt_mem_nhds hst)
            have heq : (fun z : ℝ × ℝ => f z q) =ᶠ[𝓝 (t, x)] fun _ => 0 := by
              filter_upwards [hcut] with z hz
              simp only [f, d, heatK_causal ν z.1 z.2 q.1 q.2 (Or.inr hz.le),
                heatK_causal ν t x q.1 q.2 (Or.inr hst.le), sub_self,
                zero_pow two_ne_zero, ENNReal.ofReal_zero, zero_mul]
            exact Tendsto.congr' heq.symm tendsto_const_nhds
          · have hpos : 0 < heatK ν (2 * t) x q.1 q.2 := by
              rw [heatK_of ⟨not_le.mp hs0, by linarith⟩]
              exact RoughHeatKernel.heatKernel_pos (mul_pos hν (by linarith)) _
            have hkne : ENNReal.ofReal (heatK ν (2 * t) x q.1 q.2 ^ 2) ≠ 0 :=
              (ENNReal.ofReal_pos.mpr (pow_pos hpos 2)).ne'
            have hwne : w q ≠ ⊤ := by
              intro htop
              apply hqfin.ne
              change ENNReal.ofReal (heatK ν (2 * t) x q.1 q.2 ^ 2) * w q = ⊤
              rw [htop, ENNReal.mul_top hkne]
            have hdl : Tendsto (fun z : ℝ × ℝ => d z q) (𝓝 (t, x)) (𝓝 0) := by
              have h := ((tendsto_heatK_of_ne hν t x (y := q.2) hqne).sub_const
                (heatK ν t x q.1 q.2)).pow 2
              simp only [sub_self, zero_pow two_ne_zero] at h
              have hh := (ENNReal.continuous_ofReal.tendsto 0).comp h
              simpa only [Function.comp_def, ENNReal.ofReal_zero] using hh
            simpa only [zero_mul] using ENNReal.Tendsto.mul_const hdl (Or.inr hwne)
  have hsplit (z : ℝ × ℝ) :
      (∫⁻ q, f z q ∂positiveTimeSpaceVolume) =
        (∫⁻ q, K.indicator (f z) q ∂positiveTimeSpaceVolume) +
          ∫⁻ q, Kᶜ.indicator (f z) q ∂positiveTimeSpaceVolume := by
    rw [← lintegral_add_left ((hfm z).indicator hKm)]
    apply lintegral_congr
    intro q
    by_cases hq : q ∈ K
    · simp only [Set.indicator_of_mem hq,
        Set.indicator_of_notMem (show q ∉ Kᶜ from fun hc => hc hq), add_zero]
    · simp only [Set.indicator_of_notMem hq,
        Set.indicator_of_mem (show q ∈ Kᶜ from hq), zero_add]
  change Tendsto (fun z : ℝ × ℝ => ∫⁻ q, f z q ∂positiveTimeSpaceVolume) (𝓝 (t, x)) (𝓝 0)
  simp_rw [hsplit]
  simpa only [zero_add] using hKlim.add hOfflim


end RoughHeatKernel.WeightedCausalHeatKernel

end
