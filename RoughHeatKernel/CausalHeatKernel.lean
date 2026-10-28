/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
module

public import RoughHeatKernel.Scaled
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The causal heat kernel in positive-time space

The variance-scaled one-dimensional heat kernel, restricted to causal input
times, belongs to L² in the input time-space variables. Its squared L² distance
is jointly continuous in the output time and space, including nonpositive
output times. All diffusivity assumptions are explicit.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open Real MeasureTheory Filter Set
open scoped ENNReal Topology

namespace RoughHeatKernel.CausalHeatKernel

/-- Positive-time Lebesgue measure times spatial Lebesgue measure. -/
def positiveTimeSpaceVolume : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioi (0 : ℝ))).prod volume

/-- The causal heat kernel `G_ν(t-s, x-y) 1_{0<s<t}`. -/
def heatK (ν t x s y : ℝ) : ℝ :=
  if 0 < s ∧ s < t then RoughHeatKernel.heatKernel (ν * (t - s)) (x - y) else 0

theorem heatK_eq_heatKernel (ν t x s y : ℝ) :
    heatK ν t x s y =
      if 0 < s ∧ s < t then RoughHeatKernel.heatKernel (ν * (t - s)) (x - y) else 0 := by
  rfl

theorem heatK_of_not {ν t x s y : ℝ} (h : ¬ (0 < s ∧ s < t)) : heatK ν t x s y = 0 := by
  simp [heatK, h]

theorem heatK_of {ν t x s y : ℝ} (h : 0 < s ∧ s < t) :
    heatK ν t x s y = RoughHeatKernel.heatKernel (ν * (t - s)) (x - y) := by
  simp [heatK_eq_heatKernel, h]

theorem heatK_causal (ν t x s y : ℝ) (h : s ≤ 0 ∨ t ≤ s) : heatK ν t x s y = 0 := by
  apply heatK_of_not
  rintro ⟨h1, h2⟩
  rcases h with h | h <;> linarith

theorem measurable_heatK (ν : ℝ) :
    Measurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => heatK ν q.1.1 q.1.2 q.2.1 q.2.2) := by
  simp only [heatK_eq_heatKernel]
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_lt measurable_const (measurable_snd.fst)).inter
      (measurableSet_lt measurable_snd.fst measurable_fst.fst)
  · unfold RoughHeatKernel.heatKernel
    fun_prop


/-! ### The closed form of the squared L² norm -/

/-- The spatial integral: `∫ G_ν(r, x-y)² dy = (4πν)^{-1/2} r^{-1/2}` (as a lower integral). -/
theorem lintegral_heatKernel_mul_sq {ν r : ℝ} (hν : 0 < ν) (hr : 0 < r) (x : ℝ) :
    ∫⁻ y, ENNReal.ofReal (RoughHeatKernel.heatKernel (ν * r) (x - y) ^ 2) =
      ENNReal.ofReal (1 / Real.sqrt (4 * π * ν) * r ^ (-(1 / 2 : ℝ))) := by
  rw [lintegral_sub_left_eq_self
    (fun y => ENNReal.ofReal (RoughHeatKernel.heatKernel (ν * r) y ^ 2)) x]
  have hrep : (fun y => RoughHeatKernel.heatKernel (ν * r) y ^ 2) = fun y =>
      RoughHeatKernel.heatKernel (ν / 2 * r) y *
        (1 / Real.sqrt (4 * π * ν) * r ^ (-(1 / 2 : ℝ))) := by
    funext y
    rw [RoughHeatKernel.heatKernel_mul_sq_eq hν hr y]
    ring
  have hint : Integrable (fun y => RoughHeatKernel.heatKernel (ν * r) y ^ 2) := by
    rw [hrep]
    exact (RoughHeatKernel.integrable_heatKernel (by positivity)).mul_const _
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun y => sq_nonneg _), hrep, integral_mul_const,
    RoughHeatKernel.integral_heatKernel (by positivity), one_mul]

/-- The time integral `∫_a^t (4πν)^{-1/2} (t-s)^{-1/2} ds = √((t-a)/(πν))`. -/
theorem lintegral_time {ν a t : ℝ} (hν : 0 < ν) (hat : a < t) :
    ∫⁻ s in Ioo a t, ENNReal.ofReal (1 / Real.sqrt (4 * π * ν) * (t - s) ^ (-(1 / 2 : ℝ))) =
      ENNReal.ofReal (Real.sqrt ((t - a) / (π * ν))) := by
  have hii : IntervalIntegrable (fun s => 1 / Real.sqrt (4 * π * ν) * (t - s) ^ (-(1 / 2 : ℝ)))
      volume a t := by
    have h0 : IntervalIntegrable (fun u : ℝ => u ^ (-(1 / 2 : ℝ))) volume (t - t) (t - a) :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have h1 := h0.comp_sub_left t
    simp only [sub_sub_cancel] at h1
    exact (h1.symm.const_mul _)
  have hio : IntegrableOn (fun s => 1 / Real.sqrt (4 * π * ν) * (t - s) ^ (-(1 / 2 : ℝ)))
      (Ioo a t) := ((intervalIntegrable_iff_integrableOn_Ioo_of_le hat.le).mp hii)
  rw [← ofReal_integral_eq_lintegral_ofReal hio
    ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun s hs =>
      mul_nonneg (by positivity) (Real.rpow_nonneg (sub_nonneg.mpr hs.2.le) _)))]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hat.le,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left
      (fun u => u ^ (-(1 / 2 : ℝ))), sub_self,
    integral_rpow (Or.inl (by norm_num)), Real.zero_rpow (by norm_num)]
  have hta : 0 < t - a := sub_pos.mpr hat
  rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
    Real.sqrt_div hta.le, show (4 : ℝ) * π * ν = 2 ^ 2 * (π * ν) by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have : 0 < Real.sqrt (π * ν) := Real.sqrt_pos.mpr (by positivity)
  field_simp
  ring

/-- Closed form of the squared L² norm of the kernel section beyond time `a ≥ 0`:
`∫∫_{s > a} G_ν(t-s, x-y)² 1_{0<s<t} dy ds = √((t-a)/(πν))`, which is `0` when `t ≤ a`
(`Real.sqrt` of a nonpositive number is `0`). -/
theorem lintegral_heatK_sq_Ioi {ν a : ℝ} (hν : 0 < ν) (ha : 0 ≤ a) (t x : ℝ) :
    ∫⁻ w, {w : ℝ × ℝ | a < w.1}.indicator
        (fun w => ENNReal.ofReal (heatK ν t x w.1 w.2 ^ 2)) w ∂positiveTimeSpaceVolume =
      ENNReal.ofReal (Real.sqrt ((t - a) / (π * ν))) := by
  have hmeas : Measurable (fun w : ℝ × ℝ => {w : ℝ × ℝ | a < w.1}.indicator
      (fun w => ENNReal.ofReal (heatK ν t x w.1 w.2 ^ 2)) w) := by
    refine Measurable.indicator ?_ (measurableSet_lt measurable_const measurable_fst)
    exact (((measurable_heatK ν).comp
      ((measurable_const (a := (t, x))).prodMk measurable_id)).pow_const 2).ennreal_ofReal
  rw [positiveTimeSpaceVolume, lintegral_prod _ hmeas.aemeasurable]
  have hinner : ∀ s : ℝ, (∫⁻ y, {w : ℝ × ℝ | a < w.1}.indicator
      (fun w => ENNReal.ofReal (heatK ν t x w.1 w.2 ^ 2)) (s, y)) =
      (Ioo a t).indicator
        (fun s => ENNReal.ofReal (1 / Real.sqrt (4 * π * ν) * (t - s) ^ (-(1 / 2 : ℝ)))) s := by
    intro s
    by_cases hs : a < s ∧ s < t
    · have h0 : 0 < s ∧ s < t := ⟨ha.trans_lt hs.1, hs.2⟩
      rw [Set.indicator_of_mem (show s ∈ Ioo a t from hs)]
      have hfun : (fun y => {w : ℝ × ℝ | a < w.1}.indicator
          (fun w => ENNReal.ofReal (heatK ν t x w.1 w.2 ^ 2)) (s, y)) = fun y =>
          ENNReal.ofReal (RoughHeatKernel.heatKernel (ν * (t - s)) (x - y) ^ 2) := by
        funext y
        rw [Set.indicator_of_mem (show (s, y) ∈ {w : ℝ × ℝ | a < w.1} from hs.1), heatK_of h0]
      rw [hfun]
      exact lintegral_heatKernel_mul_sq hν (sub_pos.mpr hs.2) x
    · rw [Set.indicator_of_notMem (by simpa using hs)]
      by_cases has : a < s
      · have : ¬ (0 < s ∧ s < t) := fun h => hs ⟨has, h.2⟩
        simp [Set.indicator, has, heatK_of_not this]
      · simp [Set.indicator, has]
  simp_rw [hinner]
  by_cases hat : a < t
  · rw [lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
      Set.inter_eq_left.mpr (show Ioo a t ⊆ Ioi 0 from fun s hs => ha.trans_lt hs.1)]
    exact lintegral_time hν hat
  · rw [Set.Ioo_eq_empty hat, Set.indicator_empty, lintegral_zero,
      Real.sqrt_eq_zero'.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)),
      ENNReal.ofReal_zero]

/-- The squared L² norm of the kernel section: `∫∫ G_ν(t-s,x-y)² 1_{0<s<t} = √(t/(πν))`
for every real `t` (`0` for `t ≤ 0`). -/
theorem lintegral_heatK_sq {ν : ℝ} (hν : 0 < ν) (t x : ℝ) :
    ∫⁻ w, ENNReal.ofReal (heatK ν t x w.1 w.2 ^ 2) ∂positiveTimeSpaceVolume =
      ENNReal.ofReal (Real.sqrt (t / (π * ν))) := by
  have h := lintegral_heatK_sq_Ioi hν le_rfl t x
  rw [sub_zero] at h
  rw [← h]
  apply lintegral_congr
  intro w
  by_cases hw : 0 < w.1
  · rw [Set.indicator_of_mem (show w ∈ {w : ℝ × ℝ | 0 < w.1} from hw)]
  · rw [Set.indicator_of_notMem (show w ∉ {w : ℝ × ℝ | 0 < w.1} from hw),
      heatK_causal ν t x w.1 w.2 (Or.inl (not_lt.mp hw))]
    simp

theorem measurable_heatK_section (ν t x : ℝ) :
    Measurable (fun w : ℝ × ℝ => heatK ν t x w.1 w.2) :=
  (measurable_heatK ν).comp ((measurable_const (a := (t, x))).prodMk measurable_id)

/-- Each kernel section is square integrable for the positive-time measure. -/
theorem memLp_heatK {ν : ℝ} (hν : 0 < ν) (t x : ℝ) :
    MemLp (fun w : ℝ × ℝ => heatK ν t x w.1 w.2) 2 positiveTimeSpaceVolume := by
  have hm := measurable_heatK_section ν t x
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  refine ⟨(hm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun w => sq_nonneg _),
    lintegral_heatK_sq hν]
  exact ENNReal.ofReal_lt_top

/-! ### L² continuity of the kernel in the output point -/

/-- Pointwise convergence off the diagonal time `s = t`. -/
theorem tendsto_heatK_of_ne {ν : ℝ} (hν : 0 < ν) (t x : ℝ) {s y : ℝ} (hst : s ≠ t) :
    Tendsto (fun z : ℝ × ℝ => heatK ν z.1 z.2 s y) (𝓝 (t, x)) (𝓝 (heatK ν t x s y)) := by
  rcases lt_or_gt_of_ne hst with hlt | hgt
  · by_cases hs : 0 < s
    · have hev : ∀ᶠ z : ℝ × ℝ in 𝓝 (t, x), heatK ν z.1 z.2 s y =
          RoughHeatKernel.heatKernel (ν * (z.1 - s)) (z.2 - y) := by
        have : ∀ᶠ z : ℝ × ℝ in 𝓝 (t, x), s < z.1 :=
          (continuous_fst.tendsto (t, x)).eventually (lt_mem_nhds hlt)
        filter_upwards [this] with z hz
        exact heatK_of ⟨hs, hz⟩
      rw [heatK_of ⟨hs, hlt⟩]
      refine Tendsto.congr' (EventuallyEq.symm hev) ?_
      have hc := RoughHeatKernel.continuousAt_heatKernel_joint (ν * (t - s), x)
        (show 0 < ν * (t - s) from mul_pos hν (sub_pos.mpr hlt)) y
      have hmap : ContinuousAt (fun z : ℝ × ℝ => (ν * (z.1 - s), z.2)) (t, x) := by fun_prop
      exact ContinuousAt.comp (g := fun z : ℝ × ℝ => RoughHeatKernel.heatKernel z.1 (z.2 - y))
        (f := fun z : ℝ × ℝ => (ν * (z.1 - s), z.2)) hc hmap
    · simp only [heatK_causal ν _ _ s y (Or.inl (not_lt.mp hs))]
      exact tendsto_const_nhds
  · have hev : ∀ᶠ z : ℝ × ℝ in 𝓝 (t, x), heatK ν z.1 z.2 s y = 0 := by
      have : ∀ᶠ z : ℝ × ℝ in 𝓝 (t, x), z.1 < s :=
        (continuous_fst.tendsto (t, x)).eventually (gt_mem_nhds hgt)
      filter_upwards [this] with z hz
      exact heatK_causal ν _ _ s y (Or.inr hz.le)
    rw [heatK_causal ν t x s y (Or.inr hgt.le)]
    exact Tendsto.congr' (EventuallyEq.symm hev) tendsto_const_nhds

/-- Domination away from the singular time: for `0 < s ≤ t - η`, `|t' - t| ≤ η/4`,
`|x' - x| ≤ 1`, `G_ν(t'-s, x'-y)² ≤ 4 e^{6/(νη)} G_{2ν}(t-s, x-y)²`. -/
theorem heatK_sq_le_local {ν t x t' x' η s y : ℝ} (hν : 0 < ν) (hη : 0 < η)
    (hs : s ≤ t - η) (ht' : |t' - t| ≤ η / 4) (hx' : |x' - x| ≤ 1) :
    heatK ν t' x' s y ^ 2 ≤ 4 * Real.exp (6 / (ν * η)) * heatK (2 * ν) t x s y ^ 2 := by
  by_cases hs0 : 0 < s
  · have hts : η ≤ t - s := by linarith
    have ht'1 := (abs_le.mp ht').1
    have ht'2 := (abs_le.mp ht').2
    rw [heatK_of ⟨hs0, by linarith⟩, heatK_of ⟨hs0, by linarith⟩]
    have hT : 0 < ν * (t - s) := mul_pos hν (by linarith)
    have h := RoughHeatKernel.heatKernel_sq_le_local (t := ν * (t - s)) (u := ν * (t' - s))
      (s := 0) (x := x') (z := x) (y := y) hT (by nlinarith) (by nlinarith) le_rfl
      (by positivity) hx'
    simp only [sub_zero] at h
    rw [show 2 * ν * (t - s) = 2 * (ν * (t - s)) by ring]
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
    gcongr
  · rw [heatK_causal ν t' x' s y (Or.inl (not_lt.mp hs0)), zero_pow two_ne_zero]
    positivity

/-- The squared difference restricted to `{s ≤ t - η}` tends to `0` (dominated convergence). -/
theorem tendsto_lintegral_indicator_le {ν t η : ℝ} (hν : 0 < ν) (hη : 0 < η) (x : ℝ) :
    Tendsto (fun z : ℝ × ℝ => ∫⁻ w, {w : ℝ × ℝ | w.1 ≤ t - η}.indicator
        (fun w => ENNReal.ofReal ((heatK ν z.1 z.2 w.1 w.2 - heatK ν t x w.1 w.2) ^ 2)) w
          ∂positiveTimeSpaceVolume) (𝓝 (t, x)) (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ C = 8 * Real.exp (6 / (ν * η)) :=
    ⟨_, by positivity, rfl⟩
  let bound : ℝ × ℝ → ℝ≥0∞ := fun w =>
    ENNReal.ofReal C * ENNReal.ofReal (heatK (2 * ν) t x w.1 w.2 ^ 2) +
      2 * ENNReal.ofReal (heatK ν t x w.1 w.2 ^ 2)
  have hmA : MeasurableSet {w : ℝ × ℝ | w.1 ≤ t - η} :=
    measurableSet_le measurable_fst measurable_const
  have hsq (ν' t' x' : ℝ) : Measurable (fun w : ℝ × ℝ =>
      ENNReal.ofReal (heatK ν' t' x' w.1 w.2 ^ 2)) :=
    ((measurable_heatK_section ν' t' x').pow_const 2).ennreal_ofReal
  have h0 : ∫⁻ w, (0 : ℝ≥0∞) ∂positiveTimeSpaceVolume = 0 := lintegral_zero
  rw [← h0]
  refine tendsto_lintegral_filter_of_dominated_convergence bound ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun z => Measurable.indicator ?_ hmA
    exact (((measurable_heatK_section ν z.1 z.2).sub
      (measurable_heatK_section ν t x)).pow_const 2).ennreal_ofReal
  · have hev : ∀ᶠ z : ℝ × ℝ in 𝓝 (t, x), |z.1 - t| ≤ η / 4 ∧ |z.2 - x| ≤ 1 := by
      have h1 : ∀ᶠ z : ℝ × ℝ in 𝓝 (t, x), |z.1 - t| ≤ η / 4 := by
        have : ∀ᶠ r in 𝓝 t, |r - t| ≤ η / 4 := by
          filter_upwards [Metric.closedBall_mem_nhds t (show (0:ℝ) < η / 4 by positivity)]
            with r hr
          simpa [Metric.mem_closedBall, Real.dist_eq] using hr
        exact (continuous_fst.tendsto (t, x)).eventually this
      have h2 : ∀ᶠ z : ℝ × ℝ in 𝓝 (t, x), |z.2 - x| ≤ 1 := by
        have : ∀ᶠ r in 𝓝 x, |r - x| ≤ 1 := by
          filter_upwards [Metric.closedBall_mem_nhds x one_pos] with r hr
          simpa [Metric.mem_closedBall, Real.dist_eq] using hr
        exact (continuous_snd.tendsto (t, x)).eventually this
      exact h1.and h2
    filter_upwards [hev] with z hz
    refine Eventually.of_forall fun w => ?_
    by_cases hw : w.1 ≤ t - η
    · rw [Set.indicator_of_mem (show w ∈ {w : ℝ × ℝ | w.1 ≤ t - η} from hw)]
      have hk := heatK_sq_le_local (y := w.2) hν hη hw hz.1 hz.2
      have hreal : (heatK ν z.1 z.2 w.1 w.2 - heatK ν t x w.1 w.2) ^ 2 ≤
          C * heatK (2 * ν) t x w.1 w.2 ^ 2 + 2 * heatK ν t x w.1 w.2 ^ 2 := by
        nlinarith [sq_nonneg (heatK ν z.1 z.2 w.1 w.2 + heatK ν t x w.1 w.2)]
      refine (ENNReal.ofReal_le_ofReal hreal).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hC0,
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    · rw [Set.indicator_of_notMem (show w ∉ {w : ℝ × ℝ | w.1 ≤ t - η} from hw)]
      exact bot_le
  · rw [lintegral_add_left ((hsq _ _ _).const_mul _), lintegral_const_mul _ (hsq _ _ _),
      lintegral_const_mul _ (hsq _ _ _), lintegral_heatK_sq (by positivity),
      lintegral_heatK_sq hν]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top, ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top⟩
  · refine Eventually.of_forall fun w => ?_
    by_cases hw : w.1 ≤ t - η
    · simp only [Set.indicator_of_mem (show w ∈ {w : ℝ × ℝ | w.1 ≤ t - η} from hw)]
      have hne : w.1 ≠ t := by linarith
      have h := ((tendsto_heatK_of_ne hν t x (y := w.2) hne).sub_const
        (heatK ν t x w.1 w.2)).pow 2
      rw [sub_self, zero_pow two_ne_zero] at h
      have h' := (ENNReal.continuous_ofReal.tendsto 0).comp h
      rw [ENNReal.ofReal_zero] at h'
      exact h'
    · simp only [Set.indicator_of_notMem (show w ∉ {w : ℝ × ℝ | w.1 ≤ t - η} from hw)]
      exact tendsto_const_nhds

/-- The real-number estimate behind the short-time tail bound. -/
theorem tail_bound_real {ν t η δ t' : ℝ} (hν : 0 < ν) (hη : 0 < η)
    (hηδ : η ≤ π * ν * δ ^ 2 / 128) (hδ : 0 < δ) (ht' : t' ≤ t + η) :
    2 * Real.sqrt ((t' - (t - η)) / (π * ν)) + 2 * Real.sqrt ((t - (t - η)) / (π * ν)) ≤
      δ / 2 := by
  have hpν : 0 < π * ν := by positivity
  have hq : Real.sqrt (2 * η / (π * ν)) ≤ δ / 8 := by
    rw [show δ / 8 = Real.sqrt ((δ / 8) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ hpν]
    nlinarith
  have h1 : Real.sqrt ((t' - (t - η)) / (π * ν)) ≤ Real.sqrt (2 * η / (π * ν)) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith) hpν.le)
  have h2 : Real.sqrt ((t - (t - η)) / (π * ν)) ≤ Real.sqrt (2 * η / (π * ν)) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith) hpν.le)
  linarith

/-- **L² continuity of the heat kernel in the output point**, at every `(t,x) ∈ ℝ²`, the time
origin and negative times included: `∫∫ (G_ν(t'-s,x'-y)1_{0<s<t'} - G_ν(t-s,x-y)1_{0<s<t})²
→ 0` as `(t',x') → (t,x)`. -/
theorem tendsto_heatK_sq {ν : ℝ} (hν : 0 < ν) (z : ℝ × ℝ) :
    Tendsto (fun z' : ℝ × ℝ => ∫⁻ w : ℝ × ℝ,
      ENNReal.ofReal ((heatK ν z'.1 z'.2 w.1 w.2 - heatK ν z.1 z.2 w.1 w.2) ^ 2)
        ∂positiveTimeSpaceVolume) (𝓝 z) (𝓝 0) := by
  obtain ⟨t, x⟩ := z
  by_cases ht : t ≤ 0
  · have hk0 : ∀ s y, heatK ν t x s y = 0 := fun s y => heatK_causal ν t x s y (by
      by_cases hs : s ≤ 0
      · exact Or.inl hs
      · exact Or.inr (ht.trans (not_le.mp hs).le))
    simp only [hk0, sub_zero, lintegral_heatK_sq hν]
    have hc : Continuous (fun z' : ℝ × ℝ => ENNReal.ofReal (Real.sqrt (z'.1 / (π * ν)))) :=
      ENNReal.continuous_ofReal.comp ((continuous_fst.div_const _).sqrt)
    have h := hc.tendsto (t, x)
    have h0 : Real.sqrt (t / (π * ν)) = 0 :=
      Real.sqrt_eq_zero'.mpr (div_nonpos_of_nonpos_of_nonneg ht (by positivity))
    rw [h0, ENNReal.ofReal_zero] at h
    exact h
  · rw [not_le] at ht
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ ε := by
      rcases eq_or_ne ε ⊤ with rfl | hne
      · exact ⟨1, one_pos, le_top⟩
      · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' hne, (ENNReal.ofReal_toReal hne).le⟩
    obtain ⟨η, hη, hηt, hηδ⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ t / 2 ∧ η ≤ π * ν * δ ^ 2 / 128 :=
      ⟨min (t / 2) (π * ν * δ ^ 2 / 128), lt_min (by positivity) (by positivity),
        min_le_left _ _, min_le_right _ _⟩
    have hA := tendsto_lintegral_indicator_le (t := t) hν hη x
    have hA' := hA.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < ENNReal.ofReal (δ / 2) from
      ENNReal.ofReal_pos.mpr (half_pos hδ)))
    have hT : ∀ᶠ z' : ℝ × ℝ in 𝓝 (t, x), z'.1 ≤ t + η :=
      (continuous_fst.tendsto (t, x)).eventually (ge_mem_nhds (by linarith))
    filter_upwards [hA', hT] with z' hz'A hz'T
    have hsq (t' x' : ℝ) : Measurable (fun w : ℝ × ℝ =>
        ENNReal.ofReal (heatK ν t' x' w.1 w.2 ^ 2)) :=
      ((measurable_heatK_section ν t' x').pow_const 2).ennreal_ofReal
    have hfm : Measurable (fun w : ℝ × ℝ =>
        ENNReal.ofReal ((heatK ν z'.1 z'.2 w.1 w.2 - heatK ν t x w.1 w.2) ^ 2)) :=
      (((measurable_heatK_section ν z'.1 z'.2).sub
        (measurable_heatK_section ν t x)).pow_const 2).ennreal_ofReal
    have hmA : MeasurableSet {w : ℝ × ℝ | w.1 ≤ t - η} :=
      measurableSet_le measurable_fst measurable_const
    have hmB : MeasurableSet {w : ℝ × ℝ | t - η < w.1} :=
      measurableSet_lt measurable_const measurable_fst
    have hsplit : (∫⁻ w, ENNReal.ofReal ((heatK ν z'.1 z'.2 w.1 w.2 - heatK ν t x w.1 w.2) ^ 2)
        ∂positiveTimeSpaceVolume) =
        (∫⁻ w, {w : ℝ × ℝ | w.1 ≤ t - η}.indicator (fun w =>
          ENNReal.ofReal ((heatK ν z'.1 z'.2 w.1 w.2 - heatK ν t x w.1 w.2) ^ 2)) w
            ∂positiveTimeSpaceVolume) +
        ∫⁻ w, {w : ℝ × ℝ | t - η < w.1}.indicator (fun w =>
          ENNReal.ofReal ((heatK ν z'.1 z'.2 w.1 w.2 - heatK ν t x w.1 w.2) ^ 2)) w
            ∂positiveTimeSpaceVolume := by
      rw [← lintegral_add_left (hfm.indicator hmA)]
      refine lintegral_congr fun w => ?_
      by_cases hw : w.1 ≤ t - η
      · rw [Set.indicator_of_mem (show w ∈ {w : ℝ × ℝ | w.1 ≤ t - η} from hw),
          Set.indicator_of_notMem (show w ∉ {w : ℝ × ℝ | t - η < w.1} from not_lt.mpr hw),
          add_zero]
      · rw [Set.indicator_of_notMem (show w ∉ {w : ℝ × ℝ | w.1 ≤ t - η} from hw),
          Set.indicator_of_mem (show w ∈ {w : ℝ × ℝ | t - η < w.1} from not_le.mp hw),
          zero_add]
    have hB : (∫⁻ w, {w : ℝ × ℝ | t - η < w.1}.indicator (fun w =>
          ENNReal.ofReal ((heatK ν z'.1 z'.2 w.1 w.2 - heatK ν t x w.1 w.2) ^ 2)) w
            ∂positiveTimeSpaceVolume) ≤ ENNReal.ofReal (δ / 2) := by
      calc _ ≤ ∫⁻ w, (2 * {w : ℝ × ℝ | t - η < w.1}.indicator
                (fun w => ENNReal.ofReal (heatK ν z'.1 z'.2 w.1 w.2 ^ 2)) w +
              2 * {w : ℝ × ℝ | t - η < w.1}.indicator
                (fun w => ENNReal.ofReal (heatK ν t x w.1 w.2 ^ 2)) w) ∂positiveTimeSpaceVolume := by
            refine lintegral_mono fun w => ?_
            by_cases hw : t - η < w.1
            · simp only [Set.indicator_of_mem (show w ∈ {w : ℝ × ℝ | t - η < w.1} from hw)]
              rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
                ← ENNReal.ofReal_mul (by norm_num),
                ← ENNReal.ofReal_add (by positivity) (by positivity)]
              exact ENNReal.ofReal_le_ofReal (by
                nlinarith [sq_nonneg (heatK ν z'.1 z'.2 w.1 w.2 + heatK ν t x w.1 w.2)])
            · simp only [Set.indicator_of_notMem
                (show w ∉ {w : ℝ × ℝ | t - η < w.1} from hw)]
              exact bot_le
        _ = 2 * ENNReal.ofReal (Real.sqrt ((z'.1 - (t - η)) / (π * ν))) +
              2 * ENNReal.ofReal (Real.sqrt ((t - (t - η)) / (π * ν))) := by
            rw [lintegral_add_left (((hsq _ _).indicator hmB).const_mul _),
              lintegral_const_mul _ ((hsq _ _).indicator hmB),
              lintegral_const_mul _ ((hsq _ _).indicator hmB),
              lintegral_heatK_sq_Ioi hν (by linarith), lintegral_heatK_sq_Ioi hν (by linarith)]
        _ ≤ ENNReal.ofReal (δ / 2) := by
            rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
              ← ENNReal.ofReal_mul (by norm_num),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
            exact ENNReal.ofReal_le_ofReal (tail_bound_real hν hη hηδ hδ hz'T)
    calc _ = _ := hsplit
      _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := add_le_add hz'A.le hB
      _ = ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]
      _ ≤ ε := hδε

end RoughHeatKernel.CausalHeatKernel

end
