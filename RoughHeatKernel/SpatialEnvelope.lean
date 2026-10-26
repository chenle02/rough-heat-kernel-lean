/- Copyright (c) 2026 Le Chen. Apache-2.0.
Known uniform quarter-Hölder Gaussian envelope with an explicit universal constant. -/
module

public import RoughHeatKernel.Increments
public import RoughHeatKernel.ChenDalang
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

noncomputable section
set_option autoImplicit false
open Set
namespace RoughHeatKernel.SpatialEnvelope

lemma normalized_gaussian_derivative (a : ℝ) :
    |a| * Real.exp (-(a^2/4)) ≤ 1 := by
  have h : |a| ≤ a^2/4+1 := by nlinarith [sq_nonneg (|a|-2),sq_abs a]
  calc
    _ ≤ (a^2/4+1) * Real.exp (-(a^2/4)) :=
      mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ ≤ Real.exp (a^2/4) * Real.exp (-(a^2/4)) :=
      mul_le_mul_of_nonneg_right (Real.add_one_le_exp _) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

lemma kernel_ratio {r : ℝ} (hr : 0<r) (x : ℝ) :
    heatKernel r x = Real.sqrt 2 * Real.exp (-(x^2/(4*r))) * heatKernel (2*r) x := by
  have hs : Real.sqrt (2*Real.pi*(2*r)) = Real.sqrt 2 * Real.sqrt (2*Real.pi*r) := by
    rw [show 2*Real.pi*(2*r)=2*(2*Real.pi*r) by ring,Real.sqrt_mul (by norm_num)]
  have he : -(1/(2*r))*x^2 = -(x^2/(4*r)) + -(1/(2*(2*r)))*x^2 := by
    field_simp; ring
  unfold heatKernel
  rw [he,Real.exp_add,hs]
  have htwo : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : Real.sqrt (2*Real.pi*r) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp

lemma derivative_envelope {r : ℝ} (hr : 0<r) (x : ℝ) :
    |-(x/r)*heatKernel r x| ≤ (2/Real.sqrt r)*heatKernel (2*r) x := by
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hs2 : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  have hgauss := normalized_gaussian_derivative (x/Real.sqrt r)
  have harg : (x/Real.sqrt r)^2/4 = x^2/(4*r) := by rw [div_pow,hs2]; ring
  rw [harg,abs_div,abs_of_pos hs] at hgauss
  rw [abs_mul,abs_neg,abs_div,abs_of_pos hr,abs_of_pos (heatKernel_pos hr _),kernel_ratio hr]
  have hsqrt : Real.sqrt 2 ≤ (2:ℝ) := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg (2:ℝ)]
  have hnn := (heatKernel_pos (show 0<2*r by positivity) x).le
  calc
    _ = (Real.sqrt 2 / Real.sqrt r) *
      ((|x|/Real.sqrt r)*Real.exp (-(x^2/(4*r)))) * heatKernel (2*r) x := by
      field_simp
      rw [hs2]
      ring
    _ ≤ (Real.sqrt 2 / Real.sqrt r) * 1 * heatKernel (2*r) x := by gcongr
    _ ≤ (2/Real.sqrt r)*heatKernel (2*r) x := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hsqrt hs.le) hnn

lemma kernel_le_of_sq_le {r a b : ℝ} (hr : 0<r) (h : b^2 ≤ a^2) :
    heatKernel r a ≤ heatKernel r b := by
  unfold heatKernel
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  exact mul_le_mul_of_nonpos_left h (neg_nonpos.mpr (by positivity))

lemma kernel_segment_envelope {r u v w : ℝ} (hr : 0<r) (huv : u≤v)
    (hd : v-u≤Real.sqrt r) (hwu : u≤w) (hwv : w≤v) :
    heatKernel (2*r) w ≤ Real.exp 1 * (heatKernel (2*r) u+heatKernel (2*r) v) := by
  have hr2 : 0<2*r := by positivity
  have hu := (heatKernel_pos hr2 u).le
  have hv := (heatKernel_pos hr2 v).le
  have he : 1≤Real.exp (1:ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
  by_cases hu0 : 0≤u
  · have hw2 : u^2≤w^2 := by nlinarith
    calc
      _ ≤ heatKernel (2*r) u := kernel_le_of_sq_le hr2 hw2
      _ ≤ heatKernel (2*r) u+heatKernel (2*r) v := le_add_of_nonneg_right hv
      _ ≤ _ := le_mul_of_one_le_left (add_nonneg hu hv) he
  by_cases hv0 : v≤0
  · have hw2 : v^2≤w^2 := by nlinarith
    calc
      _ ≤ heatKernel (2*r) v := kernel_le_of_sq_le hr2 hw2
      _ ≤ heatKernel (2*r) u+heatKernel (2*r) v := le_add_of_nonneg_left hu
      _ ≤ _ := le_mul_of_one_le_left (add_nonneg hu hv) he
  have hu2 : u^2≤r := by
    have hsq : (v-u)^2 ≤ Real.sqrt r ^2 :=
      (sq_le_sq₀ (sub_nonneg.mpr huv) (Real.sqrt_nonneg r)).mpr hd
    rw [Real.sq_sqrt hr.le] at hsq
    nlinarith
  have hzero : heatKernel (2*r) 0 ≤ Real.exp 1 * heatKernel (2*r) u := by
    have harg : 0 ≤ 1 + -(1/(2*(2*r)))*u^2 := by
      have : u^2/(4*r) ≤ 1 := (div_le_iff₀ (by positivity : 0<4*r)).mpr (by nlinarith)
      have hid : -(1/(2*(2*r)))*u^2 = -(u^2/(4*r)) := by ring
      rw [hid]; linarith
    rw [heatKernel_zero]
    calc
      _ = (1/Real.sqrt (2*Real.pi*(2*r)))*1 := by ring
      _ ≤ (1/Real.sqrt (2*Real.pi*(2*r)))*Real.exp (1 + -(1/(2*(2*r)))*u^2) :=
        mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.mpr harg) (by positivity)
      _ = _ := by rw [Real.exp_add]; unfold heatKernel; ring
  calc
    _ ≤ heatKernel (2*r) 0 := heatKernel_le_heatKernel_zero hr2 w
    _ ≤ Real.exp 1 * heatKernel (2*r) u := hzero
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hv) (Real.exp_pos _).le

lemma kernel_le_two_double {r : ℝ} (hr : 0<r) (x : ℝ) :
    heatKernel r x ≤ 2*heatKernel (2*r) x := by
  have hnn := (heatKernel_pos (show 0<2*r by positivity) x).le
  rw [kernel_ratio hr]
  have he : Real.exp (-(x^2/(4*r))) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have hsqrt : Real.sqrt 2 ≤ (2:ℝ) := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg (2:ℝ)]
  calc
    _ ≤ Real.sqrt 2 * 1 * heatKernel (2*r) x := by gcongr
    _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_right hsqrt (heatKernel_pos (by positivity) x).le

lemma ordered_near_increment {r u v : ℝ} (hr : 0<r) (huv : u≤v)
    (hd : v-u≤Real.sqrt r) :
    |heatKernel r u-heatKernel r v| ≤
      (2*Real.exp 1)*((v-u)/Real.sqrt r)*(heatKernel (2*r) u+heatKernel (2*r) v) := by
  have hs := (Real.sqrt_pos.mpr hr).le
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
    (f:=heatKernel r) (a:=u) (b:=v)
    (f':=fun w => -(w/r)*heatKernel r w)
    (C:=(2/Real.sqrt r)*(Real.exp 1*(heatKernel (2*r) u+heatKernel (2*r) v)))
    (fun w _ => (hasDerivAt_heatKernel hr w).hasDerivWithinAt)
    (fun w hw => by
      rw [Real.norm_eq_abs]
      exact (derivative_envelope hr w).trans
        (mul_le_mul_of_nonneg_left (kernel_segment_envelope hr huv hd hw.1 hw.2.le) (by positivity)))
    v ⟨huv,le_rfl⟩
  rw [Real.norm_eq_abs,abs_sub_comm] at hmv
  convert hmv using 1
  ring

lemma ordered_quarter_increment {r u v : ℝ} (hr : 0<r) (huv : u≤v) :
    |heatKernel r u-heatKernel r v| ≤
      (2*Real.exp 1)*((v-u)/Real.sqrt r)^(1/4:ℝ)*
        (heatKernel (2*r) u+heatKernel (2*r) v) := by
  have hs : 0<Real.sqrt r := Real.sqrt_pos.mpr hr
  have hsum := add_nonneg (heatKernel_pos (show 0<2*r by positivity) u).le
    (heatKernel_pos (show 0<2*r by positivity) v).le
  have hq0 : 0≤(v-u)/Real.sqrt r := div_nonneg (sub_nonneg.mpr huv) hs.le
  by_cases hd : v-u≤Real.sqrt r
  · have hq1 : (v-u)/Real.sqrt r≤1 := (div_le_one hs).mpr hd
    have hp : (v-u)/Real.sqrt r ≤ ((v-u)/Real.sqrt r)^(1/4:ℝ) := by
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_ge' hq0 hq1
          (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)≤1))
    exact (ordered_near_increment hr huv hd).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (by positivity)) hsum)
  · have hq1 : 1≤(v-u)/Real.sqrt r := (le_div_iff₀ hs).mpr (by linarith)
    have hp : 1≤((v-u)/Real.sqrt r)^(1/4:ℝ) :=
      Real.one_le_rpow hq1 (by norm_num)
    have htriv : |heatKernel r u-heatKernel r v| ≤
        2*(heatKernel (2*r) u+heatKernel (2*r) v) := by
      have hu := (heatKernel_pos hr u).le
      have hv := (heatKernel_pos hr v).le
      have hdiff : |heatKernel r u-heatKernel r v| ≤ heatKernel r u+heatKernel r v := by
        exact abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩
      exact hdiff.trans (by nlinarith [kernel_le_two_double hr u,kernel_le_two_double hr v])
    have he : 1≤Real.exp (1:ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
    calc
      _ ≤ 2*(heatKernel (2*r) u+heatKernel (2*r) v) := htriv
      _ ≤ (2*Real.exp 1)*1*(heatKernel (2*r) u+heatKernel (2*r) v) := by gcongr; norm_num
      _ ≤ _ := by gcongr

theorem quarter_increment_normalized {r : ℝ} (hr : 0<r) (u v : ℝ) :
    |heatKernel r u-heatKernel r v| ≤
      (2*Real.exp 1)*(|u-v|/Real.sqrt r)^(1/4:ℝ)*
        (heatKernel (2*r) u+heatKernel (2*r) v) := by
  rcases le_total u v with huv|hvu
  · simpa only [abs_sub_comm u v,abs_of_nonneg (sub_nonneg.mpr huv)] using
      ordered_quarter_increment hr huv
  · have h := ordered_quarter_increment hr hvu
    rw [abs_sub_comm] at h
    simpa only [abs_of_nonneg (sub_nonneg.mpr hvu),add_comm] using h

/-- A fixed universal positive constant precedes every positive time and pair of spatial points. -/
theorem quarter_increment {r : ℝ} (hr : 0<r) (u v : ℝ) :
    |heatKernel r u-heatKernel r v| ≤
      (2*Real.exp 1)*|u-v|^(1/4:ℝ)*r^(-(1/8:ℝ))*
        (heatKernel (2*r) u+heatKernel (2*r) v) := by
  have hpow : (|u-v|/Real.sqrt r)^(1/4:ℝ) = |u-v|^(1/4:ℝ)*r^(-(1/8:ℝ)) := by
    rw [Real.div_rpow (abs_nonneg _) (Real.sqrt_nonneg _),Real.sqrt_eq_rpow,
      ← Real.rpow_mul hr.le]
    norm_num
    rw [Real.rpow_neg hr.le,div_eq_mul_inv]
  have h := quarter_increment_normalized hr u v
  rw [hpow] at h
  convert h using 1
  ring

theorem exists_quarter_increment_constant :
    ∃ C : ℝ, 0<C ∧ ∀ r : ℝ, 0<r → ∀ u v : ℝ,
      |heatKernel r u-heatKernel r v| ≤
        C*|u-v|^(1/4:ℝ)*r^(-(1/8:ℝ))*(heatKernel (2*r) u+heatKernel (2*r) v) := by
  exact ⟨2*Real.exp 1,by positivity,fun _ hr u v => quarter_increment hr u v⟩


end RoughHeatKernel.SpatialEnvelope
