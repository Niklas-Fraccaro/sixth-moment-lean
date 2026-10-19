import Sechstmoment.Denominator.Gram.NonstationaryChiDecay
import Sechstmoment.Numerator.U.ZeroModes.Transforms.PositiveTimeMellinStripDecay
import Sechstmoment.Numerator.V.Chi.Phase

/-! The actual logarithmically shifted time-weight family. Its support,
smoothness, derivative bounds and Mellin decay have common constants. -/

namespace Sechstmoment.Source
open Complex Real Set MeasureTheory
open scoped BigOperators ContDiff
noncomputable section

def noDPTimeWeight (w : ℝ → ℂ) (T : ℝ) (u : ℂ) (x : ℝ) : ℂ :=
  chiShiftLeadingPhase T u*a03ProfileProduct w (fun y : ℝ => (y:ℂ)^(-u)) x

theorem noDPTimeWeight_tsupport (w : ℝ → ℂ) (T : ℝ) (u : ℂ) :
    tsupport (noDPTimeWeight w T u) ⊆ tsupport w :=
  tsupport_mul_subset_right.trans (a03_profile_product_tsupport _ _)

theorem noDPTimeWeight_contDiff {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1:ℝ) 2) (T : ℝ) (u : ℂ) :
    ContDiff ℝ ∞ (noDPTimeWeight w T u) := by
  apply contDiff_const.mul
  apply a03_profile_product_contDiff hw
  intro x hx
  exact positive_cpow_contDiffAt (-u) (zero_lt_one.trans_le (hws hx).1)

theorem noDPTimeWeight_eq_scaled_power (w : ℝ → ℂ) {T x : ℝ}
    (hT : 0 < T) (hx : 0 < x) (u : ℂ) :
    noDPTimeWeight w T u x = w x*chiShiftLeadingPhase (T*x) u := by
  have hp : 0 < T/(2*Real.pi) := by positivity
  unfold noDPTimeWeight a03ProfileProduct chiShiftLeadingPhase
  rw [show T*x/(2*Real.pi) = (T/(2*Real.pi))*x by ring,
    Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hp.le hx.le]
  ring

theorem logarithmic_time_shift_norm {T R : ℝ} (hL : 1 ≤ Real.log T)
    (hR : 0 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖z/(Real.log T:ℂ)‖ ≤ R := by
  have hL0 : 0 < Real.log T := by linarith
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL0]
  exact (div_le_div_of_nonneg_right hz hL0.le).trans (div_le_self hR hL)

theorem time_weight_leading_scalar_bound {T R : ℝ} (hT : 2*Real.pi ≤ T)
    (hL : 1 ≤ Real.log T) (hR : 0 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖chiShiftLeadingPhase T (z/(Real.log T:ℂ))‖ ≤ Real.exp R := by
  have hL0 : 0 < Real.log T := by linarith
  have hp : 0 < 2*Real.pi := by positivity
  have hT0 : 0 < T := hp.trans_le hT
  have hb1 : 1 ≤ T/(2*Real.pi) := (le_div_iff₀ hp).mpr (by simpa using hT)
  have hb0 : 0 < T/(2*Real.pi) := zero_lt_one.trans_le hb1
  have hbT : T/(2*Real.pi) ≤ T := by
    apply (div_le_iff₀ hp).mpr
    exact le_mul_of_one_le_right hT0.le (by linarith [Real.two_le_pi])
  have hlog0 : 0 ≤ Real.log (T/(2*Real.pi)) := Real.log_nonneg hb1
  have hlogL : Real.log (T/(2*Real.pi)) ≤ Real.log T := Real.log_le_log hb0 hbT
  have hu : ‖z/(Real.log T:ℂ)‖ ≤ R/Real.log T := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL0]
    exact div_le_div_of_nonneg_right hz hL0.le
  have hre : -(z/(Real.log T:ℂ)).re ≤ R/Real.log T := by
    have H := Complex.re_le_norm (-(z/(Real.log T:ℂ)))
    simp only [neg_re,norm_neg] at H
    exact H.trans hu
  unfold chiShiftLeadingPhase
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hb0,neg_re,Real.rpow_def_of_pos hb0]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ Real.log (T/(2*Real.pi))*(R/Real.log T) :=
      mul_le_mul_of_nonneg_left hre hlog0
    _ ≤ Real.log T*(R/Real.log T) :=
      mul_le_mul_of_nonneg_right hlogL (div_nonneg hR hL0.le)
    _ = R := by field_simp [hL0.ne']

theorem noDPTimeWeight_uniform_derivative_bounds {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∀ T : ℝ, 2*Real.pi ≤ T →
      1 ≤ Real.log T → ∀ z : ℂ, ‖z‖ ≤ R → ∀ j x,
      ‖iteratedDeriv j (noDPTimeWeight w T (z/(Real.log T:ℂ))) x‖ ≤ C j := by
  obtain ⟨D,hD,hderiv⟩ := d06_time_power_profile_uniform_derivative_bounds hw hws hR
  refine ⟨fun j => Real.exp R*D j,fun j => mul_nonneg (Real.exp_pos _).le (hD j),?_⟩
  intro T hT hL z hz j x
  have hu : ‖-(z/(Real.log T:ℂ))‖ ≤ R := by
    simpa only [norm_neg] using logarithmic_time_shift_norm hL hR hz
  unfold noDPTimeWeight
  rw [iteratedDeriv_const_mul_field,norm_mul]
  exact mul_le_mul (time_weight_leading_scalar_bound hT hL hR hz)
    (hderiv _ hu j x) (norm_nonneg _) (Real.exp_pos _).le

theorem noDPTimeWeight_mellin (w : ℝ → ℂ) (T : ℝ) (u s : ℂ) :
    mellin (noDPTimeWeight w T u) s =
      chiShiftLeadingPhase T u*mellin w (s-u) := by
  unfold mellin
  simp only [smul_eq_mul]
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  unfold noDPTimeWeight a03ProfileProduct
  calc
    _ = chiShiftLeadingPhase T u*((x:ℂ)^(s-1)*(x:ℂ)^(-u)*w x) := by ring
    _ = _ := by
      rw [← Complex.cpow_add _ _ hx0,show s-1+(-u) = s-u-1 by ring]

theorem noDPTimeWeight_uniform_mellin_decay {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {R : ℝ} (hR : 0 ≤ R) (κ : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2*Real.pi ≤ T → 1 ≤ Real.log T →
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ v : ℝ,
      (1+|v|)^N*‖mellin (noDPTimeWeight w T (z/(Real.log T:ℂ)))
        ((κ:ℂ)+(v:ℂ)*I)‖ ≤ C := by
  obtain ⟨D,hD,hstrip⟩ := a03PositiveTimeMellin_strip_full_height_decay hw hws (κ-R) (κ+R) N
  refine ⟨Real.exp R*(1+R)^N*D,by positivity,?_⟩
  intro T hT hL z hz v
  let u := z/(Real.log T:ℂ)
  have hu : ‖u‖ ≤ R := logarithmic_time_shift_norm hL hR hz
  have hre := abs_le.mp ((Complex.abs_re_le_norm u).trans hu)
  have him : |u.im| ≤ R := (Complex.abs_im_le_norm u).trans hu
  have hκ : κ-u.re ∈ Icc (κ-R) (κ+R) := ⟨by linarith,by linarith⟩
  have hs : (κ:ℂ)+(v:ℂ)*I-u = ((κ-u.re:ℝ):ℂ)+((v-u.im:ℝ):ℂ)*I := by
    apply Complex.ext <;> simp
  have hdec := hstrip _ hκ (v-u.im)
  have hv : 1+|v| ≤ (1+R)*(1+|v-u.im|) := by
    have H := abs_add_le (v-u.im) u.im
    rw [sub_add_cancel] at H
    nlinarith [abs_nonneg (v-u.im)]
  rw [noDPTimeWeight_mellin,norm_mul,hs]
  calc
    _ ≤ ((1+R)*(1+|v-u.im|))^N*
        (Real.exp R*‖mellin w (((κ-u.re:ℝ):ℂ)+((v-u.im:ℝ):ℂ)*I)‖) := by
      gcongr
      exact time_weight_leading_scalar_bound hT hL hR hz
    _ = (Real.exp R*(1+R)^N)*
        ((1+|v-u.im|)^N*‖mellin w (((κ-u.re:ℝ):ℂ)+((v-u.im:ℝ):ℂ)*I)‖) := by
      rw [mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdec (by positivity)

end
end Sechstmoment.Source
