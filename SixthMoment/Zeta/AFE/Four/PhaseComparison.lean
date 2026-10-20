import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import SixthMoment.Zeta.AFE.Four.Definitions


namespace SixthMoment.Source
open Complex
open scoped BigOperators
noncomputable section

theorem principalLog_unit_near_bound {a w : ℂ} (ha : ‖a‖ = 1)
    (harg : |(Complex.log a).im| ≤ Real.pi/2)
    (hw : ‖w-a‖ ≤ 1/2) :
    ‖Complex.log w-Complex.log a‖ ≤ 2*‖w-a‖ := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hv : ‖w/a-1‖ = ‖w-a‖ := by
    rw [div_sub_one ha0, norm_div, ha, div_one]
  have hvsmall : ‖w/a-1‖ ≤ 1/2 := by simpa only [hv] using hw
  have hv0 : w/a ≠ 0 := by
    intro h
    rw [h] at hvsmall
    norm_num at hvsmall
  have hl : ‖Complex.log (w/a)‖ ≤ 2*‖w-a‖ := by
    have hb := Complex.norm_log_one_add_half_le_self hvsmall
    rw [add_sub_cancel, hv] at hb
    linarith [norm_nonneg (w-a)]
  have him : |(Complex.log (w/a)).im| ≤ 1 :=
    (Complex.abs_im_le_norm _).trans (hl.trans (by linarith))
  have he : Complex.exp (Complex.log a+Complex.log (w/a)) = w := by
    rw [Complex.exp_add, Complex.exp_log ha0, Complex.exp_log hv0,
      mul_div_cancel₀ _ ha0]
  have hlow : -Real.pi < (Complex.log a+Complex.log (w/a)).im := by
    simp only [Complex.add_im]
    linarith [(abs_le.mp harg).1, (abs_le.mp him).1, Real.pi_gt_three]
  have hhigh : (Complex.log a+Complex.log (w/a)).im ≤ Real.pi := by
    simp only [Complex.add_im]
    linarith [(abs_le.mp harg).2, (abs_le.mp him).2, Real.pi_gt_three]
  have heq : Complex.log w = Complex.log a+Complex.log (w/a) := by
    calc
      Complex.log w = Complex.log (Complex.exp (Complex.log a+Complex.log (w/a))) :=
        congrArg Complex.log he.symm
      _ = _ := Complex.log_exp hlow hhigh
  rw [heq, add_sub_cancel_left]
  exact hl

theorem principalLog_near_I_bound {w : ℂ} (hw : ‖w-I‖ ≤ 1/2) :
    ‖Complex.log w-Complex.log I‖ ≤ 2*‖w-I‖ := by
  apply principalLog_unit_near_bound (by simp) _ hw
  simp [Complex.log_I, abs_of_nonneg (by positivity : 0 ≤ Real.pi/2)]

theorem principalLog_near_neg_I_bound {w : ℂ} (hw : ‖w-(-I)‖ ≤ 1/2) :
    ‖Complex.log w-Complex.log (-I)‖ ≤ 2*‖w-(-I)‖ := by
  apply principalLog_unit_near_bound (by simp) _ hw
  simp [Complex.log_neg_I, abs_of_nonneg (by positivity : 0 ≤ Real.pi/2)]

def bblrGammaBase (t : ℝ) (α : MomentShifts) (j : Fin 4) : ℂ :=
  (sourceZetaPoints t j+α j)/2

def bblrGammaPhaseCenter : Fin 4 → ℂ := ![I,I,-I,-I]

def bblrGammaPhaseLogError (t : ℝ) (α : MomentShifts) : ℂ :=
  ∑ j : Fin 4, (Complex.log (bblrGammaBase t α j)-
    Complex.log (t/2 : ℂ)-Complex.log (bblrGammaPhaseCenter j))

def bblrGammaMainPhase (t : ℝ) (α : MomentShifts) (z : ℂ) : ℂ :=
  (∏ j : Fin 4, (bblrGammaBase t α j)^(z/2))/(t/2 : ℂ)^(2*z)

@[simp] theorem bblrGammaPhaseCenter_norm (j : Fin 4) :
    ‖bblrGammaPhaseCenter j‖ = 1 := by
  fin_cases j <;> simp [bblrGammaPhaseCenter]

theorem bblrGammaBase_scaled_sub_center {t : ℝ} (ht : t ≠ 0)
    (α : MomentShifts) (j : Fin 4) :
    bblrGammaBase t α j/(t/2 : ℂ)-bblrGammaPhaseCenter j =
      ((1/2 : ℂ)+α j)/(t : ℂ) := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  fin_cases j <;>
    simp [bblrGammaBase, sourceZetaPoints, bblrGammaPhaseCenter,
      criticalLinePoint] <;> field_simp <;> ring


private theorem bblrGammaBase_scaled_norm_le {t A : ℝ}
    (hA : 0 ≤ A) (ht : 4*(A+1) ≤ t) (α : MomentShifts)
    (hα : ∀ j, ‖α j‖ ≤ A) (j : Fin 4) :
    ‖bblrGammaBase t α j/(t/2 : ℂ)-bblrGammaPhaseCenter j‖ ≤ (1/2+A)/t := by
  have htpos : 0 < t := by linarith
  rw [bblrGammaBase_scaled_sub_center htpos.ne' α j, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
  apply div_le_div_of_nonneg_right _ htpos.le
  calc
    ‖(1/2 : ℂ)+α j‖ ≤ ‖(1/2 : ℂ)‖+‖α j‖ := norm_add_le _ _
    _ ≤ 1/2+A := by norm_num; linarith [hα j]

private theorem bblrGammaBase_scaled_ne_zero {t A : ℝ}
    (hA : 0 ≤ A) (ht : 4*(A+1) ≤ t) (α : MomentShifts)
    (hα : ∀ j, ‖α j‖ ≤ A) (j : Fin 4) :
    bblrGammaBase t α j/(t/2 : ℂ) ≠ 0 := by
  have htpos : 0 < t := by linarith
  have hd := bblrGammaBase_scaled_norm_le hA ht α hα j
  have hh : (1/2+A)/t ≤ 1/2 := by
    rw [div_le_iff₀ htpos]; linarith
  intro hz
  rw [hz, zero_sub, norm_neg, bblrGammaPhaseCenter_norm] at hd
  linarith

theorem bblrGammaPhaseLogError_norm_le {t A : ℝ}
    (hA : 0 ≤ A) (ht : 4*(A+1) ≤ t) (α : MomentShifts)
    (hα : ∀ j, ‖α j‖ ≤ A) :
    ‖bblrGammaPhaseLogError t α‖ ≤ (4+8*A)/t := by
  have htpos : 0 < t := by linarith
  have ht2 : 0 < t/2 := by positivity
  have hb (j : Fin 4) :
      ‖Complex.log (bblrGammaBase t α j)-Complex.log (t/2 : ℂ)-
        Complex.log (bblrGammaPhaseCenter j)‖ ≤ 2*((1/2+A)/t) := by
    have hd := bblrGammaBase_scaled_norm_le hA ht α hα j
    have hh : ‖bblrGammaBase t α j/(t/2 : ℂ)-bblrGammaPhaseCenter j‖ ≤ 1/2 := by
      apply hd.trans; rw [div_le_iff₀ htpos]; linarith
    have harg : |(Complex.log (bblrGammaPhaseCenter j)).im| ≤ Real.pi/2 := by
      fin_cases j <;> simp [bblrGammaPhaseCenter, Complex.log_I, Complex.log_neg_I,
        abs_of_nonneg (by positivity : 0 ≤ Real.pi/2)]
    have hl := principalLog_unit_near_bound (bblrGammaPhaseCenter_norm j) harg hh
    have hlog := Complex.log_ofReal_mul ht2
      (bblrGammaBase_scaled_ne_zero hA ht α hα j)
    push_cast at hlog
    rw [Complex.ofReal_log ht2.le] at hlog
    push_cast at hlog
    have he : (t/2 : ℂ)*(bblrGammaBase t α j/(t/2 : ℂ)) =
        bblrGammaBase t α j := by
      exact mul_div_cancel₀ _ (div_ne_zero (Complex.ofReal_ne_zero.mpr htpos.ne') (by norm_num))
    rw [he] at hlog
    rw [hlog]
    have he' : Complex.log (t/2 : ℂ)+Complex.log (bblrGammaBase t α j/(t/2 : ℂ))-
        Complex.log (t/2 : ℂ)-Complex.log (bblrGammaPhaseCenter j) =
        Complex.log (bblrGammaBase t α j/(t/2 : ℂ))-
        Complex.log (bblrGammaPhaseCenter j) := by ring
    rw [he']
    exact hl.trans (mul_le_mul_of_nonneg_left hd (by norm_num))
  unfold bblrGammaPhaseLogError
  calc
    _ ≤ ∑ j : Fin 4, ‖Complex.log (bblrGammaBase t α j)-Complex.log (t/2 : ℂ)-
        Complex.log (bblrGammaPhaseCenter j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 4, 2*((1/2+A)/t) := Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by simp; ring

theorem bblrGammaMainPhase_eq_exp {t A : ℝ}
    (hA : 0 ≤ A) (ht : 4*(A+1) ≤ t) (α : MomentShifts)
    (hα : ∀ j, ‖α j‖ ≤ A) (z : ℂ) :
    bblrGammaMainPhase t α z =
      Complex.exp ((z/2)*bblrGammaPhaseLogError t α) := by
  have htpos : 0 < t := by linarith
  have ht2 : (t/2 : ℂ) ≠ 0 := div_ne_zero (Complex.ofReal_ne_zero.mpr htpos.ne') (by norm_num)
  have hb (j : Fin 4) : bblrGammaBase t α j ≠ 0 := by
    intro h; exact bblrGammaBase_scaled_ne_zero hA ht α hα j (by rw [h]; simp)
  unfold bblrGammaMainPhase
  simp_rw [Complex.cpow_def_of_ne_zero (hb _)]
  rw [← Complex.exp_sum, Complex.cpow_def_of_ne_zero ht2, ← Complex.exp_sub]
  congr 1
  unfold bblrGammaPhaseLogError
  simp only [Fin.sum_univ_succ, Fin.isValue]
  simp [bblrGammaPhaseCenter, Complex.log_I, Complex.log_neg_I]
  ring

theorem bblrGammaMainPhase_error_le {t A : ℝ}
    (hA : 0 ≤ A) (ht : 4*(A+1) ≤ t) (α : MomentShifts)
    (hα : ∀ j, ‖α j‖ ≤ A) (z : ℂ)
    (hz : (2+4*A)*‖z‖ ≤ t) :
    ‖bblrGammaMainPhase t α z-1‖ ≤ (4+8*A)*‖z‖/t := by
  have htpos : 0 < t := by linarith
  rw [bblrGammaMainPhase_eq_exp hA ht α hα z]
  have he : ‖(z/2)*bblrGammaPhaseLogError t α‖ ≤ (2+4*A)*‖z‖/t := by
    rw [norm_mul, norm_div]
    have hb := bblrGammaPhaseLogError_norm_le hA ht α hα
    calc
      _ ≤ (‖z‖/‖(2 : ℂ)‖)*((4+8*A)/t) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by norm_num; ring
  have hs : ‖(z/2)*bblrGammaPhaseLogError t α‖ ≤ 1 :=
    he.trans ((div_le_iff₀ htpos).mpr (by simpa using hz))
  calc
    _ ≤ 2*‖(z/2)*bblrGammaPhaseLogError t α‖ := Complex.norm_exp_sub_one_le hs
    _ ≤ 2*((2+4*A)*‖z‖/t) := mul_le_mul_of_nonneg_left he (by norm_num)
    _ = _ := by ring

end
end SixthMoment.Source
