import Mathlib.Analysis.SpecialFunctions.Pow.Real
import SixthMoment.Analysis.Complex.HorizontalLog
import SixthMoment.Numerator.V.Chi.Shift


namespace SixthMoment.Source
open Complex Real Set
noncomputable section

def chiPhaseLogError (s : ℂ) : ℂ :=
  Complex.log ((1-s)/2)+Complex.log (s/2)-2*(Real.log (|s.im|/2):ℂ)

def chiShiftLeadingPhase (t : ℝ) (u : ℂ) : ℂ := ((t/(2*Real.pi):ℝ):ℂ)^(-u)

theorem chiShiftMainPhase_eq_leading (s u : ℂ) (ht : s.im ≠ 0) :
    chiShiftMainPhase s u = chiShiftLeadingPhase |s.im| u*
      Complex.exp ((-u/2)*chiPhaseLogError s) := by
  have hA : (1-s)/2 ≠ 0 := by
    intro h
    have H := congrArg Complex.im h
    simp only [div_ofNat_im,sub_im,one_im,zero_sub,zero_im] at H
    apply ht
    linarith
  have hB : s/2 ≠ 0 := by
    intro h
    have H := congrArg Complex.im h
    simp only [div_ofNat_im,zero_im] at H
    apply ht
    linarith
  have hπ : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hab : 0 < |s.im| := abs_pos.mpr ht
  have hb : 0 < |s.im|/(2*Real.pi) := by positivity
  have hb0 : ((|s.im|/(2*Real.pi):ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have ht2 : 0 < |s.im|/2 := by positivity
  have hlog : Real.log (|s.im|/(2*Real.pi)) = Real.log (|s.im|/2)-Real.log Real.pi := by
    rw [show |s.im|/(2*Real.pi) = (|s.im|/2)/Real.pi by field_simp,
      Real.log_div ht2.ne' Real.pi_ne_zero]
  have hc : (Real.log (|s.im|/(2*Real.pi)):ℂ) =
      (Real.log (|s.im|/2):ℂ)-(Real.log Real.pi:ℂ) := by exact_mod_cast hlog
  simp only [chiShiftMainPhase,chiShiftLeadingPhase,
    Complex.cpow_def_of_ne_zero hπ,Complex.cpow_def_of_ne_zero hA,
    Complex.cpow_def_of_ne_zero hB,Complex.cpow_def_of_ne_zero hb0,
    ← Complex.ofReal_log Real.pi_pos.le,← Complex.ofReal_log hb.le,← Complex.exp_add]
  congr 1
  rw [hc]
  unfold chiPhaseLogError
  ring

theorem chiPhaseLogError_bound (s : ℂ) (ht : s.im ≠ 0) (hre : |s.re| ≤ 2) :
    ‖chiPhaseLogError s‖ ≤ 5/|s.im| := by
  have hab : 0 < |s.im| := abs_pos.mpr ht
  have ht2 : s.im/2 ≠ 0 := div_ne_zero ht (by norm_num)
  have hA : ((1-s)/2) = (((1-s.re)/2:ℝ):ℂ)+((-(s.im/2):ℝ):ℂ)*I := by
    conv_lhs => rw [← Complex.re_add_im s]
    push_cast
    ring
  have hB : s/2 = ((s.re/2:ℝ):ℂ)+((s.im/2:ℝ):ℂ)*I := by
    apply Complex.ext <;> simp [div_ofNat_re,div_ofNat_im]
  have hratio (a : ℝ) : |a/2|/|s.im/2| = |a|/|s.im| := by
    norm_num [abs_div]
    field_simp [hab.ne']
  have HA := norm_log_horizontal_sub ((1-s.re)/2) (-(s.im/2)) (neg_ne_zero.mpr ht2)
  have HB := norm_log_horizontal_sub (s.re/2) (s.im/2) ht2
  rw [← hA,abs_neg,hratio] at HA
  rw [← hB,hratio] at HB
  have hpure_pos (t : ℝ) (htp : 0 < t) : Complex.log (((-(t/2):ℝ):ℂ)*I)+
      Complex.log (((t/2:ℝ):ℂ)*I) = 2*(Real.log (t/2):ℂ) := by
    have ht2p : 0 < t/2 := by positivity
    have ha : (((-(t/2):ℝ):ℂ)*I) = ((t/2:ℝ):ℂ)*(-I) := by push_cast; ring
    rw [ha,Complex.log_ofReal_mul ht2p (neg_ne_zero.mpr I_ne_zero),
      Complex.log_ofReal_mul ht2p I_ne_zero,Complex.log_I,Complex.log_neg_I]
    ring
  have hpure : Complex.log (((-(s.im/2):ℝ):ℂ)*I)+
      Complex.log (((s.im/2:ℝ):ℂ)*I) = 2*(Real.log (|s.im|/2):ℂ) := by
    rcases lt_or_gt_of_ne ht with hneg | hpos
    · rw [abs_of_neg hneg]
      simpa only [neg_div,neg_neg,add_comm] using hpure_pos (-s.im) (by linarith)
    · rw [abs_of_pos hpos]
      exact hpure_pos s.im hpos
  have hid : chiPhaseLogError s =
      (Complex.log ((1-s)/2)-Complex.log (((-(s.im/2):ℝ):ℂ)*I))+
        (Complex.log (s/2)-Complex.log (((s.im/2:ℝ):ℂ)*I)) := by
    unfold chiPhaseLogError
    rw [← hpure]
    ring
  rw [hid]
  calc
    _ ≤ ‖Complex.log ((1-s)/2)-Complex.log (((-(s.im/2):ℝ):ℂ)*I)‖+
        ‖Complex.log (s/2)-Complex.log (((s.im/2:ℝ):ℂ)*I)‖ := norm_add_le _ _
    _ ≤ |1-s.re|/|s.im|+|s.re|/|s.im| := add_le_add HA HB
    _ = (|1-s.re|+|s.re|)/|s.im| := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by
      have H := abs_sub (1:ℝ) s.re
      norm_num at H
      linarith) hab.le

theorem chiShiftMainPhase_error {R : ℝ} (hR : 0 ≤ R) (s u : ℂ)
    (ht : s.im ≠ 0) (hre : |s.re| ≤ 2) (hu : ‖u‖ ≤ R) (hlarge : 5*R ≤ |s.im|) :
    ‖chiShiftMainPhase s u-chiShiftLeadingPhase |s.im| u‖ ≤
      ‖chiShiftLeadingPhase |s.im| u‖*(5*R/|s.im|) := by
  have hab : 0 < |s.im| := abs_pos.mpr ht
  have he : ‖(-u/2)*chiPhaseLogError s‖ ≤ 5*R/(2*|s.im|) := by
    rw [norm_mul,norm_div,norm_neg,Complex.norm_ofNat]
    apply (mul_le_mul (div_le_div_of_nonneg_right hu (by norm_num))
      (chiPhaseLogError_bound s ht hre) (norm_nonneg _) (by positivity)).trans_eq
    ring
  have hsmall : ‖(-u/2)*chiPhaseLogError s‖ ≤ 1 := by
    apply he.trans
    apply (div_le_one (by positivity : 0 < 2*|s.im|)).mpr
    linarith
  rw [chiShiftMainPhase_eq_leading s u ht,
    show chiShiftLeadingPhase |s.im| u*Complex.exp ((-u/2)*chiPhaseLogError s)-
      chiShiftLeadingPhase |s.im| u = chiShiftLeadingPhase |s.im| u*
        (Complex.exp ((-u/2)*chiPhaseLogError s)-1) by ring,norm_mul]
  apply (mul_le_mul_of_nonneg_left (Complex.norm_exp_sub_one_le hsmall)
    (norm_nonneg _)).trans
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (by norm_num))
    (norm_nonneg _)).trans_eq
  ring

theorem chi_shift_leading_error {R : ℝ} (hR : 0 ≤ R) (s u : ℂ)
    (hre : |s.re| ≤ 2) (hu : ‖u‖ ≤ R) (ht : 192*(R+R^2)+8 ≤ |s.im|) :
    ‖zetaChi (s+u)/zetaChi s-chiShiftLeadingPhase |s.im| u‖ ≤
      ‖chiShiftLeadingPhase |s.im| u‖*((384*(R+R^2)+5*R)/|s.im|) := by
  have ht0 : 0 < |s.im| := by nlinarith [sq_nonneg R]
  have hs : s.im ≠ 0 := abs_pos.mp ht0
  have hlarge : 5*R ≤ |s.im| := by nlinarith [sq_nonneg R]
  have hphase := chiShiftMainPhase_error hR s u hs hre hu hlarge
  have hδ : 5*R/|s.im| ≤ 1 := (div_le_one ht0).mpr hlarge
  have hp : ‖chiShiftMainPhase s u‖ ≤ 2*‖chiShiftLeadingPhase |s.im| u‖ := by
    have hn := norm_sub_le (chiShiftMainPhase s u-chiShiftLeadingPhase |s.im| u)
      (-chiShiftLeadingPhase |s.im| u)
    simp only [sub_neg_eq_add,sub_add_cancel,norm_neg] at hn
    have hmul := mul_le_mul_of_nonneg_left hδ (norm_nonneg (chiShiftLeadingPhase |s.im| u))
    nlinarith
  have hgamma := chi_shift_gamma_error hR s u hre hu ht
  have he : zetaChi (s+u)/zetaChi s-chiShiftLeadingPhase |s.im| u =
      (zetaChi (s+u)/zetaChi s-chiShiftMainPhase s u)+
        (chiShiftMainPhase s u-chiShiftLeadingPhase |s.im| u) := by ring
  rw [he]
  apply (norm_add_le _ _).trans ((add_le_add hgamma hphase).trans ?_)
  have hm : 0 ≤ 192*(R+R^2)/|s.im| := by positivity
  calc
    _ ≤ (2*‖chiShiftLeadingPhase |s.im| u‖)*(192*(R+R^2)/|s.im|)+
        ‖chiShiftLeadingPhase |s.im| u‖*(5*R/|s.im|) :=
      add_le_add (mul_le_mul_of_nonneg_right hp hm) le_rfl
    _ = _ := by ring

theorem chi_shift_log_scaled_error {T R : ℝ} (hR : 0 ≤ R)
    (hL : 1 ≤ Real.log T) (hTπ : 2*Real.pi ≤ T)
    (hlarge : 192*(R+R^2)+8 ≤ T) (s z : ℂ) (hre : |s.re| ≤ 2)
    (him : |s.im| ∈ Icc T (2*T)) (hz : ‖z‖ ≤ R) :
    ‖zetaChi (s+z/(Real.log T:ℂ))/zetaChi s-
        chiShiftLeadingPhase |s.im| (z/(Real.log T:ℂ))‖ ≤
      Real.exp R*(384*(R+R^2)+5*R)/T := by
  let L := Real.log T
  let t := |s.im|
  let u := z/(L:ℂ)
  let K := 384*(R+R^2)+5*R
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hT0 : 0 < T := (by positivity : 0 < 2*Real.pi).trans_le hTπ
  have ht0 : 0 < t := hT0.trans_le him.1
  have hu : ‖u‖ ≤ R/L := by
    dsimp only [u]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL0]
    exact div_le_div_of_nonneg_right hz hL0.le
  have huR : ‖u‖ ≤ R := hu.trans (div_le_self hR hL)
  have hπ0 : 0 < 2*Real.pi := by positivity
  have hb1 : 1 ≤ t/(2*Real.pi) :=
    (le_div_iff₀ hπ0).mpr (by simpa using hTπ.trans him.1)
  have hb : 0 < t/(2*Real.pi) := zero_lt_one.trans_le hb1
  have hbT : t/(2*Real.pi) ≤ T := by
    apply (div_le_iff₀ hπ0).mpr
    have H := mul_le_mul_of_nonneg_left
      (show (2:ℝ) ≤ 2*Real.pi by linarith [Real.two_le_pi]) hT0.le
    have htUpper : t ≤ 2*T := him.2
    nlinarith
  have hlog0 : 0 ≤ Real.log (t/(2*Real.pi)) := Real.log_nonneg hb1
  have hlogL : Real.log (t/(2*Real.pi)) ≤ L := Real.log_le_log hb hbT
  have hminus : -u.re ≤ R/L := by
    have H := Complex.re_le_norm (-u)
    simp only [neg_re,norm_neg] at H
    exact H.trans hu
  have hnorm : ‖chiShiftLeadingPhase t u‖ ≤ Real.exp R := by
    unfold chiShiftLeadingPhase
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hb,Real.rpow_def_of_pos hb,neg_re]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ Real.log (t/(2*Real.pi))*(R/L) :=
        mul_le_mul_of_nonneg_left hminus hlog0
      _ ≤ L*(R/L) := mul_le_mul_of_nonneg_right hlogL (div_nonneg hR hL0.le)
      _ = R := by field_simp [hL0.ne']
  have H := chi_shift_leading_error hR s u hre huR (hlarge.trans him.1)
  change ‖zetaChi (s+u)/zetaChi s-chiShiftLeadingPhase t u‖ ≤ Real.exp R*K/T
  apply H.trans
  have hK : 0 ≤ K := by dsimp [K]; positivity
  calc
    _ ≤ Real.exp R*(K/t) := mul_le_mul_of_nonneg_right hnorm (div_nonneg hK ht0.le)
    _ = Real.exp R*K/t := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hT0 him.1

end
end SixthMoment.Source
