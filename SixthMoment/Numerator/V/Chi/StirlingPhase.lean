import SixthMoment.Numerator.V.Chi.Phase
import SixthMoment.Zeta.Gamma.Stirling


namespace SixthMoment.Source
open Complex Real
noncomputable section

def chiTransformMain (c t : ℝ) : ℂ :=
  ((t/(2*Real.pi):ℝ):ℂ)^((c-1/2:ℝ):ℂ)*
    Complex.exp (((t*Real.log (t/(2*Real.pi))-t-Real.pi/4:ℝ):ℂ)*I)

def chiStirlingLogCorrection (c t : ℝ) : ℂ :=
  ((c:ℂ)+(t:ℂ)*I-1/2)*Complex.log (1-I*(c:ℂ)/(t:ℂ))-(c:ℂ)

theorem log_vertical_point (c : ℝ) {t : ℝ} (ht : 0 < t) :
    Complex.log ((c:ℂ)+(t:ℂ)*I) =
      (Real.log t:ℂ)+(Real.pi:ℂ)/2*I+Complex.log (1-I*(c:ℂ)/(t:ℂ)) := by
  let w : ℂ := 1-I*(c:ℂ)/(t:ℂ)
  have htC : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hwre : w.re = 1 := by
    have he : I*(c:ℂ)/(t:ℂ) = ((c/t:ℝ):ℂ)*I := by push_cast; ring
    dsimp only [w]
    rw [he]
    simp
  have hwpos : 0 < w.re := by rw [hwre]; norm_num
  have hw0 : w ≠ 0 := by intro h; simp only [h,zero_re] at hwpos; linarith
  have harg := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hwpos))
  have hlog := (Complex.log_mul_eq_add_log_iff I_ne_zero hw0).mpr
    (show I.arg+w.arg ∈ Set.Ioc (-Real.pi) Real.pi from by
      rw [Complex.arg_I]
      constructor <;> linarith [harg.1,harg.2,Real.pi_pos])
  have hp : (t:ℂ)*(I*w) = (c:ℂ)+(t:ℂ)*I := by
    dsimp only [w]
    field_simp [htC]
    ring_nf
    simp [Complex.I_sq]
  rw [← hp,Complex.log_ofReal_mul ht (mul_ne_zero I_ne_zero hw0),hlog,Complex.log_I]
  dsimp only [w]
  ring

theorem chiStirlingLogCorrection_bound {c t : ℝ} (hc : |c| ≤ 2) (ht : 4 ≤ t) :
    ‖chiStirlingLogCorrection c t‖ ≤ 16/t := by
  have ht0 : 0 < t := by linarith
  have htC : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
  let w : ℂ := -I*(c:ℂ)/(t:ℂ)
  have hw : ‖w‖ = |c|/t := by simp [w,abs_of_pos ht0]
  have hsmall : ‖w‖ ≤ 1/2 := by rw [hw]; apply (div_le_iff₀ ht0).mpr; linarith
  have hlog := SixthMoment.norm_log_one_add_sub_self_le_sq hsmall
  have hca : |c-1/2| ≤ 5/2 := by
    have H := abs_sub c (1/2:ℝ)
    norm_num at H
    linarith
  have hS : ‖(c:ℂ)+(t:ℂ)*I-1/2‖ ≤ t+5/2 := by
    have H := Complex.norm_le_abs_re_add_abs_im ((c:ℂ)+(t:ℂ)*I-1/2)
    have hre : ((c:ℂ)+(t:ℂ)*I-1/2).re = c-1/2 := by simp
    have him : ((c:ℂ)+(t:ℂ)*I-1/2).im = t := by simp
    rw [hre,him,abs_of_pos ht0] at H
    linarith
  have hid : chiStirlingLogCorrection c t =
      ((c:ℂ)+(t:ℂ)*I-1/2)*(Complex.log (1+w)-w)-
        I*(c:ℂ)*((c:ℂ)-1/2)/(t:ℂ) := by
    have harg : 1+w = 1-I*(c:ℂ)/(t:ℂ) := by dsimp [w]; ring
    rw [harg]
    dsimp only [chiStirlingLogCorrection,w]
    field_simp [htC]
    ring_nf
    simp [Complex.I_sq]
  have hsecond : ‖I*(c:ℂ)*((c:ℂ)-1/2)/(t:ℂ)‖ ≤ 5/t := by
    have he : (c:ℂ)-(1/2:ℂ) = ((c-1/2:ℝ):ℂ) := by push_cast; ring
    calc
      _ = |c| * |c-1/2|/t := by
        rw [he]
        simp only [norm_div,norm_mul,Complex.norm_I,Complex.norm_real,
          Real.norm_eq_abs,abs_of_pos ht0,one_mul]
      _ ≤ 2*(5/2)/t := div_le_div_of_nonneg_right
        (mul_le_mul hc hca (abs_nonneg _) (by norm_num)) ht0.le
      _ = _ := by ring
  have hfirst : ‖((c:ℂ)+(t:ℂ)*I-1/2)*(Complex.log (1+w)-w)‖ ≤
      (t+5/2)*(2/t)^2 := by
    rw [norm_mul]
    apply (mul_le_mul hS hlog (norm_nonneg _) (by linarith)).trans
    rw [hw]
    gcongr
  rw [hid]
  apply (norm_sub_le _ _).trans ((add_le_add hfirst hsecond).trans ?_)
  have he : (t+5/2)*(2/t)^2+5/t = (9*t+10)/t^2 := by field_simp; ring
  rw [he]
  apply (div_le_div_iff₀ (sq_pos_of_pos ht0) ht0).mpr
  have hsq : 4*t ≤ t^2 := by
    have H := mul_le_mul_of_nonneg_left ht ht0.le
    nlinarith
  nlinarith

theorem chiGammaMain_dominant_eq (c : ℝ) {t : ℝ} (ht : 0 < t) :
    ((2*Real.pi:ℝ):ℂ)^(-((c:ℂ)+(t:ℂ)*I))*
        gammaStirlingMain ((c:ℂ)+(t:ℂ)*I)*
        Complex.exp (-((Real.pi:ℂ)*((c:ℂ)+(t:ℂ)*I)/2)*I) =
      chiTransformMain c t*Complex.exp (chiStirlingLogCorrection c t) := by
  have hp : 0 < 2*Real.pi := by positivity
  have hp0 : ((2*Real.pi:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have hb : 0 < t/(2*Real.pi) := div_pos ht hp
  have hb0 : ((t/(2*Real.pi):ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have hrootR : Real.sqrt (2*Real.pi) = Real.exp (Real.log (2*Real.pi)/2) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hp]
    congr 1
    ring
  have hroot : (Real.sqrt (2*Real.pi):ℂ) = Complex.exp ((Real.log (2*Real.pi):ℂ)/2) := by
    simpa only [Complex.ofReal_exp,Complex.ofReal_div,Complex.ofReal_ofNat] using
      congrArg Complex.ofReal hrootR
  have hlog : Real.log (t/(2*Real.pi)) = Real.log t-Real.log (2*Real.pi) :=
    Real.log_div ht.ne' hp.ne'
  have hlogC : (Real.log (t/(2*Real.pi)):ℂ) =
      (Real.log t:ℂ)-(Real.log (2*Real.pi):ℂ) := by exact_mod_cast hlog
  unfold gammaStirlingMain chiTransformMain chiStirlingLogCorrection
  rw [Complex.cpow_def_of_ne_zero hp0,Complex.cpow_def_of_ne_zero hb0,
    hroot,log_vertical_point c ht,
    ← Complex.ofReal_log hp.le,← Complex.ofReal_log hb.le]
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  simp only [hlogC]
  ring

end
end SixthMoment.Source
