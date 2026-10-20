import SixthMoment.Numerator.U.Replacement.TimeGamma.Complex

namespace SixthMoment.Source
open Complex Set Metric
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem gammaRatio_cone_norm_le {s u : ℂ}
    (hre : -|s.im| ≤ s.re) (him : 2 ≤ |s.im|)
    (hu : 24*(‖u‖+‖u‖^2) < |s.im|) :
    ‖Gamma (s+u)/Gamma s‖ ≤ 2*‖s^u‖ := by
  have hs0 : s ≠ 0 := by
    intro h
    simp only [h,Complex.zero_im,abs_zero] at him
    norm_num at him
  have hp0 : s^u ≠ 0 := by simp [hs0]
  let R : ℂ := (Gamma (s+u)/Gamma s)/s^u
  have he := SixthMoment.gammaRatio_normalized_error_cone s u hre him hu
  have hE : 24*(‖u‖+‖u‖^2)/|s.im| ≤ 1 :=
    (div_le_one (by linarith)).mpr hu.le
  have hRn : ‖R‖ ≤ 2 := by
    have h := norm_add_le (R-1) (1 : ℂ)
    rw [sub_add_cancel,norm_one] at h
    change ‖R-1‖ ≤ _ at he
    linarith
  have hh : Gamma (s+u)/Gamma s = R*s^u := by dsimp [R]; field_simp
  rw [hh,norm_mul]
  exact mul_le_mul_of_nonneg_right hRn (norm_nonneg _)

theorem bblrTimeGammaQuotient_complex_norm_le {T A : ℝ}
    (hA : 0 ≤ A) (hT : 8*(A+1) ≤ T)
    (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ A)
    {z y : ℂ} (hzre : 0 ≤ z.re)
    (hlarge : 192*(‖z‖+‖z‖^2) < T)
    (hyre : y.re ∈ Icc (3/4 : ℝ) (9/4)) (hyim : |y.im| ≤ 1/4) :
    ‖bblrTimeGammaQuotient T α z y‖ ≤
      16*(2*T)^(2*z.re)*Real.exp (2*Real.pi*|z.im|) := by
  have hT0 : 0 < T := by linarith
  have hz2 : ‖z/2‖ = ‖z‖/2 := by rw [norm_div]; norm_num
  have hf (j : Fin 4) :
      ‖Gamma (bblrTimeGammaBase T α y j+z/2)/
          Gamma (bblrTimeGammaBase T α y j)‖ ≤
        2*(2*T)^(z.re/2)*Real.exp (Real.pi*|z.im|/2) := by
    let s := bblrTimeGammaBase T α y j
    have hg := bblrTimeGammaBase_geometry hA hT α hα hyre hyim j
    have him : 2 ≤ |s.im| := by dsimp [s]; linarith [hg.1]
    have hu : 24*(‖z/2‖+‖z/2‖^2) < |s.im| := by
      rw [hz2]
      dsimp [s]
      nlinarith [hg.1,norm_nonneg z,sq_nonneg ‖z‖]
    have hr := gammaRatio_cone_norm_le hg.2.1 him hu
    have hs0 : s ≠ 0 := by
      intro hs
      simp only [hs,Complex.zero_im,abs_zero] at him
      norm_num at him
    have hp : ‖s^(z/2)‖ ≤ (2*T)^(z.re/2)*Real.exp (Real.pi*|z.im|/2) := by
      rw [Complex.norm_cpow_of_ne_zero hs0,Complex.div_ofNat_re,
        Complex.div_ofNat_im,div_eq_mul_inv,← Real.exp_neg]
      apply mul_le_mul
      · exact Real.rpow_le_rpow (norm_nonneg s) hg.2.2 (by positivity)
      · apply Real.exp_le_exp.mpr
        have ha := Complex.abs_arg_le_pi s
        have hh := mul_le_mul_of_nonneg_right ha (abs_nonneg z.im)
        have hneg := neg_le_abs (Complex.arg s*z.im)
        rw [abs_mul] at hneg
        linarith
      · positivity
      · positivity
    have hh := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)
    exact hr.trans (by simpa only [mul_assoc] using hh)
  have hn : ‖bblrTimeGammaQuotient T α z y‖ ≤
      (2*(2*T)^(z.re/2)*Real.exp (Real.pi*|z.im|/2))^4 := by
    unfold bblrTimeGammaQuotient
    calc
      _ ≤ ∏ j : Fin 4, ‖Gamma (bblrTimeGammaBase T α y j+z/2)/
          Gamma (bblrTimeGammaBase T α y j)‖ := Finset.norm_prod_le _ _
      _ ≤ ∏ _j : Fin 4, (2*(2*T)^(z.re/2)*Real.exp (Real.pi*|z.im|/2)) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hf j)
      _ = _ := by simp
  have hp : ((2*T)^(z.re/2))^4 = (2*T)^(2*z.re) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity : 0 ≤ 2*T)]
    congr 1
    ring
  have he : (Real.exp (Real.pi*|z.im|/2))^4 = Real.exp (2*Real.pi*|z.im|) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  apply hn.trans_eq
  rw [mul_pow,mul_pow,hp,he]
  norm_num

end
end SixthMoment.Source
