import SixthMoment.Numerator.V.Chi.Gamma
import SixthMoment.Numerator.V.Chi.StirlingPhase


namespace SixthMoment.Source
open Complex Real
noncomputable section

theorem cos_dominant_factor (z : ℂ) :
    2*Complex.cos z = Complex.exp (-z*I)*(1+Complex.exp ((2*z)*I)) := by
  have he : Complex.exp (-z*I)*Complex.exp ((2*z)*I) = Complex.exp (z*I) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [Complex.cos,mul_add,mul_one,he]
  ring

theorem chi_one_sub_main_factorization (c : ℝ) {t : ℝ} (ht : 0 < t) :
    let s := (c:ℂ)+(t:ℂ)*I
    zetaChi (1-s) = chiTransformMain c t*(Complex.Gamma s/gammaStirlingMain s)*
      Complex.exp (chiStirlingLogCorrection c t)*(1+Complex.exp (((Real.pi:ℂ)*s)*I)) := by
  let s := (c:ℂ)+(t:ℂ)*I
  have hs : s.im ≠ 0 := by simpa only [s,add_im,ofReal_im,mul_I_im,ofReal_re,zero_add] using ht.ne'
  have hG : gammaStirlingMain s ≠ 0 := mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity : (0:ℝ) < 2*Real.pi)).ne')
    (Complex.exp_ne_zero _)
  have hgamma : Complex.Gamma s = gammaStirlingMain s*(Complex.Gamma s/gammaStirlingMain s) := by
    field_simp [hG]
  have hcos : 2*Complex.cos ((Real.pi:ℂ)*s/2) =
      Complex.exp (-((Real.pi:ℂ)*s/2)*I)*(1+Complex.exp (((Real.pi:ℂ)*s)*I)) := by
    simpa only [show 2*((Real.pi:ℂ)*s/2) = (Real.pi:ℂ)*s by ring] using
      cos_dominant_factor ((Real.pi:ℂ)*s/2)
  dsimp only
  calc
    _ = (((2*Real.pi:ℝ):ℂ)^(-s)*Complex.Gamma s)*(2*Complex.cos ((Real.pi:ℂ)*s/2)) := by
      rw [chi_one_sub_eq_gamma_cos s hs]
      ring
    _ = (((2*Real.pi:ℝ):ℂ)^(-s)*gammaStirlingMain s*
        Complex.exp (-((Real.pi:ℂ)*s/2)*I))*(Complex.Gamma s/gammaStirlingMain s)*
        (1+Complex.exp (((Real.pi:ℂ)*s)*I)) := by
      conv_lhs => rw [hcos,hgamma]
      ring
    _ = _ := by rw [chiGammaMain_dominant_eq c ht]; ring

theorem norm_three_product_sub_one (a b d : ℂ) {A B C : ℝ}
    (ha : ‖a-1‖ ≤ A) (hb : ‖b-1‖ ≤ B) (hd : ‖d-1‖ ≤ C)
    (hbn : ‖b‖ ≤ 2) (hdn : ‖d‖ ≤ 2) :
    ‖a*b*d-1‖ ≤ 4*A+2*B+C := by
  have hA : 0 ≤ A := (norm_nonneg _).trans ha
  have hB : 0 ≤ B := (norm_nonneg _).trans hb
  have he : a*b*d-1 = ((a-1)*b)*d+(b-1)*d+(d-1) := by ring
  rw [he]
  calc
    _ ≤ ‖((a-1)*b)*d+(b-1)*d‖+‖d-1‖ := norm_add_le _ _
    _ ≤ (‖((a-1)*b)*d‖+‖(b-1)*d‖)+‖d-1‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ = (‖a-1‖*‖b‖*‖d‖+‖b-1‖*‖d‖)+‖d-1‖ := by simp only [norm_mul]
    _ ≤ (A*2*2+B*2)+C := by gcongr
    _ = _ := by ring

theorem chi_shadow_norm_bound (c : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖Complex.exp (((Real.pi:ℂ)*((c:ℂ)+(t:ℂ)*I))*I)‖ ≤ 1/t := by
  have hre : (((Real.pi:ℂ)*((c:ℂ)+(t:ℂ)*I))*I).re = -(Real.pi*t) := by simp
  rw [Complex.norm_exp,hre,Real.exp_neg]
  have H := Real.add_one_le_exp (Real.pi*t)
  have Hπ := mul_le_mul_of_nonneg_right Real.two_le_pi ht.le
  have hle : t ≤ Real.exp (Real.pi*t) := by linarith
  simpa only [one_div] using (one_div_le_one_div_of_le ht hle)

theorem chiTransformMain_norm (c : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖chiTransformMain c t‖ = (t/(2*Real.pi))^(c-1/2) := by
  have hb : 0 < t/(2*Real.pi) := by positivity
  unfold chiTransformMain
  rw [norm_mul,Complex.norm_exp,Complex.norm_cpow_eq_rpow_re_of_pos hb]
  simp only [ofReal_re,mul_I_re,ofReal_im,neg_zero,Real.exp_zero,mul_one]

theorem chi_transform_main_error {c t : ℝ} (hc : 0 < c) (hc' : |c| ≤ 2) (ht : 32 ≤ t) :
    ‖zetaChi (1-((c:ℂ)+(t:ℂ)*I))-chiTransformMain c t‖ ≤
      ‖chiTransformMain c t‖*(130/t) := by
  have ht0 : 0 < t := by linarith
  let s := (c:ℂ)+(t:ℂ)*I
  let a := Complex.Gamma s/gammaStirlingMain s
  let b := Complex.exp (chiStirlingLogCorrection c t)
  let d := 1+Complex.exp (((Real.pi:ℂ)*s)*I)
  have ha : ‖a-1‖ ≤ 16/t := by
    have H := gamma_stirling_relative_error s
      (by simpa only [s,add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero] using hc)
      (by simpa only [s,add_im,ofReal_im,mul_I_im,ofReal_re,zero_add,abs_of_pos ht0] using
        (show (16:ℝ) ≤ t by linarith))
    simpa only [a,s,add_im,ofReal_im,mul_I_im,ofReal_re,zero_add,abs_of_pos ht0] using H
  have hb : ‖b-1‖ ≤ 32/t := by
    have H := chiStirlingLogCorrection_bound hc' (by linarith : 4 ≤ t)
    have hsmall := H.trans ((div_le_one ht0).mpr (by linarith : 16 ≤ t))
    apply (Complex.norm_exp_sub_one_le hsmall).trans
    apply (mul_le_mul_of_nonneg_left H (by norm_num)).trans_eq
    ring
  have hd : ‖d-1‖ ≤ 1/t := by
    simpa only [d,add_sub_cancel_left] using chi_shadow_norm_bound c ht0
  have hbn : ‖b‖ ≤ 2 := by
    have H := norm_sub_le (b-1) (-1:ℂ)
    simp only [sub_neg_eq_add,sub_add_cancel,norm_neg,norm_one] at H
    have hsmall : 32/t ≤ 1 := (div_le_one ht0).mpr ht
    linarith
  have hdn : ‖d‖ ≤ 2 := by
    have H := norm_sub_le (d-1) (-1:ℂ)
    simp only [sub_neg_eq_add,sub_add_cancel,norm_neg,norm_one] at H
    have hsmall : 1/t ≤ 1 := (div_le_one ht0).mpr (by linarith)
    linarith
  have hprod := norm_three_product_sub_one a b d ha hb hd hbn hdn
  have hprod' : ‖a*b*d-1‖ ≤ 130/t := hprod.trans (by
    have H : 4*(16/t)+2*(32/t)+1/t = 129/t := by ring
    rw [H]
    exact div_le_div_of_nonneg_right (by norm_num) ht0.le)
  have he : zetaChi (1-s)-chiTransformMain c t = chiTransformMain c t*(a*b*d-1) := by
    rw [chi_one_sub_main_factorization c ht0]
    dsimp only [a,b,d,s]
    ring
  change ‖zetaChi (1-s)-chiTransformMain c t‖ ≤ _
  rw [he,norm_mul]
  exact mul_le_mul_of_nonneg_left hprod' (norm_nonneg _)

theorem chi_transform_main_explicit_error {c t : ℝ}
    (hc : 0 < c) (hc' : |c| ≤ 2) (ht : 32 ≤ t) :
    ‖zetaChi (1-((c:ℂ)+(t:ℂ)*I))-chiTransformMain c t‖ ≤
      130*(t/(2*Real.pi))^(c-1/2)/t := by
  have H := chi_transform_main_error hc hc' ht
  rw [chiTransformMain_norm c (by linarith : 0 < t)] at H
  apply H.trans_eq
  ring

end
end SixthMoment.Source
