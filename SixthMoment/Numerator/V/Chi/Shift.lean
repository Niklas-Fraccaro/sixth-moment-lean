import SixthMoment.Zeta.Centering.Stirling


namespace SixthMoment.Source
open Complex Real
open scoped Topology
noncomputable section

def chiShiftMainPhase (s u : ℂ) : ℂ :=
  (Real.pi:ℂ)^u*((1-s)/2)^(-u/2)*(s/2)^(-u/2)

theorem chi_shift_main_phase_identity (s u : ℂ)
    (hs : s.im ≠ 0) (hsu : (s+u).im ≠ 0) :
    zetaChi (s+u)/zetaChi s = chiShiftMainPhase s u*
      (normalizedGammaRatio ((1-s)/2) (-u/2)/normalizedGammaRatio (s/2) (u/2)) := by
  have H := centeringFactorAt_eq_gamma_ratios (Real.exp 1) s u hs
    (by simpa only [Real.log_exp,Complex.ofReal_one,div_one] using hsu)
  simp only [centeringFactorAt,gammaChiMainPhase,Real.log_exp,Complex.ofReal_one,div_one] at H
  apply mul_left_cancel₀ (Complex.exp_ne_zero u)
  simpa only [chiShiftMainPhase,mul_div_assoc,mul_assoc] using H

theorem chi_shift_gamma_error {R : ℝ} (hR : 0 ≤ R) (s u : ℂ)
    (hre : |s.re| ≤ 2) (hu : ‖u‖ ≤ R)
    (ht : 192*(R+R^2)+8 ≤ |s.im|) :
    ‖zetaChi (s+u)/zetaChi s-chiShiftMainPhase s u‖ ≤
      ‖chiShiftMainPhase s u‖*(192*(R+R^2)/|s.im|) := by
  have hM : 0 ≤ R+R^2 := by positivity
  have ht0 : 0 < |s.im| := by linarith
  have hs : s.im ≠ 0 := by intro h; simp only [h,abs_zero] at ht0; linarith
  have hsu : (s+u).im ≠ 0 := by
    intro h
    have he : s.im = -u.im := by
      have H : s.im+u.im = 0 := by simpa only [add_im] using h
      linarith
    have hi : |s.im| ≤ R := by rw [he,abs_neg]; exact (abs_im_le_norm u).trans hu
    nlinarith [sq_nonneg R]
  have hpart : ∀ q v : ℂ, -|q.im| ≤ q.re → |q.im| = |s.im|/2 → ‖v‖ ≤ R →
      ‖normalizedGammaRatio q v-1‖ ≤ 48*(R+R^2)/|s.im| := by
    intro q v hq hqi hv
    have hvM : ‖v‖+‖v‖^2 ≤ R+R^2 := by nlinarith [norm_nonneg v]
    have hqi0 : 0 < |q.im| := by rw [hqi]; positivity
    have H := gammaRatio_normalized_error_cone q v hq
      (by rw [hqi]; linarith) (by rw [hqi]; nlinarith)
    change ‖normalizedGammaRatio q v-1‖ ≤ _ at H
    apply H.trans
    calc
      _ ≤ 24*(R+R^2)/|q.im| := div_le_div_of_nonneg_right (by linarith) hqi0.le
      _ = _ := by rw [hqi]; ring
  have hA : |((1-s)/2).im| = |s.im|/2 := by
    simp only [div_ofNat_im,sub_im,one_im,zero_sub,abs_div,abs_neg]
    norm_num
  have hB : |(s/2).im| = |s.im|/2 := by
    simp only [div_ofNat_im,abs_div]
    norm_num
  have hconeA : -|((1-s)/2).im| ≤ ((1-s)/2).re := by
    rw [hA]
    simp only [div_ofNat_re,sub_re,one_re]
    nlinarith [(abs_le.mp hre).2]
  have hconeB : -|(s/2).im| ≤ (s/2).re := by
    rw [hB]
    simp only [div_ofNat_re]
    nlinarith [(abs_le.mp hre).1]
  have hv : ‖u/2‖ ≤ R := by rw [norm_div,Complex.norm_ofNat]; nlinarith [norm_nonneg u]
  have hv' : ‖-u/2‖ ≤ R := by simpa only [neg_div,norm_neg] using hv
  have ha := hpart ((1-s)/2) (-u/2) hconeA hA hv'
  have hb := hpart (s/2) (u/2) hconeB hB hv
  have hδ : 0 ≤ 48*(R+R^2)/|s.im| := by positivity
  have hsmall : 48*(R+R^2)/|s.im| ≤ 1/2 := (div_le_iff₀ ht0).mpr (by linarith)
  have hquot := norm_div_sub_one_le_four hδ hsmall ha hb
  have he (a b p : ℂ) : p*(a/b)-p = p*(a/b-1) := by ring
  rw [chi_shift_main_phase_identity s u hs hsu,he,norm_mul]
  apply (mul_le_mul_of_nonneg_left hquot (norm_nonneg _)).trans_eq
  ring

end
end SixthMoment.Source
