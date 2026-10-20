import Sechstmoment.Numerator.V.Chi.ShiftedIntegrability


namespace Sechstmoment.Source
open Complex Real Set
noncomputable section

theorem noDPRightLine_chi_shift_geometry {T R : ℝ} (hR : 0 ≤ R)
    (hL : 4*(2*R+2) ≤ Real.log T) {u : ℂ} (hu : ‖u‖ ≤ R/Real.log T) :
    noDPRightLine T R-u.re ∈ Icc (1:ℝ) (5/4) ∧ ‖u‖ ≤ 1/8 ∧
      noDPRightLine T R-u.re ≤ 1+(2*R+2)/Real.log T := by
  have hL0 : 0 < Real.log T := by linarith
  have hre := abs_le.mp ((Complex.abs_re_le_norm u).trans hu)
  have hsmall : ‖u‖ ≤ 1/8 := hu.trans ((div_le_iff₀ hL0).mpr (by linarith))
  have hsum : (R+2)/Real.log T+R/Real.log T = (2*R+2)/Real.log T := by ring
  have hdiff : (R+2)/Real.log T-R/Real.log T = 2/Real.log T := by ring
  have hupper : noDPRightLine T R-u.re ≤ 1+(2*R+2)/Real.log T := by
    dsimp only [noDPRightLine]
    linarith [hre.1]
  have hratio : (2*R+2)/Real.log T ≤ 1/4 := (div_le_iff₀ hL0).mpr (by linarith)
  refine ⟨⟨?_,by linarith⟩,hsmall,hupper⟩
  dsimp only [noDPRightLine]
  have hpos : 0 ≤ 2/Real.log T := by positivity
  linarith [hre.2]

theorem shifted_chi_starting_line_bound {T R : ℝ} (hT : 64 ≤ T) (hR : 0 ≤ R)
    (hL : 4*(2*R+2) ≤ Real.log T) {u : ℂ} (hu : ‖u‖ ≤ R/Real.log T)
    {t : ℝ} (ht : t ∈ Icc T (2*T)) :
    ‖zetaChi (1-((noDPRightLine T R:ℂ)+(t:ℂ)*I)+u)‖ ≤
      131*Real.exp (2*R+2)*T^(1/2:ℝ) := by
  obtain ⟨hc,hsmall,hcline⟩ := noDPRightLine_chi_shift_geometry hR hL hu
  have him : |u.im| ≤ T/2 := (Complex.abs_im_le_norm u).trans
    (hsmall.trans (by linarith))
  have htime : t-u.im ∈ Icc (T/2) (3*T) := by
    have H := abs_le.mp him
    exact ⟨by linarith [ht.1,H.2],by linarith [ht.2,H.1]⟩
  rw [chi_shift_vertical_identity]
  exact chi_transform_wide_log_line_bound hT
    ⟨by linarith [hc.1],by linarith [hc.2]⟩ hcline htime

end
end Sechstmoment.Source
