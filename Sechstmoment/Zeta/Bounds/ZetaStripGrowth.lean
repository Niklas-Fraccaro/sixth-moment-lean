import Sechstmoment.Zeta.Bounds.ZetaLeftBoundary

/-! A genuine exponential growth bound on a strip crossing the critical
strip. It is used only to discharge Phragmen-Lindelof's growth condition.
Reflection applies at nonreal points without a positive real-part condition.
-/

namespace Sechstmoment.Source
open Complex Real MeasureTheory Filter Set
open scoped Topology
noncomputable section

theorem gamma_inv_reflection_nonreal {z : ℂ} (hz : z.im ≠ 0) :
    (Complex.Gamma z)⁻¹ = Complex.Gamma (1-z)*Complex.sin (Real.pi*z)/Real.pi := by
  have hΓ : Complex.Gamma z ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    exact hz (by simpa using congrArg Complex.im hn)
  have hΓ' : Complex.Gamma (1-z) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have hi := congrArg Complex.im hn
    simp only [sub_im,one_im,neg_im,natCast_im,zero_sub,neg_zero] at hi
    exact hz (neg_eq_zero.mp hi)
  have hsin : Complex.sin (Real.pi*z) ≠ 0 := by
    intro h
    have hR := Complex.Gamma_mul_Gamma_one_sub z
    rw [h,div_zero] at hR
    exact mul_ne_zero hΓ hΓ' hR
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hR := Complex.Gamma_mul_Gamma_one_sub z
  apply mul_left_cancel₀ hΓ
  rw [mul_inv_cancel₀ hΓ,← mul_div_assoc,← mul_assoc,hR]
  field_simp

theorem gamma_inv_norm_le_exp_nonreal {z : ℂ} (hz : z.im ≠ 0) (hσ : z.re < 1) :
    ‖(Complex.Gamma z)⁻¹‖ ≤
      Real.Gamma (1-z.re)*Real.exp (Real.pi*|z.im|)/Real.pi := by
  rw [gamma_inv_reflection_nonreal hz,norm_div,norm_mul,
    Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  have hΓ : ‖Complex.Gamma (1-z)‖ ≤ Real.Gamma (1-z.re) := by
    simpa only [sub_re,one_re] using gamma_norm_le_realGamma_re
      (s := 1-z) (by simp only [sub_re,one_re]; linarith)
  have hs : ‖Complex.sin (Real.pi*z)‖ ≤ Real.exp (Real.pi*|z.im|) := by
    simpa [abs_mul,Real.pi_pos.le] using complex_sin_norm_le_exp_abs_im ((Real.pi : ℂ)*z)
  exact mul_le_mul hΓ hs (norm_nonneg _) (Real.Gamma_pos_of_pos (by linarith)).le

theorem riemannZeta_exponential_crossing_strip :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re ∈ Icc (-1/2 : ℝ) (3/2) → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C*Real.exp (Real.pi*|s.im|/2) := by
  obtain ⟨K,hK,hcomp⟩ := completedRiemannZeta₀_norm_bounded_on_strip (-1/2) (3/2)
  obtain ⟨B,hB,hgamma⟩ := realGamma_norm_bounded_on_positive_interval
    (a := 1/4) (b := 5/4) (by norm_num)
  refine ⟨(K+2)*B,by positivity,?_⟩
  intro s hs ht
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at ht
  have hi : s.im ≠ 0 := by intro h; norm_num [h] at ht
  have hnorm : 1 ≤ ‖s‖ := ht.trans (Complex.abs_im_le_norm s)
  have hnorm' : 1 ≤ ‖1-s‖ := ht.trans (by simpa using Complex.abs_im_le_norm (1-s))
  have hfrac : ‖(1 : ℂ)/s‖ ≤ 1 := by
    rw [norm_div,norm_one]
    exact div_le_one_of_le₀ hnorm (by positivity)
  have hfrac' : ‖(1 : ℂ)/(1-s)‖ ≤ 1 := by
    rw [norm_div,norm_one]
    exact div_le_one_of_le₀ hnorm' (by positivity)
  have hnum : ‖completedRiemannZeta₀ s-1/s-1/(1-s)‖ ≤ K+2 := by
    exact (norm_sub_le _ _).trans (by
      have h := norm_sub_le (completedRiemannZeta₀ s) (1/s)
      linarith [hcomp s hs.1 hs.2])
  have hΓ : ‖(Complex.Gamma (s/2))⁻¹‖ ≤ B*Real.exp (Real.pi*|s.im|/2)/Real.pi := by
    have h := gamma_inv_norm_le_exp_nonreal (z := s/2)
      (by rw [Complex.div_ofNat_im]; exact div_ne_zero hi (by norm_num))
      (by simp only [Complex.div_ofNat_re]; linarith [hs.2])
    have hB' := hgamma (1-(s/2).re) (by
      simp only [Complex.div_ofNat_re]
      constructor <;> linarith [hs.1,hs.2])
    have him : Real.pi*|(s/2).im| = Real.pi*|s.im|/2 := by
      rw [Complex.div_ofNat_im,abs_div]
      norm_num
      ring
    rw [him] at h
    exact h.trans (by gcongr)
  have hπ : ‖((Real.pi : ℂ)^(-s/2))⁻¹‖ ≤ Real.pi := by
    rw [← Complex.cpow_neg,show -(-s/2) = s/2 by ring,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,Complex.div_ofNat_re]
    have h := Real.rpow_le_rpow_of_exponent_le (by linarith [Real.two_le_pi] : 1 ≤ Real.pi)
      (show s.re/2 ≤ 1 by linarith [hs.2])
    simpa only [Real.rpow_one] using h
  rw [riemannZeta_eq_completedRiemannZeta₀ hs0,div_eq_mul_inv,mul_inv_rev,norm_mul,norm_mul]
  calc
    _ ≤ (K+2)*((B*Real.exp (Real.pi*|s.im|/2)/Real.pi)*Real.pi) := by gcongr
    _ = _ := by field_simp

end
end Sechstmoment.Source
