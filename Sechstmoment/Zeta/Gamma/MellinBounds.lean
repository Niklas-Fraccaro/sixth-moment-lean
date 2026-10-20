import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic


namespace Sechstmoment

open Real Complex MeasureTheory Set

noncomputable section

theorem gamma_norm_le_realGamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral,
    Real.Gamma_eq_integral hs]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, sub_re, one_re]

theorem gamma_inv_reflection {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    (Complex.Gamma s)⁻¹ = Complex.Gamma (1-s) * Complex.sin (π*s) / π := by
  have hGamma : Complex.Gamma s ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have hre := congrArg Complex.re hn
    simp only [neg_re, natCast_re] at hre
    have hnpos : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hSin : Complex.sin (π*s) ≠ 0 := by
    intro h
    have hreflection := Complex.Gamma_mul_Gamma_one_sub s
    rw [h, div_zero] at hreflection
    have hGamma' : Complex.Gamma (1-s) ≠ 0 := by
      apply Complex.Gamma_ne_zero
      intro n hn
      have hre := congrArg Complex.re hn
      simp only [sub_re, one_re, neg_re, natCast_re] at hre
      have hnpos : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    exact (mul_ne_zero hGamma hGamma') hreflection
  have hpi : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := Complex.Gamma_mul_Gamma_one_sub s
  apply (mul_left_cancel₀ hGamma)
  rw [mul_inv_cancel₀ hGamma]
  rw [← mul_div_assoc, ← mul_assoc, h]
  field_simp

theorem gamma_inv_norm_le {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    ‖(Complex.Gamma s)⁻¹‖ ≤
      Real.Gamma (1-s.re) * ‖Complex.sin (π*s)‖ / π := by
  rw [gamma_inv_reflection hs0 hs1, norm_div, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [sub_re, one_re] using
    gamma_norm_le_realGamma_re (s := 1-s) (by simp; linarith)

theorem complex_sin_norm_le_exp_abs_im (s : ℂ) :
    ‖Complex.sin s‖ ≤ Real.exp |s.im| := by
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
  have he : ‖Complex.exp (-s*I)-Complex.exp (s*I)‖ ≤
      2*Real.exp |s.im| := by
    apply (norm_sub_le _ _).trans
    rw [Complex.norm_exp, Complex.norm_exp]
    simp only [mul_re, neg_re, neg_im, I_re, I_im, mul_zero, mul_one, zero_sub, neg_neg]
    have h1 := Real.exp_le_exp.mpr (le_abs_self s.im)
    have h2 := Real.exp_le_exp.mpr (neg_le_abs s.im)
    linarith
  norm_num
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  have hneg : -s*I = -(s*I) := by ring
  rw [hneg] at he
  exact he.trans_eq (mul_comm _ _)

theorem gamma_inv_norm_le_exp {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    ‖(Complex.Gamma s)⁻¹‖ ≤
      Real.Gamma (1-s.re) * Real.exp (π*|s.im|) / π := by
  apply (gamma_inv_norm_le hs0 hs1).trans
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  apply mul_le_mul_of_nonneg_left _ (Real.Gamma_pos_of_pos (by linarith)).le
  simpa [abs_mul, Real.pi_pos.le] using complex_sin_norm_le_exp_abs_im ((π:ℂ)*s)

end

end Sechstmoment
