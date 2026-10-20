import SixthMoment.Numerator.U.ZeroModes.Transforms.GammaCosPolynomial
import SixthMoment.Zeta.AFE.Four.LargeGammaStrip

namespace SixthMoment.Source
open Complex Real Set
noncomputable section

theorem a03GammaCos_strip_polynomial_bound :
    ∃ C : ℝ,0≤C ∧ ∀ s : ℂ,s.re∈Icc (1/8:ℝ) (15/8) →
      ‖Complex.Gamma s*Complex.cos (Real.pi*s/2)‖≤C*(1+|s.im|)^2 := by
  obtain ⟨C,hC,hGamma⟩ := gamma_large_positive_strip_envelope 1
  refine ⟨C,hC.le,?_⟩
  intro s hs
  have hG : ‖Complex.Gamma s‖≤C*(1+|s.im|)^2*Real.exp (-(Real.pi*|s.im|/2)) := by
    exact hGamma s (by norm_num; exact hs)
  have hcos : ‖Complex.cos (Real.pi*s/2)‖≤Real.exp (Real.pi*|s.im|/2) := by
    have h := a03Complex_cos_norm_le_exp_abs_im (Real.pi*s/2)
    have he : |(Real.pi*s/2).im|=Real.pi*|s.im|/2 := by
      simp only [Complex.div_ofNat_im,Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,
        zero_mul,add_zero]
      rw [abs_div,abs_mul,abs_of_pos Real.pi_pos]
      norm_num
    rwa [he] at h
  rw [norm_mul]
  calc
    _≤(C*(1+|s.im|)^2*Real.exp (-(Real.pi*|s.im|/2)))*Real.exp (Real.pi*|s.im|/2) :=
      mul_le_mul hG hcos (norm_nonneg _) (by positivity)
    _=_ := by rw [mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one]

end
end SixthMoment.Source
