import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Sechstmoment.Numerator.V.Chi.PolynomialBound

/-! Exact duplication/reflection formula for the actual chi transform,
with the full 2*pi normalization retained. -/

namespace Sechstmoment.Source
open Complex Real
noncomputable section

theorem chi_one_sub_eq_gamma_cos (s : ℂ) (hs : s.im ≠ 0) :
    zetaChi (1-s) = 2*((2*Real.pi:ℝ):ℂ)^(-s)*Complex.Gamma s*
      Complex.cos ((Real.pi:ℂ)*s/2) := by
  have hπ : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hdup : Complex.Gamma (s/2)*Complex.Gamma ((1+s)/2) =
      Complex.Gamma s*(2:ℂ)^(1-s)*(Real.sqrt Real.pi:ℂ) := by
    simpa only [show s/2+1/2 = (1+s)/2 by ring,show 2*(s/2) = s by ring] using
      Complex.Gamma_mul_Gamma_add_half (s/2)
  have hroot : (Real.sqrt Real.pi:ℂ) = (Real.pi:ℂ)^(1/2:ℂ) := by
    simp only [Real.sqrt_eq_rpow,Complex.ofReal_cpow Real.pi_pos.le,
      Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  have hπpow : (Real.pi:ℂ)^(1/2-s)*(Real.sqrt Real.pi:ℂ)/Real.pi =
      (Real.pi:ℂ)^(-s) := by
    rw [hroot,← Complex.cpow_add _ _ hπ,show (1/2-s)+(1/2:ℂ) = 1-s by ring,
      sub_eq_add_neg,Complex.cpow_add _ _ hπ,Complex.cpow_one]
    field_simp [hπ]
  have htwo : (2:ℂ)^(1-s) = 2*(2:ℂ)^(-s) := by
    rw [sub_eq_add_neg,Complex.cpow_add _ _ (by norm_num),Complex.cpow_one]
  have hprod : ((2*Real.pi:ℝ):ℂ)^(-s) = (2:ℂ)^(-s)*(Real.pi:ℂ)^(-s) := by
    simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using
      Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ) ≤ 2) Real.pi_pos.le (-s)
  have hsin : Complex.sin ((Real.pi:ℂ)*((1-s)/2)) = Complex.cos ((Real.pi:ℂ)*s/2) := by
    rw [show (Real.pi:ℂ)*((1-s)/2) = (Real.pi:ℂ)/2-(Real.pi:ℂ)*s/2 by ring,
      Complex.sin_sub,Complex.sin_pi_div_two,Complex.cos_pi_div_two]
    ring
  calc
    _ = ((Real.pi:ℂ)^(1/2-s)/Real.pi)*
        (Complex.Gamma (s/2)*Complex.Gamma ((1+s)/2))*Complex.cos ((Real.pi:ℂ)*s/2) := by
      rw [zetaChi_one_sub_reflection hs,hsin]
      ring
    _ = ((Real.pi:ℂ)^(1/2-s)*(Real.sqrt Real.pi:ℂ)/Real.pi)*
        (2:ℂ)^(1-s)*Complex.Gamma s*Complex.cos ((Real.pi:ℂ)*s/2) := by
      rw [hdup]
      ring
    _ = _ := by rw [hπpow,htwo,hprod]; ring

end
end Sechstmoment.Source
