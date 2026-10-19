import Mathlib.Analysis.Fourier.ZMod
import Sechstmoment.Zeta.DirichletL.Weights.Definitions

/-! The modulus of the actual primitive root number, obtained from finite
Fourier inversion and Gauss-sum conjugation, without a Gauss-sum estimate
being assumed.
-/

namespace Sechstmoment.Source
open Complex Real ZMod ComplexConjugate
open scoped Topology BigOperators
noncomputable section

theorem primitive_gaussSum_norm_sq {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    ‖gaussSum χ stdAddChar‖^2 = (N : ℝ) := by
  have hχinv : χ⁻¹.IsPrimitive := by
    simpa only [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv] using hχ
  have hF : ZMod.dft (fun x : ZMod N => χ x) =
      fun k => χ⁻¹ (-k)*gaussSum χ stdAddChar :=
    funext (fun k => hχ.fourierTransform_eq_inv_mul_gaussSum k)
  have h := congrFun (ZMod.dft_dft (fun x : ZMod N => χ x)) (-1)
  rw [hF, ZMod.dft_mul_const, ZMod.dft_comp_neg] at h
  simp only [neg_neg, map_one, smul_eq_mul, mul_one] at h
  rw [hχinv.fourierTransform_eq_inv_mul_gaussSum] at h
  simp only [inv_inv] at h
  have hstar : star (gaussSum χ stdAddChar) = χ (-1)*gaussSum χ⁻¹ stdAddChar := by
    rw [star_gaussSum_eq, AddChar.inv_mulShift]
    simpa only [inv_inv, Units.val_neg, Units.val_one] using
      gaussSum_mulShift_eq χ⁻¹ stdAddChar (-1 : (ZMod N)ˣ)
  have hnorm : ((‖gaussSum χ stdAddChar‖^2 : ℝ) : ℂ) = (N : ℂ) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    change gaussSum χ stdAddChar * star (gaussSum χ stdAddChar) = _
    rw [hstar]
    linear_combination h
  exact_mod_cast hnorm

theorem primitive_rootNumber_norm {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) : ‖χ.rootNumber‖ = 1 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hNhalf : ((N : ℝ)^(1/2 : ℝ))^2 = (N : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    norm_num
  have hnorm : ‖χ.rootNumber‖^2 = 1 := by
    rw [DirichletCharacter.rootNumber, norm_div, norm_div, norm_pow, norm_I, one_pow, div_one]
    rw [show (N : ℂ) = ((N : ℝ) : ℂ) by norm_cast,
      Complex.norm_cpow_eq_rpow_re_of_pos hN]
    norm_num only [Complex.div_ofNat_re, one_re]
    rw [div_pow, primitive_gaussSum_norm_sq χ hχ, hNhalf, div_self hN.ne']
  nlinarith [norm_nonneg χ.rootNumber]

end
end Sechstmoment.Source
