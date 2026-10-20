import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Sechstmoment.Zeta.Gamma.ReciprocalSums


namespace Sechstmoment.Source
open Complex Real
open scoped BigOperators
noncomputable section

theorem norm_log_quadratic_remainder {z : ℂ} (hz : ‖z‖ ≤ 1/2) :
    ‖Complex.log (1+z)-z+z^2/2‖ ≤ (2/3:ℝ)*‖z‖^3 := by
  have hp : Complex.logTaylor 3 z = z-z^2/2 := by
    norm_num [Complex.logTaylor,Finset.sum_range_succ]
    ring
  have H := Complex.norm_log_sub_logTaylor_le 2 (by linarith : ‖z‖ < 1)
  rw [hp] at H
  have hi : (1-‖z‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div,div_le_iff₀ (by linarith : 0 < 1-‖z‖)]
    linarith
  have he : Complex.log (1+z)-z+z^2/2 = Complex.log (1+z)-(z-z^2/2) := by ring
  rw [he]
  apply H.trans
  nlinarith [mul_le_mul_of_nonneg_left hi (pow_nonneg (norm_nonneg z) 3)]

def stirlingStepError (s : ℂ) : ℂ := (s+1/2)*Complex.log (1+s⁻¹)-1

theorem stirlingStepError_bound (s : ℂ) (hs : 2 ≤ ‖s‖) :
    ‖stirlingStepError s‖ ≤ 2/‖s‖^2 := by
  have hn : 0 < ‖s‖ := by linarith
  have hs0 : s ≠ 0 := norm_ne_zero_iff.mp hn.ne'
  have hsmall : ‖s⁻¹‖ ≤ 1/2 := by
    rw [norm_inv,inv_eq_one_div,div_le_iff₀ hn]
    linarith
  have H := norm_log_quadratic_remainder hsmall
  have hid : stirlingStepError s =
      (s+1/2)*(Complex.log (1+s⁻¹)-s⁻¹+(s⁻¹)^2/2)-(s⁻¹)^2/4 := by
    unfold stirlingStepError
    field_simp [hs0]
    ring
  have hp : ‖s+(1/2:ℂ)‖ ≤ ‖s‖+1/2 := by
    simpa using norm_add_le s (1/2:ℂ)
  have hq : ‖s‖+1/2 ≤ (3/2:ℝ)*‖s‖ := by linarith
  rw [hid]
  calc
    _ ≤ ‖(s+1/2)*(Complex.log (1+s⁻¹)-s⁻¹+(s⁻¹)^2/2)‖+‖(s⁻¹)^2/4‖ := norm_sub_le _ _
    _ = ‖s+1/2‖*‖Complex.log (1+s⁻¹)-s⁻¹+(s⁻¹)^2/2‖+‖s⁻¹‖^2/4 := by
      rw [norm_mul,norm_div,norm_pow,Complex.norm_ofNat]
    _ ≤ (‖s‖+1/2)*((2/3:ℝ)*‖s⁻¹‖^3)+‖s⁻¹‖^2/4 := by
      gcongr
    _ ≤ ((3/2:ℝ)*‖s‖)*((2/3:ℝ)*‖s⁻¹‖^3)+‖s⁻¹‖^2/4 := by
      gcongr
    _ = (5/4:ℝ)/‖s‖^2 := by
      rw [norm_inv]
      field_simp [hn.ne']
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) (sq_nonneg ‖s‖)

theorem stirlingStepError_finite_sum_bound (s : ℂ) (hre : 0 ≤ s.re)
    (him : 2 ≤ |s.im|) (N : ℕ) :
    ‖∑ k ∈ Finset.range N, stirlingStepError (s+k)‖ ≤ 8/|s.im| := by
  have hnorm (k : ℕ) : 2 ≤ ‖s+k‖ := by
    have H := Complex.abs_im_le_norm (s+(k:ℂ))
    simp only [add_im,natCast_im,add_zero] at H
    exact him.trans H
  calc
    _ ≤ ∑ k ∈ Finset.range N, ‖stirlingStepError (s+k)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range N, 2/‖s+k‖^2 :=
      Finset.sum_le_sum (fun k _ => stirlingStepError_bound (s+k) (hnorm k))
    _ = 2*(∑ k ∈ Finset.range N, (‖s+k‖^2)⁻¹) := by
      rw [Finset.mul_sum]
      simp only [div_eq_mul_inv]
    _ ≤ 2*(4/|s.im|) := mul_le_mul_of_nonneg_left
      (reciprocalSquareSum_range_le s N hre (by linarith)) (by norm_num)
    _ = _ := by ring

end
end Sechstmoment.Source
