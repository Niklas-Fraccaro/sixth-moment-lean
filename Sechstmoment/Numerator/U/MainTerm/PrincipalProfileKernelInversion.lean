import Sechstmoment.Numerator.U.MainTerm.PrincipalPolarPointLimit
import Sechstmoment.Numerator.U.MainTerm.PrincipalRationalInversion


namespace Sechstmoment
open Complex Real MeasureTheory Set Source
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 1000000

theorem actualPrincipalPolarLimitKernel_profile_inversion
    (σ : MomentShifts) (m : Fin 6) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (f g : ℝ → ℂ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    (hfsupp : ∀ x ∉ Icc 0 a, f x = 0) (hgsupp : ∀ y ∉ Icc 0 b, g y = 0)
    (c : ℝ) (hc : 0 < c)
    (hshift : ∀ j : Fin 4, 0 < c + (bblrSixShifts σ m j).re)
    (h01 : bblrSixShifts σ m 0 ≠ bblrSixShifts σ m 1)
    (h23 : bblrSixShifts σ m 2 ≠ bblrSixShifts σ m 3) :
    (1 / (2 * π) : ℂ)^2 *
      (∫ y : ℝ × ℝ, actualPrincipalPolarLimitKernel σ m f g c c y
        ∂(volume.prod volume)) =
      (arithmeticFactor : ℂ) *
        (∫ A in (0 : ℝ)..a, ∫ B in (0 : ℝ)..b,
          f A * g B *
            (∫ t in (0 : ℝ)..min A B,
              exponentialDifference (bblrSixShifts σ m 2) (bblrSixShifts σ m 3) (A - t) *
              exponentialDifference (bblrSixShifts σ m 0) (bblrSixShifts σ m 1) (B - t)) /
            principalPurePolarProduct (bblrSixShifts σ m)) := by
  let α : MomentShifts := bblrSixShifts σ m
  let R : ℝ × ℝ → ℂ := fun y =>
    profileLaplaceTransform f (a04VerticalPoint c y.1) *
    profileLaplaceTransform g (a04VerticalPoint c y.2) /
      ((a04VerticalPoint c y.1 + a04VerticalPoint c y.2) *
        (a04VerticalPoint c y.1 + α 2) * (a04VerticalPoint c y.1 + α 3) *
        (a04VerticalPoint c y.2 + α 0) * (a04VerticalPoint c y.2 + α 1))
  have hkernel (y : ℝ × ℝ) : actualPrincipalPolarLimitKernel σ m f g c c y =
      ((arithmeticFactor : ℂ) / principalPurePolarProduct α) * R y := by
    unfold actualPrincipalPolarLimitKernel
    rw [ninePolarRationalFactor_zero_split]
    dsimp [α, R, a04VerticalPoint]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hdouble := doubleProfileRationalIntegral_eq_positiveConvolution
    hf hfs hg hgs hc (α 2) (α 3) (α 0) (α 1)
    (hshift 2) (hshift 3) (hshift 0) (hshift 1) h23 h01
  let K : ℝ × ℝ → ℂ := fun p =>
    exponentialDifference (α 2) (α 3) p.1 * exponentialDifference (α 0) (α 1) p.2
  have hK : Continuous K := by
    unfold K exponentialDifference
    fun_prop
  have hcompact := positiveConvolution_eq_interval_compact a b ha hb f g K
    hfs.continuous hgs.continuous hK hfsupp hgsupp
  simp only [K] at hcompact
  simp_rw [hkernel]
  rw [integral_const_mul]
  calc
    _ = ((arithmeticFactor : ℂ) / principalPurePolarProduct α) *
        ((1 / (2 * π) : ℂ)^2 * ∫ y : ℝ × ℝ, R y ∂(volume.prod volume)) := by ring
    _ = ((arithmeticFactor : ℂ) / principalPurePolarProduct α) *
        (∫ A in (0 : ℝ)..a, ∫ B in (0 : ℝ)..b,
          f A * g B * ∫ t in (0 : ℝ)..min A B,
            exponentialDifference (α 2) (α 3) (A - t) *
            exponentialDifference (α 0) (α 1) (B - t)) := by
      rw [hdouble]
      simpa only [mul_assoc] using congrArg
        (fun z : ℂ => ((arithmeticFactor : ℂ) / principalPurePolarProduct α) * z) hcompact
    _ = _ := by
      simp only [intervalIntegral.integral_div]
      dsimp only [α]
      ring

end
end Sechstmoment
