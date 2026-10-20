import Sechstmoment.Numerator.V.Contour.PolynomialSmoothShift
import Sechstmoment.Numerator.V.Contour.ShiftedChiContour


namespace Sechstmoment.Source
open Complex Real Set MeasureTheory Polynomial
open scoped Topology BigOperators ContDiff
noncomputable section

theorem polynomial_shiftedChi_smooth_shift {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1 : ℝ) 2) {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1/4)
    (P Q : ℝ[X]) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 80 ≤ T →
      ∀ u : ℂ, ‖u‖ ≤ 1/8 → ∀ α : Fin 4 → ℂ, (∀ j, ‖α j‖ ≤ 1/8) →
      ∀ c : ℝ, c ∈ Icc (1/2 : ℝ) (5/4) →
      ‖(∫ t : ℝ, shiftedChiProfileFactor T u α
          (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q)
          ((c : ℂ)+(t : ℂ)*I)*almostHolomorphicWeight w 16 T c t)-
        (∫ t : ℝ, shiftedChiProfileFactor T u α
          (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q)
          ((1/2 : ℂ)+(t : ℂ)*I)*w (t/T))‖ ≤ C/T^3 := by
  obtain ⟨A,hA,hshift⟩ := shiftedChiProfileFactor_smooth_shift_integral hw hws 16
  obtain ⟨B,hB,hP⟩ := polynomialProfileContourMass_bound hη P
  obtain ⟨D,hD,hQ⟩ := polynomialProfileContourMass_bound hη Q
  refine ⟨A*B*D,by positivity,?_⟩
  intro T hT u hu α hα c hc
  have hTpos : 0 < T := by linarith
  have hT1 : 1 < T := by linarith
  have hpow : T^(2*η)*T^(2*η) ≤ T := by
    rw [← Real.rpow_add hTpos]
    have h := Real.rpow_le_rpow_of_exponent_le hT1.le
      (show 2*η+2*η ≤ 1 by linarith)
    simpa only [Real.rpow_one] using h
  have hmass : profileContourMass T η (zeroExtendedPolynomialProfile η P)*
      profileContourMass T η (zeroExtendedPolynomialProfile η Q) ≤ B*D*T := by
    calc
      _ ≤ (B*T^(2*η))*(D*T^(2*η)) := mul_le_mul (hP T hT1) (hQ T hT1)
        (profileContourMass_nonneg _ _ _) (by positivity)
      _ = (B*D)*(T^(2*η)*T^(2*η)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  have h := hshift T hT η η _ _ (polynomialProfile_upper_support η P)
    (polynomialProfile_upper_support η Q) u hu α hα c hc
  calc
    _ ≤ A*profileContourMass T η (zeroExtendedPolynomialProfile η P)*
        profileContourMass T η (zeroExtendedPolynomialProfile η Q)*T^13/T^(16+1) := h
    _ = A*(profileContourMass T η (zeroExtendedPolynomialProfile η P)*
        profileContourMass T η (zeroExtendedPolynomialProfile η Q))*T^13/T^17 := by ring
    _ ≤ A*(B*D*T)*T^13/T^17 := by gcongr
    _ = _ := by field_simp


end
end Sechstmoment.Source
