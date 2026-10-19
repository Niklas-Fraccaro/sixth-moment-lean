import Sechstmoment.Numerator.V.Contour.SameSideContour

/-! The interior contour displacement for the actual polynomial profiles.
Order 16 makes the Cauchy-Green error at most C/T^3 for every fixed
profile exponent at most 1/4. Replacing the weight on the right line and
the subsequent stationary-phase transformation are separate steps.
-/

namespace Sechstmoment.Source
open Complex Real Set MeasureTheory Polynomial
open scoped Topology BigOperators ContDiff
noncomputable section

theorem polynomialProfile_upper_support (η : ℝ) (P : ℝ[X]) :
    ∀ x : ℝ, η < x → zeroExtendedPolynomialProfile η P x = 0 := by
  intro x hx
  have hn : x ∉ Ico (0 : ℝ) η := by intro h; linarith [h.2]
  simp [zeroExtendedPolynomialProfile,hn]

theorem polynomialProfile_uniform_bound {η : ℝ} (hη : 0 < η) (P : ℝ[X]) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Icc (0 : ℝ) η, |zeroExtendedPolynomialProfile η P x| ≤ B := by
  have hP : Continuous (fun x : ℝ => P.eval x) := by fun_prop
  obtain ⟨B,hbound⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) 1) hP.continuousOn
  refine ⟨max 1 B,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro x hx
  by_cases hx' : x ∈ Ico (0 : ℝ) η
  · rw [zeroExtendedPolynomialProfile,Set.indicator_of_mem hx']
    have hy : 1-x/η ∈ Icc (0 : ℝ) 1 := by
      have hr : 0 ≤ x/η := div_nonneg hx.1 hη.le
      have hl : x/η ≤ 1 := (div_le_one hη).mpr hx.2
      constructor <;> linarith
    have h := hbound (1-x/η) hy
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_right _ _)
  · simp only [zeroExtendedPolynomialProfile,Set.indicator_apply]
    rw [ite_eq_right hx',abs_zero]
    exact zero_le_one.trans (le_max_left _ _)

theorem polynomialProfileContourMass_bound {η : ℝ} (hη : 0 < η) (P : ℝ[X]) :
    ∃ B : ℝ, 0 < B ∧ ∀ T : ℝ, 1 < T →
      profileContourMass T η (zeroExtendedPolynomialProfile η P) ≤ B*T^(2*η) := by
  obtain ⟨B,hB,hbound⟩ := polynomialProfile_uniform_bound hη P
  exact ⟨B,hB,fun T hT => profileContourMass_bound hT _ hB.le hbound⟩

theorem polynomial_sameSide_smooth_shift {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1 : ℝ) 2) {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1/4)
    (P Q : ℝ[X]) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 80 ≤ T →
      ∀ α : Fin 4 → ℂ, (∀ j, ‖α j‖ ≤ 1/8) →
      ∀ c : ℝ, c ∈ Icc (1/2 : ℝ) (5/4) →
      ‖(∫ t : ℝ, sameSideProfileFactor T α
          (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q)
          ((c : ℂ)+(t : ℂ)*I)*almostHolomorphicWeight w 16 T c t)-
        (∫ t : ℝ, sameSideProfileFactor T α
          (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q)
          ((1/2 : ℂ)+(t : ℂ)*I)*w (t/T))‖ ≤ C/T^3 := by
  obtain ⟨A,hA,hshift⟩ := sameSideProfileFactor_smooth_shift_integral hw hws 16
  obtain ⟨B,hB,hP⟩ := polynomialProfileContourMass_bound hη P
  obtain ⟨D,hD,hQ⟩ := polynomialProfileContourMass_bound hη Q
  refine ⟨A*B*D,by positivity,?_⟩
  intro T hT α hα c hc
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
    (polynomialProfile_upper_support η Q) α hα c hc
  calc
    _ ≤ A*profileContourMass T η (zeroExtendedPolynomialProfile η P)*
        profileContourMass T η (zeroExtendedPolynomialProfile η Q)*T^13/T^(16+1) := h
    _ = A*(profileContourMass T η (zeroExtendedPolynomialProfile η P)*
        profileContourMass T η (zeroExtendedPolynomialProfile η Q))*T^13/T^17 := by ring
    _ ≤ A*(B*D*T)*T^13/T^17 := by gcongr
    _ = _ := by field_simp

end
end Sechstmoment.Source
