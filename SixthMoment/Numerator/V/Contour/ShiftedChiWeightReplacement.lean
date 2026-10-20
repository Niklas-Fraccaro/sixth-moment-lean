import SixthMoment.Numerator.V.Contour.ShiftedChiPolynomial
import SixthMoment.Numerator.V.Contour.ShiftedChiStartingLine
import SixthMoment.Numerator.V.Contour.WeightReplacement


namespace SixthMoment.Source
open Complex Real Set MeasureTheory Polynomial
open scoped ContDiff
noncomputable section

theorem polynomial_shiftedChi_weight_replacement {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {η : ℝ} (hη : 0 < η) (R : ℝ) (hR : 0 ≤ R) (P Q : ℝ[X]) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 80 ≤ T → 4*(2*R+2) ≤ Real.log T →
      ∀ u : ℂ, ‖u‖ ≤ R/Real.log T → ∀ β : Fin 4 → ℂ,
      (∀ j, ‖β j‖ ≤ R/Real.log T) →
      ‖(∫ t : ℝ, shiftedChiProfileFactor T u β
          (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q)
          ((noDPRightLine T R:ℂ)+(t:ℂ)*I)*
          almostHolomorphicWeight w K T (noDPRightLine T R) t)-
        (∫ t : ℝ, shiftedChiProfileFactor T u β
          (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q)
          ((noDPRightLine T R:ℂ)+(t:ℂ)*I)*w (t/T))‖ ≤
        C*T^(1/2+2*η:ℝ)*(Real.log T)^4 := by
  obtain ⟨B,hB,hP⟩ := polynomialProfile_uniform_bound hη P
  obtain ⟨D,hD,hQ⟩ := polynomialProfile_uniform_bound hη Q
  obtain ⟨A,hA,hfactor⟩ := shiftedChiProfileFactor_starting_line_bound η R hR
  obtain ⟨W,hW,hreplace⟩ := almostHolomorphicWeight_integrated_replacement hw hws K
  refine ⟨W*A*B*D,by positivity,?_⟩
  intro T hT hLA u hu β hβ
  have hT1 : 1 < T := by linarith
  have hc := noDPRightLine_in_contour hR (by linarith : 4*(R+2) ≤ Real.log T)
  have huSmall := (noDPRightLine_chi_shift_geometry hR hLA hu).2.1
  have hβSmall (j : Fin 4) : ‖β j‖ ≤ 1/8 :=
    (noDPRightLine_chi_shift_geometry hR hLA (hβ j)).2.1
  let F : ℝ → ℂ := fun t => shiftedChiProfileFactor T u β
    (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q)
    ((noDPRightLine T R:ℂ)+(t:ℂ)*I)
  have hF : ContinuousOn F (Icc (T/2) (3*T)) := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    have hs := shiftedChiProfileFactor_differentiableAt hT1 η η
      (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q)
      (polynomialProfile_upper_support η P) (polynomialProfile_upper_support η Q) β
      (s := (noDPRightLine T R:ℂ)+(t:ℂ)*I)
      (by simpa only [add_im,ofReal_im,mul_I_im,ofReal_re,zero_add,
          abs_of_nonneg (by linarith [ht.1] : 0 ≤ t)] using
        (show (40:ℝ) ≤ t by linarith [ht.1])) huSmall hβSmall
    have hpath : ContinuousAt (fun v : ℝ => (noDPRightLine T R:ℂ)+(v:ℂ)*I) t := by fun_prop
    exact ContinuousAt.comp (f := fun v : ℝ => (noDPRightLine T R:ℂ)+(v:ℂ)*I)
      hs.continuousAt hpath
  have hgap : |noDPRightLine T R-1/2| ≤ 1 := by
    rw [abs_of_nonneg (by linarith [hc.1])]
    linarith [hc.2]
  have hpoint := hfactor T (by linarith : 64 ≤ T) hLA B D hB.le hD.le
    (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q)
    (polynomialProfile_upper_support η P) (polynomialProfile_upper_support η Q)
    hP hQ u hu β hβ
  have H := hreplace T (by linarith : 1 ≤ T) (noDPRightLine T R) hgap F hF
    (A*B*D*T^(1/2+2*η:ℝ)*(Real.log T)^4) (by positivity) hpoint
  apply H.trans_eq
  ring

theorem polynomial_shiftedChi_critical_to_starting_line {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1/4) (R : ℝ) (hR : 0 ≤ R) (P Q : ℝ[X]) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 80 ≤ T → 4*(2*R+2) ≤ Real.log T →
      ∀ u : ℂ, ‖u‖ ≤ R/Real.log T → ∀ β : Fin 4 → ℂ,
      (∀ j, ‖β j‖ ≤ R/Real.log T) →
      ‖(∫ t : ℝ, shiftedChiProfileFactor T u β
          (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q)
          ((1/2:ℂ)+(t:ℂ)*I)*w (t/T))-
        (∫ t : ℝ, shiftedChiProfileFactor T u β
          (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q)
          ((noDPRightLine T R:ℂ)+(t:ℂ)*I)*w (t/T))‖ ≤
        C*T^(1/2+2*η:ℝ)*(Real.log T)^4 := by
  obtain ⟨D,hD,hshift⟩ := polynomial_shiftedChi_smooth_shift hw hws hη hη' P Q
  obtain ⟨E,hE,hreplace⟩ := polynomial_shiftedChi_weight_replacement hw hws hη R hR P Q 16
  refine ⟨D+E,by positivity,?_⟩
  intro T hT hL u hu β hβ
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hL1 : 1 ≤ Real.log T := by linarith
  have hc := noDPRightLine_in_contour hR (by linarith : 4*(R+2) ≤ Real.log T)
  have Hshift := hshift T hT u (noDPRightLine_chi_shift_geometry hR hL hu).2.1 β
    (fun j => (noDPRightLine_chi_shift_geometry hR hL (hβ j)).2.1)
    (noDPRightLine T R) ⟨by linarith [hc.1],hc.2⟩
  have Hreplace := hreplace T hT hL u hu β hβ
  let M := T^(1/2+2*η:ℝ)*(Real.log T)^4
  have hM1 : 1 ≤ M := by
    have hp : 1 ≤ T^(1/2+2*η:ℝ) := by
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hT1
        (show (0:ℝ) ≤ 1/2+2*η by linarith)
    have hq : 1 ≤ (Real.log T)^4 := one_le_pow₀ hL1
    dsimp only [M]
    simpa only [one_mul] using mul_le_mul hp hq (by norm_num) (by linarith)
  have hsmall : D/T^3 ≤ D*M := by
    have hden : 1 ≤ T^3 := one_le_pow₀ hT1
    calc
      _ ≤ D := (div_le_iff₀ (pow_pos hT0 3)).mpr
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hden hD.le)
      _ ≤ D*M := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hM1 hD.le
  have H := norm_sub_le_norm_sub_add_norm_sub
    (∫ t : ℝ, shiftedChiProfileFactor T u β
      (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q)
      ((1/2:ℂ)+(t:ℂ)*I)*w (t/T))
    (∫ t : ℝ, shiftedChiProfileFactor T u β
      (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q)
      ((noDPRightLine T R:ℂ)+(t:ℂ)*I)*almostHolomorphicWeight w 16 T (noDPRightLine T R) t)
    (∫ t : ℝ, shiftedChiProfileFactor T u β
      (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q)
      ((noDPRightLine T R:ℂ)+(t:ℂ)*I)*w (t/T))
  apply (H.trans (add_le_add (by simpa only [norm_sub_rev] using Hshift) Hreplace)).trans
  calc
    _ ≤ D*M+E*T^(1/2+2*η:ℝ)*(Real.log T)^4 := add_le_add hsmall le_rfl
    _ = _ := by dsimp only [M]; ring

end
end SixthMoment.Source
