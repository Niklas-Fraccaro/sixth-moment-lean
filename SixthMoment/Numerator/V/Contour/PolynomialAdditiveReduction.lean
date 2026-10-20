import SixthMoment.Numerator.V.Arithmetic.AmplifierExpansion
import SixthMoment.Numerator.V.Contour.ShiftedChiWeightReplacement


namespace SixthMoment.Source
open Complex Real Set MeasureTheory Polynomial
open scoped BigOperators ContDiff
noncomputable section

def noDPAmplifiedAdditiveMain (w : ℝ → ℂ) (T η : ℝ) (f g : ℝ → ℝ)
    (u : ℂ) (β : Fin 4 → ℂ) : ℂ :=
  ∑ a ∈ Finset.range ⌊T^η⌋₊, ∑ b ∈ Finset.range ⌊T^η⌋₊,
    noDPAmplifierPairWeight T f g a b*
      ∑' m : ℕ+, noDPAdditiveChiTerm w T ((a+1:ℝ)*(b+1:ℝ)) u β m

theorem polynomial_shiftedChi_additive_reduction {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1/4) (R : ℝ) (hR : 0 ≤ R) (P Q : ℝ[X]) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, max 80 (100*Real.pi) ≤ T →
      4*(2*R+2) ≤ Real.log T → ∀ u : ℂ, ‖u‖ ≤ R/Real.log T →
      ∀ β : Fin 4 → ℂ, (∀ j, ‖β j‖ ≤ R/Real.log T) →
      ‖(∫ t : ℝ, shiftedChiProfileFactor T u β
          (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q)
          ((1/2:ℂ)+(t:ℂ)*I)*w (t/T))-
        (2*Real.pi:ℂ)*noDPAmplifiedAdditiveMain w T η
          (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) u β‖ ≤
        C*T^(1/2+2*η:ℝ)*(Real.log T)^4 := by
  obtain ⟨A,hA,Hadd⟩ := shiftedChi_profile_additive_reduction hw hws hR η
  obtain ⟨D,hD,Hshift⟩ := polynomial_shiftedChi_critical_to_starting_line hw hws hη hη' R hR P Q
  obtain ⟨B,hB,hP⟩ := polynomialProfile_uniform_bound hη P
  obtain ⟨E,hE,hQ⟩ := polynomialProfile_uniform_bound hη Q
  refine ⟨D+(2*Real.pi)*A*B*E,by positivity,?_⟩
  intro T hT hL u hu β hβ
  have hT80 : 80 ≤ T := (le_max_left _ _).trans hT
  let Icrit : ℂ := ∫ t : ℝ, shiftedChiProfileFactor T u β
    (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q)
    ((1/2:ℂ)+(t:ℂ)*I)*w (t/T)
  let Iright : ℂ := ∫ t : ℝ, shiftedChiProfileFactor T u β
    (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q)
    ((noDPRightLine T R:ℂ)+(t:ℂ)*I)*w (t/T)
  let M := noDPAmplifiedAdditiveMain w T η
    (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) u β
  have Hright : ‖(1/(2*Real.pi):ℂ)*Iright-M‖ ≤
      A*B*E*T^(1/2+2*η:ℝ)*(Real.log T)^4 :=
    Hadd T hT hL u hu β hβ B E hB.le hE.le _ _
      (polynomialProfile_upper_support η P) (polynomialProfile_upper_support η Q) hP hQ
  have hpi : (2*Real.pi:ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2*Real.pi:ℝ) ≠ 0)
  have he : Iright-(2*Real.pi:ℂ)*M =
      (2*Real.pi:ℂ)*((1/(2*Real.pi):ℂ)*Iright-M) := by field_simp [hpi]
  have hright : ‖Iright-(2*Real.pi:ℂ)*M‖ ≤
      (2*Real.pi)*A*B*E*T^(1/2+2*η:ℝ)*(Real.log T)^4 := by
    rw [he,norm_mul]
    have hnorm : ‖(2*Real.pi:ℂ)‖ = 2*Real.pi := by simp
    rw [hnorm]
    exact (mul_le_mul_of_nonneg_left Hright (by positivity)).trans_eq (by ring)
  have H := (norm_sub_le_norm_sub_add_norm_sub Icrit Iright ((2*Real.pi:ℂ)*M)).trans
    (add_le_add (Hshift T hT80 hL u hu β hβ) hright)
  exact H.trans_eq (by ring)

end
end SixthMoment.Source
