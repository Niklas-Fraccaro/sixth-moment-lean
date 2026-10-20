import Sechstmoment.Numerator.V.Contour.ShiftedChiFactor
import Sechstmoment.Numerator.V.Contour.ShiftedLineGeometry


namespace Sechstmoment.Source
open Complex Real Set
open scoped BigOperators
noncomputable section

theorem shiftedChiProfileFactor_starting_line_bound (η R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 64 ≤ T → 4*(2*R+2) ≤ Real.log T →
      ∀ B D : ℝ, 0 ≤ B → 0 ≤ D → ∀ f g : ℝ → ℝ,
      (∀ x, η < x → f x = 0) → (∀ x, η < x → g x = 0) →
      (∀ x ∈ Icc (0:ℝ) η, |f x| ≤ B) → (∀ x ∈ Icc (0:ℝ) η, |g x| ≤ D) →
      ∀ u : ℂ, ‖u‖ ≤ R/Real.log T → ∀ β : Fin 4 → ℂ,
      (∀ j, ‖β j‖ ≤ R/Real.log T) → ∀ t ∈ Icc T (2*T),
      ‖shiftedChiProfileFactor T u β f g ((noDPRightLine T R:ℂ)+(t:ℂ)*I)‖ ≤
        C*B*D*T^(1/2+2*η:ℝ)*(Real.log T)^4 := by
  obtain ⟨Z,hZ,hzeta⟩ := four_zeta_starting_line_bound
  let A : ℝ := R+2
  refine ⟨131*Real.exp (2*R+2)*Z*(Real.exp (η*A))^2,by positivity,?_⟩
  intro T hT hLA B D hB hD f g hfs hgs hf hg u hu β hβ t ht
  have hT1 : 1 < T := by linarith
  have hT0 : 0 < T := by linarith
  have hL : 1 ≤ Real.log T := by linarith
  have hc' : noDPRightLine T R ≤ 1+A/Real.log T := by rfl
  have hchi := shifted_chi_starting_line_bound hT hR hLA hu ht
  have hz := hzeta T R hL hR β hβ t
  have hsp : ((noDPRightLine T R:ℂ)+(t:ℂ)*I).re ≤ 1+A/Real.log T := by
    simpa only [add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero] using hc'
  have hp := profileDirichletSum_one_sub_log_bound hT1 (show 0 ≤ A by dsimp [A]; linarith)
    hB f hfs hf hsp
  have hq := profileDirichletSum_one_sub_log_bound hT1 (show 0 ≤ A by dsimp [A]; linarith)
    hD g hgs hg hsp
  rw [shiftedChiProfileFactor,shiftedChiZetaFactor,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ ((131*Real.exp (2*R+2)*T^(1/2:ℝ))*(Z*(Real.log T)^4))*
        (B*Real.exp (η*A)*T^η)*(D*Real.exp (η*A)*T^η) := by gcongr
    _ = _ := by
      rw [show (1/2+2*η:ℝ) = (1/2:ℝ)+η+η by ring,
        Real.rpow_add hT0,Real.rpow_add hT0]
      ring

end
end Sechstmoment.Source
