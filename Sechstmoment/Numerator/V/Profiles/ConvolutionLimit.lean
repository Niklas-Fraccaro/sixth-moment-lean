import Sechstmoment.Numerator.V.Profiles.Normalization
import Sechstmoment.Numerator.V.Profiles.SourceProfile

/-! Quantitative harmonic profile chapter: L^3 simplex asymptotics and the
actual arithmetic remainder convolution with L^6 main term and L^5 error.
The additive contour/stationary-phase identity and the final DP input are
separate obligations; neither is asserted by this chapter. -/

namespace Sechstmoment.Source.NoDPHarmonic
open Real Complex MeasureTheory Set Polynomial NoDPGlobalRest
open scoped BigOperators Topology
noncomputable section

def scaledShifts (L : ℝ) (σ : Fin 4 → ℂ) : Fin 4 → ℂ := fun j => σ j/(L:ℂ)

def residueShifts (i : Fin 4) (σ : Fin 4 → ℂ) : Fin 3 → ℂ :=
  fun j => σ (Equiv.swap 0 i j.succ)

theorem scaledShifts_norm {L R : ℝ} (hL : 0 < L) {σ : Fin 4 → ℂ} (hσ : ‖σ‖ ≤ R) :
    ‖scaledShifts L σ‖ ≤ R/L := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hσ
  apply (pi_norm_le_iff_of_nonneg (div_nonneg hR hL.le)).mpr
  intro j
  rw [scaledShifts,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  exact div_le_div_of_nonneg_right ((norm_le_pi_norm σ j).trans hσ) hL.le

theorem polynomial_gamma_asymptotic {η R ρ : ℝ}
    (hη : 0 ≤ η) (hR : 0 ≤ R) (hρ0 : 0 < ρ) (hρ : ρ < 1/4) (P Q : ℝ[X]) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → 2*R ≤ ρ*L →
      ∀ i : Fin 4, ∀ σ : Fin 4 → ℂ, ‖σ‖ ≤ R →
      let ν := residueShifts i σ
      ‖gammaProfileSum η L i (scaledShifts L σ) ν ν
          (reversedPolynomial η P) (reversedPolynomial η Q) -
        arithmeticConstant*((L:ℂ)^6*
          (polynomialSimplexIntegral η P (ν 0) (ν 1) (ν 2)*
            polynomialSimplexIntegral η Q (ν 0) (ν 1) (ν 2)))‖ ≤ C*L^5 := by
  obtain ⟨B,D,hf⟩ := reversedPolynomial_regular η P
  obtain ⟨A,E,hg⟩ := reversedPolynomial_regular η Q
  let C := productErrorConstant η R B D A E*((1+1/ρ)*globalBound ρ) +
    (2*uniformBound ρ/ρ)*R*(iterBounds η R B D 3).1*(iterBounds η R A E 3).1
  have hCp := productErrorConstant_nonneg hη hR hf.bound_nonneg hf.lip_nonneg
    hg.bound_nonneg hg.lip_nonneg
  have hAf := (iterBounds_nonneg (R := R) hη hf.bound_nonneg hf.lip_nonneg 3).1
  have hAg := (iterBounds_nonneg (R := R) hη hg.bound_nonneg hg.lip_nonneg 3).1
  have hC : 0 ≤ C := by unfold C globalBound uniformBound; positivity
  refine ⟨C+1,by positivity,?_⟩
  intro L hL hLR i σ hσ
  dsimp only
  have hL0 : 0 < L := by linarith
  have hscale := scaledShifts_norm hL0 hσ
  have hsmall : ‖scaledShifts L σ‖ ≤ ρ/2 := hscale.trans
    ((div_le_iff₀ hL0).mpr (by nlinarith))
  have hν : ∀ j, ‖residueShifts i σ j‖ ≤ R :=
    fun j => (norm_le_pi_norm σ _).trans hσ
  apply (gamma_profile_asymptotic hf hg hη hR hL i (scaledShifts L σ)
    hρ0 hρ hsmall hscale (residueShifts i σ) (residueShifts i σ) hν hν).trans
  change C*L^5 ≤ (C+1)*L^5
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

theorem source_polynomial_gamma_asymptotic {η R ρ : ℝ}
    (hη : 0 < η) (hR : 0 ≤ R) (hρ0 : 0 < ρ) (hρ : ρ < 1/4) (P Q : ℝ[X]) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → 2*R ≤ ρ*L →
      ∀ i : Fin 4, ∀ σ : Fin 4 → ℂ, ‖σ‖ ≤ R →
      let ν := residueShifts i σ
      ‖sourceGammaProfileSum η L i (scaledShifts L σ) ν ν P Q -
        arithmeticConstant*((L:ℂ)^6*
          (polynomialSimplexIntegral η P (ν 0) (ν 1) (ν 2)*
            polynomialSimplexIntegral η Q (ν 0) (ν 1) (ν 2)))‖ ≤ C*L^5 := by
  obtain ⟨C,hC,H⟩ := polynomial_gamma_asymptotic hη.le hR hρ0 hρ P Q
  refine ⟨C,hC,?_⟩
  intro L hL hLR i σ hσ
  dsimp only
  rw [← gammaProfileSum_eq_source hη (by linarith : 0 < L)]
  exact H L hL hLR i σ hσ

theorem source_polynomial_gamma_normalized_asymptotic {η R ρ : ℝ}
    (hη : 0 < η) (hR : 0 ≤ R) (hρ0 : 0 < ρ) (hρ : ρ < 1/4) (P Q : ℝ[X]) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → 2*R ≤ ρ*L →
      ∀ i : Fin 4, ∀ σ : Fin 4 → ℂ, ‖σ‖ ≤ R →
      let ν := residueShifts i σ
      ‖sourceGammaProfileSum η L i (scaledShifts L σ) ν ν P Q -
        arithmeticConstant*((η*L:ℝ):ℂ)^6*
          (dpNormalizedTriple η P (ν 0) (-(ν 1)) (-(ν 2))*
            dpNormalizedTriple η Q (ν 0) (-(ν 1)) (-(ν 2)))‖ ≤ C*L^5 := by
  obtain ⟨C,hC,H⟩ := source_polynomial_gamma_asymptotic hη hR hρ0 hρ P Q
  refine ⟨C,hC,?_⟩
  intro L hL hLR i σ hσ
  dsimp only
  have h := H L hL hLR i σ hσ
  dsimp only at h
  rw [polynomialSimplexIntegral_eq_dpNormalizedTriple hη.ne',
    polynomialSimplexIntegral_eq_dpNormalizedTriple hη.ne'] at h
  convert h using 1
  congr 1
  push_cast
  ring

end
end Sechstmoment.Source.NoDPHarmonic
