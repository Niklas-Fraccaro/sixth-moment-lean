import Sechstmoment.Numerator.V.DP.DPResidueContinuity
import Sechstmoment.Numerator.V.Profiles.ArithmeticNormalization

/-! The original harmonic profile, after division by log^6, has a
uniform inverse-log error and a bounded continuous leading coefficient. -/

namespace Sechstmoment.Source
open NoDPHarmonic Complex Real Polynomial Metric
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def residueProfileLeading (η : ℝ) (P Q : ℝ[X]) (i : Fin 4) (σ : Fin 4 → ℂ) : ℂ :=
  (arithmeticFactor:ℂ)*(η:ℂ)^6*
    (dpNormalizedTriple η P (σ (Equiv.swap 0 i 1))
      (-(σ (Equiv.swap 0 i 2))) (-(σ (Equiv.swap 0 i 3)))*
    dpNormalizedTriple η Q (σ (Equiv.swap 0 i 1))
      (-(σ (Equiv.swap 0 i 2))) (-(σ (Equiv.swap 0 i 3))))

theorem residueProfileLeading_continuous (η : ℝ) (P Q : ℝ[X]) (i : Fin 4) :
    Continuous (residueProfileLeading η P Q i) := by
  have hP := dpNormalizedTriple_continuous_shifts η P
    (fun σ : Fin 4 → ℂ => σ (Equiv.swap 0 i 1))
    (fun σ : Fin 4 → ℂ => -(σ (Equiv.swap 0 i 2)))
    (fun σ : Fin 4 → ℂ => -(σ (Equiv.swap 0 i 3))) (by fun_prop) (by fun_prop) (by fun_prop)
  have hQ := dpNormalizedTriple_continuous_shifts η Q
    (fun σ : Fin 4 → ℂ => σ (Equiv.swap 0 i 1))
    (fun σ : Fin 4 → ℂ => -(σ (Equiv.swap 0 i 2)))
    (fun σ : Fin 4 → ℂ => -(σ (Equiv.swap 0 i 3))) (by fun_prop) (by fun_prop) (by fun_prop)
  exact continuous_const.mul (hP.mul hQ)

theorem residueProfileLeading_uniform_bound (η : ℝ) (P Q : ℝ[X]) (R : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ σ : Fin 4 → ℂ, ‖σ‖ ≤ R → ∀ i : Fin 4,
      ‖residueProfileLeading η P Q i σ‖ ≤ B := by
  have hf : Continuous (fun σ : Fin 4 → ℂ => fun i : Fin 4 =>
      residueProfileLeading η P Q i σ) :=
    continuous_pi (fun i => residueProfileLeading_continuous η P Q i)
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0 : Fin 4 → ℂ) R).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max 1 B,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro σ hσ i
  exact (norm_le_pi_norm (fun j => residueProfileLeading η P Q j σ) i).trans
    ((hB σ (by simpa only [mem_closedBall,dist_zero_right] using hσ)).trans (le_max_right _ _))

theorem residueProfile_scaled_uniform_error {η R : ℝ} (hη : 0 < η) (hR : 0 ≤ R)
    (P Q : ℝ[X]) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → 2*R ≤ (1/8)*L →
      ∀ σ : Fin 4 → ℂ, ‖σ‖ ≤ R → ∀ i : Fin 4,
      ‖originalProfileSum η L i (scaledShifts L σ) P Q/(L:ℂ)^6-
        residueProfileLeading η P Q i σ‖ ≤ C/L := by
  obtain ⟨C,hC,HC⟩ := original_polynomial_profile_arithmetic_asymptotic
    (ρ := 1/8) hη hR (by norm_num) (by norm_num) P Q
  refine ⟨C,hC,?_⟩
  intro L hL hLR σ hσ i
  have hL0 : 0 < L := by linarith
  have hLC : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL0.ne'
  have H := HC L hL hLR i σ hσ
  dsimp only at H
  have hmain : (arithmeticFactor:ℂ)*((η*L:ℝ):ℂ)^6*
      (dpNormalizedTriple η P (residueShifts i σ 0) (-(residueShifts i σ 1))
        (-(residueShifts i σ 2))*
      dpNormalizedTriple η Q (residueShifts i σ 0) (-(residueShifts i σ 1))
        (-(residueShifts i σ 2))) =
      (L:ℂ)^6*residueProfileLeading η P Q i σ := by
    unfold residueProfileLeading residueShifts
    push_cast
    ring
  rw [hmain] at H
  have hid : originalProfileSum η L i (scaledShifts L σ) P Q/(L:ℂ)^6-
      residueProfileLeading η P Q i σ =
      (originalProfileSum η L i (scaledShifts L σ) P Q-
        (L:ℂ)^6*residueProfileLeading η P Q i σ)/(L:ℂ)^6 := by field_simp [hLC]
  rw [hid,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL0]
  apply (div_le_div_iff₀ (pow_pos hL0 6) hL0).mpr
  calc
    _ ≤ (C*L^5)*L := mul_le_mul_of_nonneg_right H hL0.le
    _ = _ := by ring

end
end Sechstmoment.Source
