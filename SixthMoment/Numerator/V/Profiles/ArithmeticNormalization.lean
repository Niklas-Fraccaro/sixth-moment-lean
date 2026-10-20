import SixthMoment.Arithmetic.Factor.Convergence
import SixthMoment.Numerator.V.Profiles.OriginalProfile


namespace SixthMoment.Source.NoDPHarmonic
open Real Complex Polynomial NoDPGlobalRest
open scoped BigOperators
noncomputable section

theorem arithmeticConstant_eq_arithmeticFactor :
    arithmeticConstant = (arithmeticFactor : ℂ) := by
  have hm := arithmeticFactor_wellDefined.1.map_tprod
    Complex.ofRealHom Complex.continuous_ofReal
  change (∏' p : {n : ℕ // n.Prime},
    (1-(p.val:ℂ)⁻¹)^4*(1+4*(p.val:ℂ)⁻¹+((p.val:ℂ)⁻¹)^2)) =
      Complex.ofRealHom (∏' p : {n : ℕ // n.Prime}, eulerFactor (p.val:ℝ))
  rw [hm]
  apply tprod_congr
  intro p
  change _ = (eulerFactor (p.val:ℝ):ℂ)
  unfold eulerFactor
  push_cast
  simp only [div_eq_mul_inv,inv_pow,one_mul]

theorem original_polynomial_profile_arithmetic_asymptotic {η R ρ : ℝ}
    (hη : 0 < η) (hR : 0 ≤ R) (hρ0 : 0 < ρ) (hρ : ρ < 1/4) (P Q : ℝ[X]) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → 2*R ≤ ρ*L →
      ∀ i : Fin 4, ∀ σ : Fin 4 → ℂ, ‖σ‖ ≤ R →
      let ν := residueShifts i σ
      ‖originalProfileSum η L i (scaledShifts L σ) P Q -
        (arithmeticFactor:ℂ)*((η*L:ℝ):ℂ)^6*
          (dpNormalizedTriple η P (ν 0) (-(ν 1)) (-(ν 2))*
            dpNormalizedTriple η Q (ν 0) (-(ν 1)) (-(ν 2)))‖ ≤ C*L^5 := by
  simpa only [arithmeticConstant_eq_arithmeticFactor] using
    original_polynomial_profile_asymptotic hη hR hρ0 hρ P Q

end
end SixthMoment.Source.NoDPHarmonic
