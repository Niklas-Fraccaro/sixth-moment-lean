import SixthMoment.Denominator.Unbalanced.Conjugation
import SixthMoment.Zeta.Tests

namespace SixthMoment
open Complex MeasureTheory Set Polynomial
open scoped ComplexConjugate BigOperators
noncomputable section
set_option maxHeartbeats 0

def d06PolynomialReflectionError (T t : ℝ) (q : ℝ[X]) : ℂ :=
  (criticalChi t)⁻¹ * zetaCp T t q -
    zetaPolynomialDerivative T (reflectedTestPolynomial q) (1-criticalLinePoint t)

theorem d06PolynomialReflectionError_identity (T t : ℝ) (q : ℝ[X]) :
    (criticalChi t)⁻¹ * zetaCp T t q =
      zetaPolynomialDerivative T (reflectedTestPolynomial q) (1-criticalLinePoint t) +
        d06PolynomialReflectionError T t q := by
  unfold d06PolynomialReflectionError
  ring

def d06UUConjugateProfiles (ρ : Fin 4 → ℝ → ℝ) : Fin 4 → ℝ → ℝ :=
  ![ρ 0,ρ 3,ρ 1,ρ 2]

def d06UUReflectedProfiles (ρ : Fin 4 → ℝ → ℝ) : Fin 4 → ℝ → ℝ :=
  ![ρ 0,ρ 2,ρ 1,ρ 3]

def d06UVReflectedProfiles (ρ : Fin 4 → ℝ → ℝ) : Fin 4 → ℝ → ℝ :=
  ![ρ 0,ρ 2,ρ 3,ρ 1]

def d06BalancedPolynomialIntegrand (T t : ℝ) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) : ℂ :=
  zetaCp T t p * zetaPolynomialDerivative T q (1-criticalLinePoint t) *
    d02BalancedAmplifier T t ρ

def d06UnbalancedPlusPolynomialIntegrand (T t : ℝ) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) : ℂ :=
  criticalChi t * zetaCp T t p *
    zetaPolynomialDerivative T q (1-criticalLinePoint t) *
      d04UnbalancedPlusAmplifier T t ρ

def d06UnbalancedMinusPolynomialIntegrand (T t : ℝ) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) : ℂ :=
  (criticalChi t)⁻¹ * zetaCp T t p *
    zetaPolynomialDerivative T q (1-criticalLinePoint t) *
      d04UnbalancedAmplifier T t ρ

def d06VVExtremePolynomialIntegrand (T t : ℝ) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) : ℂ :=
  ((criticalChi t)⁻¹)^3 * zetaCp T t p * zetaCp T t q *
    profileDirichletSum T (ρ 0) (criticalLinePoint t) *
    profileDirichletSum T (ρ 1) (criticalLinePoint t) *
    profileDirichletSum T (ρ 2) (criticalLinePoint t) *
    profileDirichletSum T (ρ 3) (criticalLinePoint t)

def d06UUReflectionIntegrand (T t : ℝ) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) : ℂ :=
  zetaCp T t p * d06PolynomialReflectionError T t q *
    d02BalancedAmplifier T t (d06UUReflectedProfiles ρ)

def d06UVReflectionIntegrand (T t : ℝ) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) : ℂ :=
  (criticalChi t)⁻¹ * zetaCp T t p * d06PolynomialReflectionError T t q *
    d04UnbalancedAmplifier T t (d06UVReflectedProfiles ρ)

private theorem d06_profile_star_plus (T t : ℝ) (f : ℝ → ℝ) :
    star (profileDirichletSum T f (criticalLinePoint t)) =
      profileDirichletSum T f (1-criticalLinePoint t) := by
  rw [criticalLinePoint_one_sub]
  exact (profileDirichletSum_conj T f (criticalLinePoint t)).symm

private theorem d06_profile_star_minus (T t : ℝ) (f : ℝ → ℝ) :
    star (profileDirichletSum T f (1-criticalLinePoint t)) =
      profileDirichletSum T f (criticalLinePoint t) := by
  rw [criticalLinePoint_one_sub]
  change conj (profileDirichletSum T f (conj (criticalLinePoint t))) = _
  rw [profileDirichletSum_conj,conj_conj]

theorem d06ProjectedGram_UU (T t : ℝ) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) :
    projectedZetaTest .U T t p (ρ 0) (ρ 1) *
      star (projectedZetaTest .U T t q (ρ 2) (ρ 3)) =
    (1/2 : ℂ) * ((d06BalancedPolynomialIntegrand T t p q (d06UUConjugateProfiles ρ) +
      d06BalancedPolynomialIntegrand T t p (reflectedTestPolynomial q)
        (d06UUReflectedProfiles ρ) + d06UUReflectionIntegrand T t p q ρ).re : ℂ) := by
  rw [projectedZetaTest_gram]
  congr 2
  congr 1
  simp only [rawZetaTest,star_mul,d04_zetaCp_conj,d06_profile_star_plus,
    d06_profile_star_minus,show star (criticalChi t) = (criticalChi t)⁻¹
      from d04_criticalChi_conj t]
  unfold d06BalancedPolynomialIntegrand d06UUReflectionIntegrand
    d06PolynomialReflectionError d02BalancedAmplifier
    d06UUConjugateProfiles d06UUReflectedProfiles
  simp
  field_simp [criticalChi_ne_zero t]
  ring

theorem d06ProjectedGram_VV (T t : ℝ) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) :
    projectedZetaTest .V T t p (ρ 0) (ρ 1) *
      star (projectedZetaTest .V T t q (ρ 2) (ρ 3)) =
    (1/2 : ℂ) * ((d06BalancedPolynomialIntegrand T t p q ρ +
      d06VVExtremePolynomialIntegrand T t p q ρ).re : ℂ) := by
  rw [projectedZetaTest_gram]
  congr 2
  congr 1
  simp only [rawZetaTest,star_mul,d04_zetaCp_conj,d06_profile_star_plus,
    show star (criticalChi t) = (criticalChi t)⁻¹ from d04_criticalChi_conj t]
  unfold d06BalancedPolynomialIntegrand d02BalancedAmplifier
    d06VVExtremePolynomialIntegrand
  ring

theorem d06ProjectedGram_UV (T t : ℝ) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) :
    projectedZetaTest .U T t p (ρ 0) (ρ 1) *
      star (projectedZetaTest .V T t q (ρ 2) (ρ 3)) =
    (1/2 : ℂ) * ((d06UnbalancedPlusPolynomialIntegrand T t p q ρ +
      d06UnbalancedMinusPolynomialIntegrand T t p (reflectedTestPolynomial q)
        (d06UVReflectedProfiles ρ) + d06UVReflectionIntegrand T t p q ρ).re : ℂ) := by
  rw [projectedZetaTest_gram]
  congr 2
  congr 1
  simp only [rawZetaTest,star_mul,d04_zetaCp_conj,d06_profile_star_plus,
    show star (criticalChi t) = (criticalChi t)⁻¹ from d04_criticalChi_conj t]
  unfold d06UnbalancedPlusPolynomialIntegrand d04UnbalancedPlusAmplifier
    d06UnbalancedMinusPolynomialIntegrand d04UnbalancedAmplifier
    d06UVReflectionIntegrand d06PolynomialReflectionError d06UVReflectedProfiles
  simp [d04UnbalancedAmplifier]
  field_simp [criticalChi_ne_zero t]
  ring

end
end SixthMoment
