import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import SixthMoment.Zeta.Amplifiers
import SixthMoment.Zeta.Generators
import SixthMoment.Zeta.TestTypes
import Std


namespace SixthMoment

open Complex Polynomial
open scoped ComplexConjugate

noncomputable section

def rawZetaTest (τ : TestType) (T t : ℝ) (p : ℝ[X]) (f g : ℝ → ℝ) : ℂ :=
  match τ with
  | .U => criticalChi t * zetaCp T t p *
      profileDirichletSum T f (criticalLinePoint t) *
      profileDirichletSum T g (1 - criticalLinePoint t)
  | .V => zetaCp T t p * profileDirichletSum T f (criticalLinePoint t) *
      profileDirichletSum T g (criticalLinePoint t)

theorem rawZetaTest_U_eq_chi_mul_conj_amplifier (T t : ℝ)
    (p : ℝ[X]) (f g : ℝ → ℝ) :
    rawZetaTest .U T t p f g = criticalChi t * zetaCp T t p *
      profileDirichletSum T f (criticalLinePoint t) *
      conj (profileDirichletSum T g (criticalLinePoint t)) := by
  change criticalChi t * zetaCp T t p * profileDirichletSum T f (criticalLinePoint t) *
    profileDirichletSum T g (1-criticalLinePoint t) = _
  congr 1
  rw [criticalLinePoint_one_sub]
  change profileDirichletSum T g (conj (criticalLinePoint t)) = _
  exact profileDirichletSum_conj T g (criticalLinePoint t)

def projectedZetaTest (τ : TestType) (T t : ℝ) (p : ℝ[X]) (f g : ℝ → ℝ) : ℂ :=
  phaseProjection (criticalChi t) (rawZetaTest τ T t p f g)

theorem projectedZetaTest_real_structure (τ : TestType) (T t : ℝ)
    (p : ℝ[X]) (f g : ℝ → ℝ) :
    projectedZetaTest τ T t p f g =
      criticalChi t ^ 3 * star (projectedZetaTest τ T t p f g) :=
  zeta_phaseProjection_real_structure t _

theorem projectedZetaTest_mixed_re (τ : TestType) (T t : ℝ)
    (p : ℝ[X]) (f g : ℝ → ℝ) :
    riemannZeta (criticalLinePoint t) ^ 3 * star (projectedZetaTest τ T t p f g) =
      ((riemannZeta (criticalLinePoint t) ^ 3 * star (rawZetaTest τ T t p f g)).re : ℂ) :=
  zeta_phaseProjection_mixed_re t _

theorem projectedZetaTest_gram (τ σ : TestType) (T t : ℝ)
    (p q : ℝ[X]) (f g h k : ℝ → ℝ) :
    projectedZetaTest τ T t p f g * star (projectedZetaTest σ T t q h k) =
      (1 / 2 : ℂ) * ((rawZetaTest τ T t p f g * star (rawZetaTest σ T t q h k) +
        (star (criticalChi t)) ^ 3 * rawZetaTest τ T t p f g *
          rawZetaTest σ T t q h k).re : ℂ) :=
  zeta_phaseProjection_gram t _ _

end

end SixthMoment
