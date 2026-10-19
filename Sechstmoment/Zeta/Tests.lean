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
import Sechstmoment.Zeta.Amplifiers
import Sechstmoment.Zeta.Generators
import Sechstmoment.Zeta.TestTypes
import Std

/-!
# The manuscript's actual U/V tests

These definitions use the Riemann zeta function and its complex derivatives.
They instantiate the exact phase projection of §1.1, and also assemble the 250
rows of Appendix A with their unscaled integer coefficients. They introduce no
asymptotic moment formula. The profile sum is indexed by `n+1` to exclude zero;
for the supported profiles and `T > 1` it is proved to be a finite Dirichlet sum.
-/

namespace Sechstmoment

open Complex Polynomial
open scoped ComplexConjugate

noncomputable section

/-- `F_U = χ C_p A_f overline(A_g)`, `F_V = C_p A_f A_g`, literally as in (1.1). -/
def rawZetaTest (τ : TestType) (T t : ℝ) (p : ℝ[X]) (f g : ℝ → ℝ) : ℂ :=
  match τ with
  | .U => criticalChi t * zetaCp T t p *
      profileDirichletSum T f (criticalLinePoint t) *
      profileDirichletSum T g (1 - criticalLinePoint t)
  | .V => zetaCp T t p * profileDirichletSum T f (criticalLinePoint t) *
      profileDirichletSum T g (criticalLinePoint t)

/-- The U test contains the literal conjugated second amplifier from (1.1).
The functional-equation replacement of `C_p` is not used in this identity. -/
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

/-- The actual test `H_p^τ(f,g) = Π_t F_τ`, exactly as in (1.1). -/
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

end Sechstmoment
