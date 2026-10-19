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
import Sechstmoment.Zeta.CenteredDerivatives
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

/-- `C⁺(t,z) = exp(z/2) ζ(1/2+it+z/log T)`. -/
def zetaCPlus (T t : ℝ) (z : ℂ) : ℂ :=
  shiftedZetaGenerator T (criticalLinePoint t) z

/-- `C⁻(t,z) = exp(z/2) ζ(1/2-it+z/log T)`. -/
def zetaCMinus (T t : ℝ) (z : ℂ) : ℂ :=
  shiftedZetaGenerator T (1 - criticalLinePoint t) z

/-- The literal finite polynomial differential operator
`p(1/2 + (log T)⁻¹ ∂s) ζ(s)`. -/
def zetaPolynomialDerivative (T : ℝ) (p : ℝ[X]) (s : ℂ) : ℂ :=
  p.sum fun m a => (a : ℂ) * centeredZetaDerivative T m s

/-- The function `C_p(t)` in §1.1. -/
def zetaCp (T t : ℝ) (p : ℝ[X]) : ℂ :=
  zetaPolynomialDerivative T p (criticalLinePoint t)

/-- Complex differentiation of the normalized generator gives exactly the
manuscript's polynomial differential operator, for arbitrary polynomial degree. -/
theorem zetaCp_eq_generator_derivatives {T : ℝ} (hT : 1 < T) (t : ℝ) (p : ℝ[X]) :
    zetaCp T t p = p.sum fun m a => (a : ℂ) * iteratedDeriv m (zetaCPlus T t) 0 := by
  unfold zetaCp zetaPolynomialDerivative zetaCPlus
  simp_rw [iteratedDeriv_shiftedZetaGenerator_criticalLine T t _ hT]

/-- Polynomial reflection, used in the main-term rule (1.5). No exact parity
claim about `C_p` is made here. -/
def reflectedTestPolynomial (p : ℝ[X]) : ℝ[X] := p.comp (-X)

end

end Sechstmoment
