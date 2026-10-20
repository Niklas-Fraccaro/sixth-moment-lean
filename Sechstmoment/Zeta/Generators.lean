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


namespace Sechstmoment

open Complex Polynomial
open scoped ComplexConjugate

noncomputable section

def zetaCPlus (T t : ℝ) (z : ℂ) : ℂ :=
  shiftedZetaGenerator T (criticalLinePoint t) z

def zetaCMinus (T t : ℝ) (z : ℂ) : ℂ :=
  shiftedZetaGenerator T (1 - criticalLinePoint t) z

def zetaPolynomialDerivative (T : ℝ) (p : ℝ[X]) (s : ℂ) : ℂ :=
  p.sum fun m a => (a : ℂ) * centeredZetaDerivative T m s

def zetaCp (T t : ℝ) (p : ℝ[X]) : ℂ :=
  zetaPolynomialDerivative T p (criticalLinePoint t)

theorem zetaCp_eq_generator_derivatives {T : ℝ} (hT : 1 < T) (t : ℝ) (p : ℝ[X]) :
    zetaCp T t p = p.sum fun m a => (a : ℂ) * iteratedDeriv m (zetaCPlus T t) 0 := by
  unfold zetaCp zetaPolynomialDerivative zetaCPlus
  simp_rw [iteratedDeriv_shiftedZetaGenerator_criticalLine T t _ hT]

def reflectedTestPolynomial (p : ℝ[X]) : ℝ[X] := p.comp (-X)

end

end Sechstmoment
