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
import Std


namespace Sechstmoment

open Complex Polynomial
open scoped ComplexConjugate

noncomputable section

def manuscriptTestPolynomial (m : ℕ) : ℝ[X] :=
  match m with
  | 0 => 1
  | 1 => 2 * X
  | 2 => 8 * X ^ 2 - 1
  | 3 => 32 * X ^ 3 - 6 * X
  | 4 => 128 * X ^ 4 - 32 * X ^ 2 + 1
  | _ => 0

end

end Sechstmoment
