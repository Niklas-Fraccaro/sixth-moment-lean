import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Std

/-!
# Literal integrands at the two external-source interfaces

All four shifts here are raw complex shifts, rather than shifts silently divided
by `log T`. The BBLR integrand has one conjugated amplifier. The DP §5.2
integrand has two conjugated amplifiers and one factor `χ(s)`.
The exact functional-equation conversion retains its actual Gamma quotient.
No moment asymptotic or external theorem is asserted by this file.
-/

namespace Sechstmoment
open Complex MeasureTheory Set
open scoped ComplexConjugate BigOperators
open Polynomial

noncomputable section

/-- Four raw shifts, in the source order `α₁, α₂, α₃, α₄`. -/
abbrev MomentShifts := Fin 4 → ℂ

/-- Convert a normalized shift tuple to the raw shifts in the papers. -/
def rawMomentShifts (T : ℝ) (σ : MomentShifts) : MomentShifts :=
  fun j => σ j / (Real.log T : ℂ)

end
end Sechstmoment
