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

/-- Smooth profiles with literal compact support inside `(0,a)`. -/
def SmoothInteriorProfile (a : ℝ) (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ioo 0 a

/-- The smooth dyadic weight class used by BBLR. -/
def SmoothDyadicWeight (Φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) Φ ∧ tsupport Φ ⊆ Icc 1 2

/-- An explicit finite seminorm bound, allowing a family of source weights. -/
def WeightSeminormBound (J : ℕ) (B : ℝ) (Φ : ℝ → ℝ) : Prop :=
  ∀ j ≤ J, ∀ x : ℝ, ‖iteratedDeriv j Φ x‖ ≤ B

/-- The polynomial profile at the DP source interface. The source sets
`P[n]=0` at `n≥y`, so the upper endpoint is excluded, even when `P(0)≠0`. -/
def zeroExtendedPolynomialProfile (η : ℝ) (P : ℝ[X]) : ℝ → ℝ :=
  (Ico 0 η).indicator (fun x => P.eval (1-x/η))

end
end Sechstmoment
