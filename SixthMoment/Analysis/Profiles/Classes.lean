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


namespace SixthMoment
open Complex MeasureTheory Set
open scoped ComplexConjugate BigOperators
open Polynomial

noncomputable section

def SmoothInteriorProfile (a : ℝ) (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ioo 0 a

def SmoothDyadicWeight (Φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) Φ ∧ tsupport Φ ⊆ Icc 1 2

def WeightSeminormBound (J : ℕ) (B : ℝ) (Φ : ℝ → ℝ) : Prop :=
  ∀ j ≤ J, ∀ x : ℝ, ‖iteratedDeriv j Φ x‖ ≤ B

def zeroExtendedPolynomialProfile (η : ℝ) (P : ℝ[X]) : ℝ → ℝ :=
  (Ico 0 η).indicator (fun x => P.eval (1-x/η))

end
end SixthMoment
