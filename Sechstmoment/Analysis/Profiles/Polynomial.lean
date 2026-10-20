import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Rat.Cast.Order
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Sechstmoment.Analysis.Profiles.Classes
import Std


namespace Sechstmoment
open Complex MeasureTheory Set Filter
open scoped Topology BigOperators

set_option maxHeartbeats 0

theorem zeroExtendedPolynomialProfile_add (η : ℝ) (P Q : Polynomial ℝ) :
    zeroExtendedPolynomialProfile η (P+Q) =
      zeroExtendedPolynomialProfile η P+zeroExtendedPolynomialProfile η Q := by
  funext x
  by_cases hx : x ∈ Ico 0 η <;>
    simp [zeroExtendedPolynomialProfile, hx, Polynomial.eval_add]

theorem zeroExtendedPolynomialProfile_sub (η : ℝ) (P Q : Polynomial ℝ) :
    zeroExtendedPolynomialProfile η (P-Q) =
      zeroExtendedPolynomialProfile η P-zeroExtendedPolynomialProfile η Q := by
  funext x
  by_cases hx : x ∈ Ico 0 η <;>
    simp [zeroExtendedPolynomialProfile, hx, Polynomial.eval_sub]

theorem zeroExtendedPolynomialProfile_zero_above (η : ℝ) (P : Polynomial ℝ)
    (x : ℝ) (hx : η < x) : zeroExtendedPolynomialProfile η P x = 0 := by
  have hn : x ∉ Ico 0 η := fun h => (not_lt_of_ge h.2.le) hx
  simp [zeroExtendedPolynomialProfile, hn]

end Sechstmoment
