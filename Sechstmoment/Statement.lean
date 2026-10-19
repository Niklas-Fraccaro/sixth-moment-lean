import Mathlib.Data.Rat.Cast.Order
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Sechstmoment.Certificate.Bounds
import Sechstmoment.Zeta.SixthMoment

/-! This module STATES the original analytic goal. It contains no proof of
`MainClaim` or `FullGoal`, and no axiom asserting either proposition. -/

namespace Sechstmoment

noncomputable def MainClaim : Prop :=
  ((declaredBound : ℝ) : EReal) ≤
    Filter.liminf (fun T => (normalizedSixthMoment T : EReal)) Filter.atTop

noncomputable def FullGoal : Prop := ArithmeticFactorWellDefined ∧ MainClaim

end Sechstmoment
