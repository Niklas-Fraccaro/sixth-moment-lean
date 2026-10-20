import Mathlib.Data.Rat.Cast.Order
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import SixthMoment.Arithmetic.Factor.Definitions


namespace SixthMoment

noncomputable def sixthMoment (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, ‖riemannZeta ((1/2 : ℂ)+(t : ℂ)*Complex.I)‖^6

noncomputable def normalizedSixthMoment (T : ℝ) : ℝ :=
  sixthMoment T / ((arithmeticFactor/(Nat.factorial 9 : ℝ))*T*(Real.log T)^9)

end SixthMoment
