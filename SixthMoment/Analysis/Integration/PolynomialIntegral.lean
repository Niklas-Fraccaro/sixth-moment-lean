import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Ring

namespace SixthMoment

open scoped BigOperators
open MeasureTheory

theorem integral_finite_polynomial {n : ℕ} (c : Fin n → ℝ) (a b : ℝ) :
    (∫ x in a..b, ∑ k : Fin n, c k * x^k.val) =
      ∑ k : Fin n, c k * (b^(k.val+1)-a^(k.val+1))/(k.val+1) := by
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_const_mul, integral_pow]
    ring
  · intro k _
    exact (continuous_const.mul (continuous_id.pow k.val)).intervalIntegrable a b

end SixthMoment
