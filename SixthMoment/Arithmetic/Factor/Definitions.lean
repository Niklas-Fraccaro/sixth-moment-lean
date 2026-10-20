import Mathlib.Data.Rat.Cast.Order
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.EReal.Lemmas


namespace SixthMoment

noncomputable def eulerFactor (p : ℝ) : ℝ :=
  (1-1/p)^4*(1+4/p+1/p^2)

noncomputable def arithmeticFactor : ℝ :=
  ∏' p : {n : ℕ // Nat.Prime n}, eulerFactor (p.val : ℝ)

def ArithmeticFactorWellDefined : Prop :=
  Multipliable (fun p : {n : ℕ // Nat.Prime n} => eulerFactor (p.val : ℝ)) ∧
    0 < arithmeticFactor

theorem eulerFactor_expansion (x : ℝ) :
    (1-x)^4*(1+4*x+x^2) = 1-9*x^2+16*x^3-9*x^4+x^6 := by ring

theorem eulerFactor_prime_pos (p : {n : ℕ // Nat.Prime n}) :
    0 < eulerFactor (p.val : ℝ) := by
  have hp : 1 < (p.val : ℝ) := by exact_mod_cast p.property.one_lt
  have hp₀ : 0 < (p.val : ℝ) := by linarith
  have hi : 1/(p.val : ℝ) < 1 := (div_lt_one hp₀).mpr hp
  have ha : 0 < 1-1/(p.val : ℝ) := by linarith
  unfold eulerFactor
  apply mul_pos (pow_pos ha 4)
  positivity

end SixthMoment
