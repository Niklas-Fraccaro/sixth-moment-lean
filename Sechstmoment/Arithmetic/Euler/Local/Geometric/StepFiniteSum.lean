import Mathlib.Algebra.BigOperators.Ring.Finset
import Sechstmoment.Arithmetic.Euler.Local.Rational.DenominatorNonzero

/-! A finite formula for the geometric convolution. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem step_eq_sum (a : R) (f : ℕ → R) (n : ℕ) :
    step a f n=∑ k ∈ range (n+1), a^(n-k)*f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [step_succ,ih]
    have hs : (∑ k ∈ range (n+1), a^(n+1-k)*f k)=a*(∑ k ∈ range (n+1), a^(n-k)*f k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k≤n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [show n+1-k=(n-k)+1 by omega,pow_succ]; ring
    symm
    rw [Finset.sum_range_succ,hs]
    simp only [Nat.sub_self,pow_zero,one_mul]
    ring

end Sechstmoment.Source.NoDPLocal
