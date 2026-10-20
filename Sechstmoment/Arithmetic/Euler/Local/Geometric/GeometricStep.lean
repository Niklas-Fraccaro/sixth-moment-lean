import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring



namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
def step (a : R) (f : ℕ → R) : ℕ → R
  | 0 => f 0
  | n+1 => f (n+1) + a * step a f n
@[simp] theorem step_zero (a : R) (f : ℕ → R) : step a f 0 = f 0 := rfl
@[simp] theorem step_succ (a : R) (f : ℕ → R) (n : ℕ) :
    step a f (n+1) = f (n+1) + a * step a f n := rfl

end Sechstmoment.Source.NoDPLocal
