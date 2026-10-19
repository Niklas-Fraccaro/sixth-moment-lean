import Sechstmoment.Arithmetic.Euler.Local.Recurrence.ThreeAnnihilator

/-!
# Symmetric three-root coefficients and the residue cancellation
These identities hold over every commutative ring, including colliding or zero roots.
-/
set_option linter.unnecessarySeqFocus false

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

set_option linter.unusedSectionVars false
namespace Sechstmoment.Source.NoDPResidues
open NoDPLocal
open scoped BigOperators
variable {R : Type*} [CommRing R]

theorem coeff2_swap (a b : R) (n : ℕ) : coeff2 a b n = coeff2 b a n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 2
    · have hn' : n = 0 ∨ n = 1 := by omega
      rcases hn' with rfl | rfl <;> simp [coeff2_succ, coeff1] <;> ring
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hn)
      rw [Nat.add_comm 2 k, coeff2_recurrence, coeff2_recurrence,
        ih (k+1) (by omega), ih k (by omega)]
      ring

theorem coeff3_swap_last (a b c : R) (n : ℕ) : coeff3 a b c n = coeff3 a c b n := by
  have h : coeff2 b c = coeff2 c b := funext (coeff2_swap b c)
  simp only [coeff3, h]

theorem third_order_unique (a b c : R) (f g : ℕ → R)
    (hi : ∀ n < 3, f n = g n)
    (hf : ∀ n, f (n+3) = (a+b+c)*f (n+2) - (a*b+a*c+b*c)*f (n+1) + a*b*c*f n)
    (hg : ∀ n, g (n+3) = (a+b+c)*g (n+2) - (a*b+a*c+b*c)*g (n+1) + a*b*c*g n) : f = g := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 3
    · exact hi n hn
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hn)
      rw [Nat.add_comm 3 k, hf, hg, ih (k+2) (by omega),
        ih (k+1) (by omega), ih k (by omega)]

theorem coeff3_swap_first (a b c : R) (n : ℕ) : coeff3 a b c n = coeff3 b a c n := by
  have H : coeff3 a b c = coeff3 b a c := by
    apply third_order_unique a b c
    · intro k hk
      have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk' with rfl | rfl | rfl <;>
        simp [coeff3_succ, coeff2_succ, coeff1] <;> ring
    · exact coeff3_recurrence a b c
    · intro k
      rw [coeff3_recurrence]
      ring
  exact congrFun H n

theorem coeff3_cycle (a b c : R) (n : ℕ) : coeff3 a b c n = coeff3 b c a n := by
  rw [coeff3_swap_first, coeff3_swap_last]

theorem coeff3_reverse (a b c : R) (n : ℕ) : coeff3 a b c n = coeff3 c b a n := by
  rw [coeff3_swap_last, coeff3_swap_first, coeff3_swap_last]

theorem coeff3_one (a b c : R) : coeff3 a b c 1 = a+b+c := by
  simp [coeff3_succ, coeff2_succ, coeff1]
  ring

theorem coeff3_two (a b c : R) :
    coeff3 a b c 2 = a^2+b^2+c^2+a*b+a*c+b*c := by
  norm_num [coeff3_succ, coeff2_succ, coeff1]
  ring

theorem coeff3_cancel_first (a b c : R) (n : ℕ) :
    coeff3 a b c (n+1) - a*coeff3 a b c n = coeff2 b c (n+1) := by
  rw [coeff3_succ]
  ring

theorem coeff4_cancel_residue_root (x a b c : R) (n : ℕ) :
    coeff4 x a b c (n+1) - x*coeff4 x a b c n = coeff3 a b c (n+1) := by
  rw [coeff4_succ]
  ring

theorem coeff3_last_zero (a b : R) (n : ℕ) : coeff3 a b 0 n = coeff2 a b n := by
  rw [coeff3_reverse, coeff3_first_zero, coeff2_swap]

theorem coeff3_zero_roots (n : ℕ) : coeff3 (0:R) 0 0 (n+1) = 0 := by
  simp [coeff3, coeff2, coeff1]

end Sechstmoment.Source.NoDPResidues
