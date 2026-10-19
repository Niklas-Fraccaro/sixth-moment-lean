import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Sechstmoment.Certificate.Kernels.Unbalanced.IntegerEvaluator

namespace Sechstmoment.Finite

theorem factorial_eq_natFactorial (n : Nat) : factorial n = Nat.factorial n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [factorial, Nat.factorial_succ, ih]

theorem choose_eq_natChoose (n k : Nat) : choose n k = (Nat.choose n k : Int) := by
  unfold choose
  split_ifs with h
  · simp only [factorial_eq_natFactorial, Nat.choose_eq_factorial_div_factorial h]
  · simp [Nat.choose_eq_zero_of_lt (by omega : n < k)]

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem moment_terms_degrees_exact : ∀ k ∈ [0,2,4,6,8], ∀ mask ∈ List.range 8,
    ∀ tr ∈ momentTerms k mask, tr.i+tr.j+tr.l+tr.h = k+5 := by decide +kernel

theorem moment_terms_divisions_exact : ∀ k ∈ [0,2,4,6,8], ∀ mask ∈ List.range 8,
    ∀ tr ∈ momentTerms k mask,
      ((factorial tr.i*factorial tr.j*factorial tr.l*factorial tr.h : Nat) : Int)*tr.value =
        (factorial k : Int)*2^(8-k)*(factorial 13 : Int) := by decide +kernel

theorem d0_odd_divisions_exact : ∀ k ∈ List.range 5,
    (2*(k : ℤ)+1)*(315/(2*(k : ℤ)+1)) = 315 := by decide +kernel

theorem d0_half_width_exact (A B C D left right j : ℤ) :
    (scale-24*A-24*B-24*C-24*D+2*(24*left+2*(right-left)*j))/2*2 =
      scale-24*A-24*B-24*C-24*D+2*(24*left+2*(right-left)*j) := by
  apply Int.ediv_mul_cancel
  refine ⟨12*(base : ℤ)-12*A-12*B-12*C-12*D+24*left+2*(right-left)*j, ?_⟩
  unfold scale
  ring

theorem dminus_half_shift_exact (A B C D : ℤ) :
    (scale-(24*A+24*B+24*C-24*D))/2*2 = scale-(24*A+24*B+24*C-24*D) := by
  apply Int.ediv_mul_cancel
  refine ⟨12*(base : ℤ)-12*A-12*B-12*C+12*D, ?_⟩
  unfold scale
  ring

end Sechstmoment.Finite
