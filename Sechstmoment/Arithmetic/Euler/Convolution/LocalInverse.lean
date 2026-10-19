import Sechstmoment.Arithmetic.Euler.Convolution.PairEuler

/-! Exact inversion of the six causal Euler operators, on arbitrary coefficient arrays. -/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Sechstmoment.Source.NoDPGlobalConvolution
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest
open scoped BigOperators
noncomputable section
variable {R : Type*} [CommRing R]

def natConv (f g : ℕ → R) (n : ℕ) : R :=
  ∑ i ∈ Finset.range (n+1), f i * g (n-i)

theorem natConv_comm (f g : ℕ → R) (n : ℕ) : natConv f g n = natConv g f n := by
  rw [natConv, natConv, ← Finset.sum_range_reflect (fun i => g i * f (n-i)) (n+1)]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  simp only [Nat.add_sub_cancel, Nat.sub_sub_self hi']
  exact mul_comm _ _

theorem natConv_succ (f g : ℕ → R) (n : ℕ) :
    natConv f g (n+1) = f 0 * g (n+1) +
      ∑ i ∈ Finset.range (n+1), f (i+1) * g (n-i) := by
  rw [natConv, Finset.sum_range_succ']
  simp only [Nat.sub_zero, Nat.add_sub_add_right]
  exact add_comm _ _

theorem back_natConv (a : R) (f g : ℕ → R) :
    back a (natConv f g) = natConv (back a f) g := by
  funext n
  cases n with
  | zero => simp [natConv]
  | succ n =>
    rw [back_succ, natConv_succ, natConv_succ]
    simp only [back_zero, back_succ, sub_mul, Finset.sum_sub_distrib]
    rw [natConv, Finset.mul_sum]
    ring

theorem back_injective (a : R) : Function.Injective (back a : (ℕ → R) → (ℕ → R)) := by
  intro f g h
  funext n
  rw [← step_back a f n, h, step_back]

theorem threeBack_injective (a b c : R) :
    Function.Injective (threeBack a b c : (ℕ → R) → (ℕ → R)) :=
  (back_injective a).comp ((back_injective b).comp (back_injective c))

theorem threeBack_natConv (a b c : R) (f g : ℕ → R) :
    threeBack a b c (natConv f g) = natConv (threeBack a b c f) g := by
  simp only [threeBack, back_natConv]

theorem natConv_delta (g : ℕ → R) :
    natConv (fun i => if i = 0 then 1 else 0) g = g := by
  funext n
  simp [natConv]

theorem coeff3_natConv_inverse (a b c : R) (f : ℕ → R) :
    natConv (coeff3 a b c) (threeBack a b c f) = f := by
  apply threeBack_injective a b c
  rw [threeBack_natConv, show threeBack a b c (coeff3 a b c) =
    (fun i => if i = 0 then 1 else 0) from funext (threeBack_coeff3 a b c)]
  exact natConv_delta _

theorem coeff3_inverse_sum (a b c : R) (f : ℕ → R) (n : ℕ) :
    f n = ∑ i : Fin (n+1), threeBack a b c f i.val * coeff3 a b c (n-i.val) := by
  have H := congrFun (coeff3_natConv_inverse a b c f) n
  rw [natConv_comm, natConv, ← Fin.sum_univ_eq_sum_range] at H
  exact H.symm

/-- Recover an arbitrary array from its six Euler differences. -/
theorem regularizedCoeff_inverse (a b c : R) (F : ℕ → ℕ → R) (h k : ℕ) :
    F h k = ∑ i : Fin (h+1), ∑ j : Fin (k+1),
      regularizedCoeff a b c F i.val j.val *
        coeff3 a b c (h-i.val) * coeff3 a b c (k-j.val) := by
  rw [coeff3_inverse_sum a b c (fun n => F n k) h]
  apply Finset.sum_congr rfl
  intro i _
  have H := coeff3_inverse_sum a b c (fun n => threeBack a b c (fun m => F m n) i.val) k
  rw [H, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  change extractRight a b c (extractLeft a b c F) i.val j.val * _ * _ = _
  rw [← extract_commute]
  change regularizedCoeff a b c F i.val j.val * _ * _ = _
  ring

end
end Sechstmoment.Source.NoDPGlobalConvolution
