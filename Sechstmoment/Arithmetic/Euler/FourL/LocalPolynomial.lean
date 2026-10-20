import Sechstmoment.Arithmetic.Euler.FourL.FourCoefficients

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Sechstmoment.Source.NoDPGlobalLFactorization
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest NoDPGlobalConvolution
open scoped BigOperators
noncomputable section
variable {R : Type*} [CommRing R]

def fourBack (a b c d : R) (f : ℕ → R) := back a (threeBack b c d f)

theorem fourBack_injective (a b c d : R) :
    Function.Injective (fourBack a b c d : (ℕ → R) → (ℕ → R)) :=
  (back_injective a).comp (threeBack_injective b c d)

theorem fourBack_natConv (a b c d : R) (f g : ℕ → R) :
    fourBack a b c d (natConv f g) = natConv (fourBack a b c d f) g := by
  simp only [fourBack,threeBack_natConv,back_natConv]

theorem fourBack_coeff4 (a b c d : R) (n : ℕ) :
    fourBack a b c d (coeff4 a b c d) n = if n = 0 then 1 else 0 := by
  have H : back a (threeBack b c d (coeff4 a b c d)) =
      threeBack b c d (back a (coeff4 a b c d)) := by
    unfold threeBack
    rw [show back a (back b (back c (back d (coeff4 a b c d)))) =
      back b (back a (back c (back d (coeff4 a b c d)))) from
      funext (back_commute a b _)]
    rw [show back a (back c (back d (coeff4 a b c d))) =
      back c (back a (back d (coeff4 a b c d))) from funext (back_commute a c _)]
    rw [show back a (back d (coeff4 a b c d)) = back d (back a (coeff4 a b c d)) from
      funext (back_commute a d _)]
  rw [fourBack,H,show back a (coeff4 a b c d) = coeff3 b c d from
    funext (back_step a (coeff3 b c d))]
  exact threeBack_coeff3 b c d n

theorem coeff4_inverse_sum (a b c d : R) (f : ℕ → R) (n : ℕ) :
    f n = ∑ i : Fin (n+1), fourBack a b c d f i.val * coeff4 a b c d (n-i.val) := by
  have H : natConv (coeff4 a b c d) (fourBack a b c d f) = f := by
    apply fourBack_injective a b c d
    rw [fourBack_natConv,show fourBack a b c d (coeff4 a b c d) =
      (fun i => if i = 0 then 1 else 0) from funext (fourBack_coeff4 a b c d)]
    exact natConv_delta _
  have Hn := congrFun H n
  rw [natConv_comm,natConv,← Fin.sum_univ_eq_sum_range] at Hn
  exact Hn.symm

def numeratorCoeff (a b c d : R) (h : ℕ) : ℕ → R :=
  fourBack a b c d (fun k => coeff4 a b c d (h+k))

@[simp] theorem numeratorCoeff_zero (a b c d : R) (h : ℕ) :
    numeratorCoeff a b c d h 0 = q0 a b c d h := by simp [numeratorCoeff,fourBack,q0]

theorem numeratorCoeff_one (a b c d : R) (h : ℕ) :
    numeratorCoeff a b c d h 1 = q1 a b c d h := by
  simp only [numeratorCoeff,fourBack,threeBack,back,q1,e1,Nat.add_zero]
  ring

theorem numeratorCoeff_two (a b c d : R) (h : ℕ) :
    numeratorCoeff a b c d h 2 = q2 a b c d h := by
  simp only [numeratorCoeff,fourBack,threeBack,back,q2,e1,e2,Nat.add_zero]
  ring

theorem numeratorCoeff_three (a b c d : R) (h : ℕ) :
    numeratorCoeff a b c d h 3 = q3 a b c d h := by
  simp only [numeratorCoeff,fourBack,threeBack,back,q3,e1,e2,e3,Nat.add_zero]
  ring

theorem fourBack_high (a b c d : R) (f : ℕ → R) (n : ℕ) :
    fourBack a b c d f (n+4) = f (n+4)-e1 a b c d*f (n+3)+
      e2 a b c d*f (n+2)-e3 a b c d*f (n+1)+e4 a b c d*f n := by
  simp only [fourBack,threeBack,back,e1,e2,e3,e4]
  ring

theorem numeratorCoeff_high (a b c d : R) (h n : ℕ) :
    numeratorCoeff a b c d h (n+4) = 0 := by
  rw [numeratorCoeff,fourBack_high]
  simp only [← Nat.add_assoc]
  rw [coeff4_recurrence a b c d (h+n)]
  ring

theorem numeratorCoeff_base (a b c d : R) (k : ℕ) :
    numeratorCoeff a b c d 0 k = if k = 0 then 1 else 0 := by
  simpa only [numeratorCoeff,Nat.zero_add] using fourBack_coeff4 a b c d k

theorem numeratorCoeff_evaluate (a b c d t : R) (h : ℕ) :
    (∑ j : Fin 4, numeratorCoeff a b c d h j.val * t^j.val) = numerator a b c d h t := by
  simp [Fin.sum_univ_succ,numeratorCoeff_zero,numeratorCoeff_one,numeratorCoeff_two,
    numeratorCoeff_three,numerator,add_assoc]

theorem numeratorCoeff_convolution (a b c d : R) (h k : ℕ) :
    coeff4 a b c d (h+k) = ∑ i : Fin (k+1), numeratorCoeff a b c d h i.val *
      coeff4 a b c d (k-i.val) :=
  coeff4_inverse_sum a b c d (fun n => coeff4 a b c d (h+n)) k

end
end Sechstmoment.Source.NoDPGlobalLFactorization
