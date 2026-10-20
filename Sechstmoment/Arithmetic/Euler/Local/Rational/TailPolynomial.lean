import Sechstmoment.Arithmetic.Euler.Local.Recurrence.FourRecurrence


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
def tail4 (a b c d : R) (h n : ℕ) := coeff4 a b c d (h+n)
@[simp] theorem tail4_zero (a b c d : R) (h : ℕ) : tail4 a b c d h 0 = coeff4 a b c d h := rfl
theorem tail4_translate (a b c d : R) (h k n : ℕ) :
    tail4 a b c d (h+k) n = tail4 a b c d h (k+n) := by simp [tail4, Nat.add_assoc]

end Sechstmoment.Source.NoDPLocal


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
def q0 (a b c d : R) (h : ℕ) := coeff4 a b c d h
@[simp] theorem q0_zero (a b c d : R) : q0 a b c d 0 = 1 := by simp [q0]
theorem q0_eq_tail (a b c d : R) (h : ℕ) : q0 a b c d h = tail4 a b c d h 0 := rfl

end Sechstmoment.Source.NoDPLocal


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
def q1 (a b c d : R) (h : ℕ) := coeff4 a b c d (h+1)-e1 a b c d*coeff4 a b c d h
@[simp] theorem q1_zero (a b c d : R) : q1 a b c d 0 = 0 := by simp [q1,e1]
theorem q1_eq (a b c d : R) (h : ℕ) :
    coeff4 a b c d (h+1) = q1 a b c d h+e1 a b c d*q0 a b c d h := by unfold q1 q0; ring

end Sechstmoment.Source.NoDPLocal


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
def q2 (a b c d : R) (h : ℕ) := coeff4 a b c d (h+2)-
  e1 a b c d*coeff4 a b c d (h+1)+e2 a b c d*coeff4 a b c d h
theorem q2_eq (a b c d : R) (h : ℕ) :
    coeff4 a b c d (h+2) = q2 a b c d h+e1 a b c d*coeff4 a b c d (h+1)-e2 a b c d*coeff4 a b c d h := by
  unfold q2; ring

end Sechstmoment.Source.NoDPLocal


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
def q3 (a b c d : R) (h : ℕ) := coeff4 a b c d (h+3)-e1 a b c d*coeff4 a b c d (h+2)+
  e2 a b c d*coeff4 a b c d (h+1)-e3 a b c d*coeff4 a b c d h
theorem q3_eq (a b c d : R) (h : ℕ) :
    coeff4 a b c d (h+3) = q3 a b c d h+e1 a b c d*coeff4 a b c d (h+2)-
      e2 a b c d*coeff4 a b c d (h+1)+e3 a b c d*coeff4 a b c d h := by unfold q3; ring

end Sechstmoment.Source.NoDPLocal


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
def numerator (a b c d : R) (h : ℕ) (t : R) :=
  q0 a b c d h+q1 a b c d h*t+q2 a b c d h*t^2+q3 a b c d h*t^3
@[simp] theorem numerator_at_zero (a b c d : R) (h : ℕ) :
    numerator a b c d h 0 = coeff4 a b c d h := by simp [numerator,q0]

end Sechstmoment.Source.NoDPLocal
