import Sechstmoment.Arithmetic.Euler.Local.Coefficients.Scaling
import Sechstmoment.Arithmetic.Euler.Residues.ThreeAlgebra

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

set_option linter.unusedSectionVars false
namespace Sechstmoment.Source.NoDPResidues
open NoDPLocal
variable {R : Type*} [CommRing R]

def den3 (a b c t : R) : R := (1-a*t)*(1-b*t)*(1-c*t)
def triQ1 (a b c : R) (h : ℕ) : R :=
  coeff3 a b c (h+1) - (a+b+c)*coeff3 a b c h
def triQ2 (a b c : R) (h : ℕ) : R :=
  coeff3 a b c (h+2) - (a+b+c)*coeff3 a b c (h+1) + (a*b+a*c+b*c)*coeff3 a b c h
def triNumerator (a b c : R) (h : ℕ) (t : R) : R :=
  coeff3 a b c h + triQ1 a b c h*t + triQ2 a b c h*t^2

theorem den3_expand (a b c t : R) :
    den3 a b c t = 1-(a+b+c)*t+(a*b+a*c+b*c)*t^2-a*b*c*t^3 := by
  unfold den3
  ring

theorem denom_split_root (x a b c t : R) :
    denom x a b c t = (1-x*t)*den3 a b c t := by
  unfold denom den3
  ring

theorem triQ1_boundary (a b c : R) (h : ℕ) :
    triQ1 a b c (h+2) = -(a*b+a*c+b*c)*coeff3 a b c (h+1) + a*b*c*coeff3 a b c h := by
  unfold triQ1
  rw [show h+2+1 = h+3 by omega, coeff3_recurrence]
  ring

theorem triQ2_boundary (a b c : R) (h : ℕ) :
    triQ2 a b c (h+1) = a*b*c*coeff3 a b c h := by
  unfold triQ2
  rw [show h+1+2 = h+3 by omega, show h+1+1 = h+2 by omega,
    coeff3_recurrence]
  ring

@[simp] theorem triQ1_base (a b c : R) : triQ1 a b c 0 = 0 := by
  simp [triQ1, coeff3_one]
@[simp] theorem triQ2_base (a b c : R) : triQ2 a b c 0 = 0 := by
  simp [triQ2, coeff3_one, coeff3_two]
  ring
@[simp] theorem triNumerator_base (a b c t : R) : triNumerator a b c 0 t = 1 := by
  simp [triNumerator]
@[simp] theorem triNumerator_at_zero (a b c : R) (h : ℕ) :
    triNumerator a b c h 0 = coeff3 a b c h := by simp [triNumerator]

theorem triNumerator_shift (a b c t : R) (h : ℕ) :
    triNumerator a b c h t = coeff3 a b c h*den3 a b c t + t*triNumerator a b c (h+1) t := by
  unfold triNumerator triQ1 triQ2
  rw [den3_expand, show h+1+2=h+3 by omega, show h+1+1=h+2 by omega,
    coeff3_recurrence]
  ring

theorem triNumerator_first (a b c t : R) :
    t*triNumerator a b c 1 t = 1-den3 a b c t := by
  have H := triNumerator_shift a b c t 0
  simpa using (show t*triNumerator a b c 1 t = 1-den3 a b c t by
    simpa only [triNumerator_base, coeff3_zero, one_mul] using
      (eq_sub_iff_add_eq.mpr (by simpa [add_comm] using H.symm)))

theorem numerator_drop_zero_root (a b c : R) (h : ℕ) (t : R) :
    numerator 0 a b c h t = triNumerator a b c h t := by
  simp [numerator, q0, q1, q2, q3, e1, e2, e3, triNumerator, triQ1, triQ2,
    coeff4_first_zero, coeff3_recurrence]
  ring

theorem triQ1_scaled (a b c r : R) (h : ℕ) :
    triQ1 (r*a) (r*b) (r*c) h = r^(h+1)*triQ1 a b c h := by
  simp only [triQ1, coeff3_scaled, pow_succ]
  ring

theorem triQ2_scaled (a b c r : R) (h : ℕ) :
    triQ2 (r*a) (r*b) (r*c) h = r^(h+2)*triQ2 a b c h := by
  simp only [triQ2, coeff3_scaled, pow_add, pow_one]
  ring

theorem triNumerator_scaled (a b c r t : R) (h : ℕ) :
    triNumerator (r*a) (r*b) (r*c) h t = r^h*triNumerator a b c h (r*t) := by
  simp only [triNumerator, coeff3_scaled, triQ1_scaled, triQ2_scaled, pow_add, pow_one]
  ring

end Sechstmoment.Source.NoDPResidues
