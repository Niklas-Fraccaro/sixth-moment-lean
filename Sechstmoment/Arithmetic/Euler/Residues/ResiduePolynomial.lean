import Sechstmoment.Arithmetic.Euler.Residues.ResidueCancellation

/-! Polynomial residue factors, their finite tails, and the existing principal factor. -/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

set_option linter.unusedSectionVars false
namespace Sechstmoment.Source.NoDPResidues
open NoDPLocal
open scoped BigOperators
variable {R S : Type*} [CommRing R] [CommRing S]

def residuePoly (a b c : R) (h : ℕ) : R := triNumerator a b c h 1

@[simp] theorem residuePoly_base (a b c : R) : residuePoly a b c 0 = 1 := by
  simp [residuePoly]

theorem residuePoly_first (a b c : R) :
    residuePoly a b c 1 = a+b+c-(a*b+a*c+b*c)+a*b*c := by
  have H := triNumerator_first a b c (1:R)
  rw [den3_expand] at H
  unfold residuePoly
  linear_combination H

theorem residuePoly_shift (a b c : R) (h : ℕ) :
    residuePoly a b c (h+1) = residuePoly a b c h-den3 a b c 1*coeff3 a b c h := by
  have H := triNumerator_shift a b c (1:R) h
  change residuePoly a b c h = coeff3 a b c h*den3 a b c 1+1*residuePoly a b c (h+1) at H
  linear_combination -H

theorem residuePoly_prefix (a b c : R) (h : ℕ) :
    residuePoly a b c h = 1-den3 a b c 1*(∑ k ∈ Finset.range h, coeff3 a b c k) := by
  induction h with
  | zero => simp
  | succ h ih => rw [residuePoly_shift, ih, Finset.sum_range_succ]; ring

theorem residuePoly_recurrence (a b c : R) (h : ℕ) :
    residuePoly a b c (h+3) = (a+b+c)*residuePoly a b c (h+2) -
      (a*b+a*c+b*c)*residuePoly a b c (h+1)+a*b*c*residuePoly a b c h := by
  simp only [residuePoly, triNumerator, triQ1, triQ2, Nat.add_assoc, coeff3_recurrence]
  ring

theorem residuePoly_swap_first (a b c : R) (h : ℕ) :
    residuePoly a b c h = residuePoly b a c h := by
  unfold residuePoly triNumerator triQ1 triQ2
  rw [coeff3_swap_first a b c h, coeff3_swap_first a b c (h+1),
    coeff3_swap_first a b c (h+2)]
  ring

theorem residuePoly_swap_last (a b c : R) (h : ℕ) :
    residuePoly a b c h = residuePoly a c b h := by
  unfold residuePoly triNumerator triQ1 triQ2
  rw [coeff3_swap_last a b c h, coeff3_swap_last a b c (h+1),
    coeff3_swap_last a b c (h+2)]
  ring

theorem residuePoly_cycle (a b c : R) (h : ℕ) :
    residuePoly a b c h = residuePoly b c a h := by
  rw [residuePoly_swap_first, residuePoly_swap_last]

theorem residuePoly_map (F : R →+* S) (a b c : R) (h : ℕ) :
    F (residuePoly a b c h) = residuePoly (F a) (F b) (F c) h := by
  simp [residuePoly, triNumerator, triQ1, triQ2, coeff3_map]

theorem residuePoly_scaled (a b c r : R) (h : ℕ) :
    residuePoly (r*a) (r*b) (r*c) h = r^h*triNumerator a b c h r := by
  simpa [residuePoly] using triNumerator_scaled a b c r (1:R) h

theorem coeff3_repeated_complex (x : ℂ) (h : ℕ) :
    coeff3 x x x h = ((h:ℂ)+1)*((h:ℂ)+2)/2*x^h := by
  have H := coeff3_map Complex.ofRealHom (1:ℝ) 1 1 h
  rw [coeff3_equal_roots] at H
  have H1 : coeff3 (1:ℂ) 1 1 h = ((h:ℂ)+1)*((h:ℂ)+2)/2 := by simpa using H.symm
  have E := coeff3_scaled (1:ℂ) 1 1 x h
  simp only [mul_one] at E
  rw [E, H1]
  ring

theorem residuePoly_eq_principalCorrection (x : ℂ) (h : ℕ) :
    residuePoly x x x h = principalCorrection x h := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [residuePoly_shift, ih, principalCorrection_succ, coeff3_repeated_complex]
    unfold den3
    ring

theorem residueLocal_eq_existing_principal (x : ℂ) (hx : ‖x‖ < 1) (h : ℕ) :
    residueLocal x x x x h = Sechstmoment.Source.principalLocalFactor x h := by
  rw [residueLocal_eq_triNumerator x x x x ‖x‖ (norm_nonneg x) le_rfl le_rfl le_rfl le_rfl hx]
  change residuePoly x x x h = _
  rw [residuePoly_eq_principalCorrection, principalCorrection_eq_existing x hx h]

@[simp] theorem residuePoly_zero_roots (h : ℕ) : residuePoly (0:R) 0 0 (h+1) = 0 := by
  simp [residuePoly, triNumerator, triQ1, triQ2, coeff3, coeff2, coeff1, Nat.add_assoc]

end Sechstmoment.Source.NoDPResidues
