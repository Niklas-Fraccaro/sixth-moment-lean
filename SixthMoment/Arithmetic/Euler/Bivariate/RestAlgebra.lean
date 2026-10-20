import SixthMoment.Arithmetic.Euler.Residues.DoubleSeries

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace SixthMoment.Source.NoDPLocalClosure
open NoDPLocal NoDPResidues Finset
open scoped BigOperators

noncomputable def restA (ai a b c x : ℂ) : ℂ := -x^2/ai*(a*b+a*c+b*c)+x^3/ai^2*(a*b*c)
noncomputable def restB (ai a b c x : ℂ) : ℂ := x^3/ai*(a*b*c)
noncomputable def restC (ai a b c x : ℂ) : ℂ :=
  -x^2*(a*b+a*c+b*c)+x^3/ai*((a+b+c)*(a*b+a*c+b*c)+a*b*c)-x^4/ai^2*((a+b+c)*a*b*c)
noncomputable def restD (ai a b c x : ℂ) : ℂ := x^3*(a*b*c)-x^4/ai*((a+b+c)*a*b*c)
noncomputable def restE (ai a b c x : ℂ) : ℂ := x^6/ai^2*(a*b*c)^2
noncomputable def restPolynomial (ai a b c x U V : ℂ) : ℂ :=
  1+restA ai a b c x*(U+V)+restB ai a b c x*(U^2+V^2)+restC ai a b c x*U*V+
    restD ai a b c x*(U^2*V+U*V^2)+restE ai a b c x*U^2*V^2

def restBox : Finset (ℕ × ℕ) := range 3 ×ˢ range 3

theorem threeBack_zero_sequence {R : Type*} [CommRing R] (a b c : R) (n : ℕ) :
    threeBack a b c (fun _ => 0) n = 0 := by
  have H (z : R) : back z (fun _ => 0) = (fun _ => 0) := by
    funext k
    cases k <;> simp [back]
  simp only [threeBack, H]

theorem weighted_threeBack_tail (ai a b c x : ℂ) (hai : ai ≠ 0) (k n : ℕ) :
    threeBack (x*a) (x*b) (x*c) (fun m => weightedResidue ai a b c x (m+k)) (n+3) = 0 := by
  rw [threeBack_high]
  rw [show n+3+k=(n+k)+3 by omega, show n+2+k=(n+k)+2 by omega,
    show n+1+k=(n+k)+1 by omega, weightedResidue_recurrence ai a b c x hai]
  ring

theorem residueRest_left_vanishes (ai a b c x : ℂ) (hai : ai ≠ 0) (m n : ℕ) :
    residueRest ai a b c x (m+3) n = 0 := by
  unfold residueRest regularizedCoeff
  rw [extract_commute]
  unfold extractRight
  have H : extractLeft (x*a) (x*b) (x*c) (fun h k => weightedResidue ai a b c x (h+k)) (m+3) =
      (fun _ => 0) := funext (fun k => weighted_threeBack_tail ai a b c x hai k m)
  rw [H]
  exact threeBack_zero_sequence _ _ _ _

theorem residueRest_symmetric (ai a b c x : ℂ) (m n : ℕ) :
    residueRest ai a b c x m n = residueRest ai a b c x n m :=
  regularizedCoeff_diagonal_symm _ _ _ _ m n

theorem residueRest_right_vanishes (ai a b c x : ℂ) (hai : ai ≠ 0) (m n : ℕ) :
    residueRest ai a b c x m (n+3) = 0 := by
  rw [residueRest_symmetric]
  exact residueRest_left_vanishes ai a b c x hai n m

theorem residueRest_support (ai a b c x : ℂ) (hai : ai ≠ 0) (m n : ℕ)
    (h : 3 ≤ m ∨ 3 ≤ n) : residueRest ai a b c x m n = 0 := by
  rcases h with hm | hn
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [Nat.add_comm 3 k]
    exact residueRest_left_vanishes ai a b c x hai k n
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [Nat.add_comm 3 k]
    exact residueRest_right_vanishes ai a b c x hai m k

theorem residueRest_outside_box (ai a b c x : ℂ) (hai : ai ≠ 0) (p : ℕ × ℕ)
    (hp : p ∉ restBox) : residueRest ai a b c x p.1 p.2 = 0 := by
  apply residueRest_support ai a b c x hai
  simpa only [restBox, mem_product, mem_range, not_and_or, not_lt] using hp

theorem residueRest_10 (ai a b c x : ℂ) (hai : ai ≠ 0) : residueRest ai a b c x 1 0 = restA ai a b c x :=
  (residueRest_linear ai a b c x hai).1

theorem residueRest_01 (ai a b c x : ℂ) (hai : ai ≠ 0) : residueRest ai a b c x 0 1 = restA ai a b c x :=
  (residueRest_linear ai a b c x hai).2

theorem residueRest_20 (ai a b c x : ℂ) (hai : ai ≠ 0) : residueRest ai a b c x 2 0 = restB ai a b c x := by
  rw [residueRest, regularizedCoeff_diagonal_axis_left, threeBack_two]
  rw [weightedResidue_second ai a b c x hai, weightedResidue_first ai a b c x hai,
    weightedResidue_base, coeff3_two]
  unfold restB
  ring

theorem residueRest_02 (ai a b c x : ℂ) (hai : ai ≠ 0) : residueRest ai a b c x 0 2 = restB ai a b c x := by
  rw [residueRest_symmetric, residueRest_20 ai a b c x hai]

theorem residueRest_11 (ai a b c x : ℂ) (hai : ai ≠ 0) : residueRest ai a b c x 1 1 = restC ai a b c x := by
  rw [residueRest, regularizedCoeff_one_one]
  norm_num only [Nat.reduceAdd]
  rw [weightedResidue_second ai a b c x hai, weightedResidue_first ai a b c x hai,
    weightedResidue_base, coeff3_two]
  unfold restC
  ring

theorem residueRest_21 (ai a b c x : ℂ) (hai : ai ≠ 0) : residueRest ai a b c x 2 1 = restD ai a b c x := by
  unfold residueRest regularizedCoeff extractLeft
  rw [threeBack_two]
  simp only [extractRight, threeBack_one, Nat.reduceAdd]
  rw [weightedResidue_recurrence ai a b c x hai 0]
  norm_num only [Nat.zero_add]
  rw [weightedResidue_second ai a b c x hai, weightedResidue_first ai a b c x hai,
    weightedResidue_base, coeff3_two]
  unfold restD
  ring

theorem residueRest_12 (ai a b c x : ℂ) (hai : ai ≠ 0) : residueRest ai a b c x 1 2 = restD ai a b c x := by
  rw [residueRest_symmetric, residueRest_21 ai a b c x hai]

theorem residueRest_22 (ai a b c x : ℂ) (hai : ai ≠ 0) : residueRest ai a b c x 2 2 = restE ai a b c x := by
  unfold residueRest regularizedCoeff extractLeft
  rw [threeBack_two]
  simp only [extractRight, threeBack_two, Nat.reduceAdd]
  rw [weightedResidue_recurrence ai a b c x hai 1, weightedResidue_recurrence ai a b c x hai 0]
  norm_num only [Nat.zero_add, Nat.reduceAdd]
  rw [weightedResidue_second ai a b c x hai, weightedResidue_first ai a b c x hai,
    weightedResidue_base, coeff3_two]
  unfold restE
  ring

theorem rest_series_summable (ai a b c x U V : ℂ) (hai : ai ≠ 0) :
    Summable (fun p : ℕ × ℕ => residueRest ai a b c x p.1 p.2*U^p.1*V^p.2) := by
  apply summable_of_ne_finset_zero (s := restBox)
  intro p hp
  rw [residueRest_outside_box ai a b c x hai p hp]
  simp

theorem rest_series_eq_polynomial (ai a b c x U V : ℂ) (hai : ai ≠ 0) :
    (∑' p : ℕ × ℕ, residueRest ai a b c x p.1 p.2*U^p.1*V^p.2) = restPolynomial ai a b c x U V := by
  rw [tsum_eq_sum (s := restBox) (fun p hp => by rw [residueRest_outside_box ai a b c x hai p hp]; simp)]
  simp only [restBox, Finset.sum_product, Finset.sum_range_succ, Finset.sum_range_zero,
    residueRest_constant, residueRest_10 ai a b c x hai, residueRest_01 ai a b c x hai,
    residueRest_20 ai a b c x hai, residueRest_02 ai a b c x hai,
    residueRest_11 ai a b c x hai, residueRest_21 ai a b c x hai,
    residueRest_12 ai a b c x hai, residueRest_22 ai a b c x hai]
  unfold restPolynomial
  ring

theorem restPolynomial_symmetric (ai a b c x U V : ℂ) :
    restPolynomial ai a b c x U V = restPolynomial ai a b c x V U := by
  unfold restPolynomial
  ring

@[simp] theorem restPolynomial_origin (ai a b c x : ℂ) : restPolynomial ai a b c x 0 0 = 1 := by
  simp [restPolynomial]

theorem restPolynomial_equal_shifts (x : ℂ) :
    restPolynomial 1 1 1 1 x 1 1 = (1-x)^4*(1+4*x+x^2) := by
  unfold restPolynomial restA restB restC restD restE
  ring

end SixthMoment.Source.NoDPLocalClosure
