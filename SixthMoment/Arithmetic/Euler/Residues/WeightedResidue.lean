import SixthMoment.Arithmetic.Euler.Residues.ResiduePolynomial

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

set_option linter.unusedSectionVars false
namespace SixthMoment.Source.NoDPResidues
open NoDPLocal

noncomputable def weightedResidue (ai a b c x : ℂ) (h : ℕ) : ℂ :=
  ai^h * residuePoly (x*a/ai) (x*b/ai) (x*c/ai) h

@[simp] theorem weightedResidue_base (ai a b c x : ℂ) : weightedResidue ai a b c x 0 = 1 := by
  simp [weightedResidue]

theorem weightedResidue_first (ai a b c x : ℂ) (hai : ai ≠ 0) :
    weightedResidue ai a b c x 1 =
      x*(a+b+c)-x^2/ai*(a*b+a*c+b*c)+x^3/ai^2*(a*b*c) := by
  rw [weightedResidue, residuePoly_first]
  field_simp [hai]

theorem weightedResidue_homogeneous (ai a b c x : ℂ) (hai : ai ≠ 0) (h : ℕ) :
    weightedResidue ai a b c x h = x^h * triNumerator a b c h (x/ai) := by
  unfold weightedResidue
  rw [show x*a/ai = (x/ai)*a by ring, show x*b/ai = (x/ai)*b by ring,
    show x*c/ai = (x/ai)*c by ring, residuePoly_scaled]
  rw [div_pow]
  field_simp [hai]

theorem weightedResidue_recurrence (ai a b c x : ℂ) (hai : ai ≠ 0) (h : ℕ) :
    weightedResidue ai a b c x (h+3) =
      x*(a+b+c)*weightedResidue ai a b c x (h+2) -
      x^2*(a*b+a*c+b*c)*weightedResidue ai a b c x (h+1) +
      x^3*a*b*c*weightedResidue ai a b c x h := by
  simp only [weightedResidue, residuePoly_recurrence, pow_add, pow_one]
  field_simp [hai]

theorem weightedResidue_swap_first (ai a b c x : ℂ) (h : ℕ) :
    weightedResidue ai a b c x h = weightedResidue ai b a c x h := by
  unfold weightedResidue
  rw [residuePoly_swap_first]

theorem weightedResidue_swap_last (ai a b c x : ℂ) (h : ℕ) :
    weightedResidue ai a b c x h = weightedResidue ai a c b x h := by
  unfold weightedResidue
  rw [residuePoly_swap_last]

theorem weighted_denominator_expand (ai a b c x : ℂ) :
    den3 (x*a/ai) (x*b/ai) (x*c/ai) 1 =
      1-(x/ai)*(a+b+c)+(x/ai)^2*(a*b+a*c+b*c)-(x/ai)^3*a*b*c := by
  rw [den3_expand]
  ring

@[simp] theorem weightedResidue_zero_parameter (ai a b c : ℂ) (h : ℕ) :
    weightedResidue ai a b c 0 (h+1) = 0 := by
  simp [weightedResidue]

theorem weightedResidue_equal_shifts (ai x : ℂ) (hai : ai ≠ 0) (h : ℕ) :
    weightedResidue ai ai ai ai x h = ai^h*principalCorrection x h := by
  simp only [weightedResidue, mul_div_cancel_right₀ x hai, residuePoly_eq_principalCorrection]

theorem weightedResidue_from_actual_tail (ai a b c x : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hx : ‖x‖ ≤ r) (ha : ‖x*a/ai‖ ≤ r) (hb : ‖x*b/ai‖ ≤ r)
    (hc : ‖x*c/ai‖ ≤ r) (hr1 : r < 1) (h : ℕ) :
    ai^h*residueLocal x (x*a/ai) (x*b/ai) (x*c/ai) h = weightedResidue ai a b c x h := by
  rw [residueLocal_eq_triNumerator x (x*a/ai) (x*b/ai) (x*c/ai) r hr hx ha hb hc hr1]
  rfl

theorem weightedResidue_first_error (ai a b c x : ℂ) (hai : ai ≠ 0) :
    weightedResidue ai a b c x 1-x*(a+b+c) =
      x^2/ai * (-(a*b+a*c+b*c)+(x/ai)*a*b*c) := by
  rw [weightedResidue_first ai a b c x hai]
  field_simp [hai]
  ring

theorem weightedResidue_second (ai a b c x : ℂ) (hai : ai ≠ 0) :
    weightedResidue ai a b c x 2 = x^2*coeff3 a b c 2 +
      x^3/ai * (-(a*b+a*c+b*c)*(a+b+c)+a*b*c) +
      x^4/ai^2 * (a*b*c*(a+b+c)) := by
  rw [weightedResidue_homogeneous ai a b c x hai 2]
  unfold triNumerator
  rw [triQ1_boundary a b c 0, triQ2_boundary a b c 1, coeff3_one]
  simp only [coeff3_zero]
  field_simp [hai]

end SixthMoment.Source.NoDPResidues
