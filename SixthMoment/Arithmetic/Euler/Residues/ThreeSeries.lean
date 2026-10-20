import SixthMoment.Arithmetic.Euler.Local.Rational.Factorization
import SixthMoment.Arithmetic.Euler.Residues.ThreeNumerator

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

set_option linter.unusedSectionVars false
namespace SixthMoment.Source.NoDPResidues
open NoDPLocal
open scoped BigOperators
noncomputable def triSeries (a b c t : ℂ) (h : ℕ) : ℂ :=
  ∑' n : ℕ, coeff3 a b c (h+n)*t^n

theorem triSeries_eq_localSeries (a b c t : ℂ) (h : ℕ) :
    triSeries a b c t h = localSeries 0 a b c t h := by
  simp [triSeries, localSeries]

theorem three_tail_summable (a b c t : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (hc : ‖c‖ ≤ r) (ht : r*‖t‖ < 1) (h : ℕ) :
    Summable (fun n : ℕ => coeff3 a b c (h+n)*t^n) := by
  simpa only [coeff4_first_zero] using
    coeff4_tail_summable 0 a b c t r hr (by simpa using hr) ha hb hc ht h

@[simp] theorem triSeries_at_zero (a b c : ℂ) (h : ℕ) :
    triSeries a b c 0 h = coeff3 a b c h := by
  rw [triSeries_eq_localSeries, localSeries_at_zero, coeff4_first_zero]

theorem triSeries_shift (a b c t : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (hc : ‖c‖ ≤ r) (ht : r*‖t‖ < 1) (h : ℕ) :
    triSeries a b c t h = coeff3 a b c h + t*triSeries a b c t (h+1) := by
  simpa only [← triSeries_eq_localSeries, coeff4_first_zero] using
    localSeries_shift 0 a b c t r hr (by simpa using hr) ha hb hc ht h

theorem den3_ne_zero (a b c t : ℂ) (r : ℝ)
    (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (hc : ‖c‖ ≤ r) (ht : r*‖t‖ < 1) :
    den3 a b c t ≠ 0 := by
  unfold den3
  exact mul_ne_zero (mul_ne_zero (one_sub_mul_ne_zero a t r ha ht)
    (one_sub_mul_ne_zero b t r hb ht)) (one_sub_mul_ne_zero c t r hc ht)

theorem three_series_factorization (a b c t : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (hc : ‖c‖ ≤ r) (ht : r*‖t‖ < 1) (h : ℕ) :
    den3 a b c t * triSeries a b c t h = triNumerator a b c h t := by
  have H := local_series_factorization 0 a b c t r hr (by simpa using hr) ha hb hc ht h
  simpa [denom_split_root, numerator_drop_zero_root, ← triSeries_eq_localSeries] using H

theorem triSeries_rational (a b c t : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (hc : ‖c‖ ≤ r) (ht : r*‖t‖ < 1) (h : ℕ) :
    triSeries a b c t h = triNumerator a b c h t / den3 a b c t := by
  apply (eq_div_iff (den3_ne_zero a b c t r ha hb hc ht)).2
  simpa [mul_comm] using three_series_factorization a b c t r hr ha hb hc ht h

theorem triSeries_base (a b c t : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (hc : ‖c‖ ≤ r) (ht : r*‖t‖ < 1) :
    triSeries a b c t 0 = (den3 a b c t)⁻¹ := by
  rw [triSeries_rational a b c t r hr ha hb hc ht 0, triNumerator_base, one_div]

theorem triSeries_swap_first (a b c t : ℂ) (h : ℕ) :
    triSeries a b c t h = triSeries b a c t h := by
  unfold triSeries
  apply tsum_congr
  intro n
  rw [coeff3_swap_first]

theorem triSeries_swap_last (a b c t : ℂ) (h : ℕ) :
    triSeries a b c t h = triSeries a c b t h := by
  unfold triSeries
  apply tsum_congr
  intro n
  rw [coeff3_swap_last]

end SixthMoment.Source.NoDPResidues
