import Sechstmoment.Arithmetic.Euler.Residues.ThreeSeries

/-!
# Exact local cancellation at a residue pole (PDF §6.1)
The correction is defined from the actual four-root infinite tail. Its evaluation
loses the distinguished root and has no denominator in that root.
-/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

set_option linter.unusedSectionVars false
namespace Sechstmoment.Source.NoDPResidues
open NoDPLocal

noncomputable def residueLocal (x a b c : ℂ) (h : ℕ) : ℂ :=
  denom x a b c 1 * (localSeries x a b c 1 h -
    (if h = 0 then 0 else x*coeff4 x a b c (h-1)/(1-x)))

section Series
variable (x a b c t : ℂ) (r : ℝ) (hr : 0 ≤ r)
  (hx : ‖x‖ ≤ r) (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (hc : ‖c‖ ≤ r)
  (ht : r*‖t‖ < 1)
include hr hx ha hb hc ht

theorem series_remove_root_shift (h : ℕ) :
    triSeries a b c t (h+1) = localSeries x a b c t (h+1) - x*localSeries x a b c t h := by
  have Hs (k : ℕ) := (coeff4_tail_summable x a b c t r hr hx ha hb hc ht k).hasSum
  apply HasSum.tsum_eq
  convert (Hs (h+1)).sub ((Hs h).mul_left x) using 1
  · ext n
    rw [show h+1+n=(h+n)+1 by omega, coeff4_succ]
    ring
  · rfl

theorem series_remove_root_base :
    triSeries a b c t 0 = (1-x*t)*localSeries x a b c t 0 := by
  have H := series_remove_root_shift x a b c t r hr hx ha hb hc ht 0
  have H3 := triSeries_shift a b c t r hr ha hb hc ht 0
  have H4 := localSeries_shift x a b c t r hr hx ha hb hc ht 0
  simp only [coeff3_zero, coeff4_zero] at H3 H4
  linear_combination H3 + t*H - H4

theorem series_remove_root_boundary (h : ℕ) :
    triSeries a b c t (h+1) =
      (1-x*t)*localSeries x a b c t (h+1) - x*coeff4 x a b c h := by
  have H := series_remove_root_shift x a b c t r hr hx ha hb hc ht h
  have H4 := localSeries_shift x a b c t r hr hx ha hb hc ht h
  linear_combination H - x*H4

theorem corrected_series_identity (h : ℕ) :
    denom x a b c t *
        (localSeries x a b c t (h+1) - x*coeff4 x a b c h/(1-x*t)) =
      triNumerator a b c (h+1) t := by
  have H := series_remove_root_boundary x a b c t r hr hx ha hb hc ht h
  have H3 := three_series_factorization a b c t r hr ha hb hc ht (h+1)
  have hn := one_sub_mul_ne_zero x t r hx ht
  calc
    _ = den3 a b c t*((1-x*t)*localSeries x a b c t (h+1)-x*coeff4 x a b c h) := by
      rw [denom_split_root]
      field_simp [hn]
    _ = den3 a b c t*triSeries a b c t (h+1) := by rw [← H]
    _ = _ := H3

end Series

theorem numerator_residue_cancel (x a b c t : ℂ) (h : ℕ) :
    numerator x a b c (h+1) t - x*coeff4 x a b c h*den3 a b c t =
      triNumerator a b c (h+1) t := by
  unfold numerator q0 q1 q2 q3 triNumerator triQ1 triQ2
  simp only [Nat.add_assoc, coeff4_succ]
  rw [den3_expand]
  simp only [e1, e2, e3]
  simp only [coeff3_recurrence]
  ring

section UnitParameter
variable (x a b c : ℂ) (r : ℝ) (hr : 0 ≤ r)
  (hx : ‖x‖ ≤ r) (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (hc : ‖c‖ ≤ r)
  (hr1 : r < 1)
include hr hx ha hb hc hr1

@[simp] theorem residueLocal_base : residueLocal x a b c 0 = 1 := by
  have ht : r*‖(1:ℂ)‖ < 1 := by simpa using hr1
  have hd := denom_norm_region_ne_zero x a b c 1 r hx ha hb hc ht
  rw [residueLocal, ite_eq_left rfl, sub_zero,
    localSeries_base x a b c 1 r hr hx ha hb hc ht]
  exact mul_inv_cancel₀ hd

theorem residueLocal_succ_evaluation (h : ℕ) :
    residueLocal x a b c (h+1) = triNumerator a b c (h+1) 1 := by
  have ht : r*‖(1:ℂ)‖ < 1 := by simpa using hr1
  simpa [residueLocal] using corrected_series_identity x a b c 1 r hr hx ha hb hc ht h

theorem residueLocal_eq_triNumerator (h : ℕ) :
    residueLocal x a b c h = triNumerator a b c h 1 := by
  cases h with
  | zero => rw [residueLocal_base x a b c r hr hx ha hb hc hr1, triNumerator_base]
  | succ h => exact residueLocal_succ_evaluation x a b c r hr hx ha hb hc hr1 h

theorem residueLocal_eq_tail (h : ℕ) :
    residueLocal x a b c h = den3 a b c 1 * triSeries a b c 1 h := by
  rw [residueLocal_eq_triNumerator x a b c r hr hx ha hb hc hr1]
  exact (three_series_factorization a b c 1 r hr ha hb hc (by simpa using hr1) h).symm

theorem residueLocal_independent_root (y : ℂ) (hy : ‖y‖ ≤ r) (h : ℕ) :
    residueLocal x a b c h = residueLocal y a b c h := by
  rw [residueLocal_eq_triNumerator x a b c r hr hx ha hb hc hr1,
    residueLocal_eq_triNumerator y a b c r hr hy ha hb hc hr1]

end UnitParameter
end Sechstmoment.Source.NoDPResidues
