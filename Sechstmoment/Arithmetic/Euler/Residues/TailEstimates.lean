import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Sechstmoment.Arithmetic.Euler.Residues.BivariateCoefficients

/-! Absolute convergence and certified finite truncations of the residue series. -/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Sechstmoment.Source.NoDPResidues
open NoDPLocal Finset Filter
open scoped BigOperators Topology

theorem quadratic_geometric_summable (q B : ℝ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => ((n:ℝ)+B)^2*q^n) := by
  have h0 := summable_geometric_of_norm_lt_one hq
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hq
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hq
  convert (h2.add (h1.mul_left (2*B))).add (h0.mul_left (B^2)) using 1
  ext n
  simp only [pow_one]
  ring

theorem residue_weighted_summable (a b c t : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (hc : ‖c‖ ≤ r) (hr1 : r ≤ 1)
    (ht : r*‖t‖ < 1) : Summable (fun n : ℕ => residuePoly a b c n*t^n) := by
  have hq : ‖r*‖t‖‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr] using ht
  apply ((quadratic_geometric_summable (r*‖t‖) 4 hq).mul_left 12).of_norm_bounded
  intro n
  calc
    ‖residuePoly a b c n*t^n‖ = ‖residuePoly a b c n‖*‖t‖^n := by simp only [norm_mul, norm_pow]
    _ ≤ (12*quadraticHeight n*r^n)*‖t‖^n := mul_le_mul_of_nonneg_right (residuePoly_bound a b c r hr ha hb hc hr1 n) (by positivity)
    _ = _ := by unfold quadraticHeight; rw [mul_pow]; ring

theorem weightedResidue_summable (ai a b c x t : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ha : ‖x*a/ai‖ ≤ r) (hb : ‖x*b/ai‖ ≤ r) (hc : ‖x*c/ai‖ ≤ r) (hr1 : r ≤ 1)
    (ht : (‖ai‖*r)*‖t‖ < 1) : Summable (fun n : ℕ => weightedResidue ai a b c x n*t^n) := by
  have hq : ‖(‖ai‖*r)*‖t‖‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hr] using ht
  apply ((quadratic_geometric_summable ((‖ai‖*r)*‖t‖) 4 hq).mul_left 12).of_norm_bounded
  intro n
  calc
    ‖weightedResidue ai a b c x n*t^n‖ = ‖weightedResidue ai a b c x n‖*‖t‖^n := by simp only [norm_mul, norm_pow]
    _ ≤ (12*quadraticHeight n*(‖ai‖*r)^n)*‖t‖^n :=
      mul_le_mul_of_nonneg_right (weightedResidue_bound ai a b c x r hr ha hb hc hr1 n) (by positivity)
    _ = _ := by unfold quadraticHeight; rw [mul_pow]; ring

theorem residue_weighted_norm_summable (a b c t : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (hc : ‖c‖ ≤ r) (hr1 : r ≤ 1) (ht : r*‖t‖ < 1) :
    Summable (fun n : ℕ => ‖residuePoly a b c n*t^n‖) :=
  (residue_weighted_summable a b c t r hr ha hb hc hr1 ht).norm

theorem weightedResidue_norm_summable (ai a b c x t : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ha : ‖x*a/ai‖ ≤ r) (hb : ‖x*b/ai‖ ≤ r) (hc : ‖x*c/ai‖ ≤ r) (hr1 : r ≤ 1)
    (ht : (‖ai‖*r)*‖t‖ < 1) : Summable (fun n : ℕ => ‖weightedResidue ai a b c x n*t^n‖) :=
  (weightedResidue_summable ai a b c x t r hr ha hb hc hr1 ht).norm

theorem series_prefix_tail (f : ℕ → ℂ) (t : ℂ) (hs : Summable (fun n => f n*t^n)) (N : ℕ) :
    (∑' n : ℕ, f n*t^n) = (∑ n ∈ range N, f n*t^n)+t^N*(∑' k : ℕ, f (N+k)*t^k) := by
  rw [← hs.sum_add_tsum_nat_add N]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [Nat.add_comm k N, pow_add]
  ring

theorem truncation_norm_bound (f : ℕ → ℂ) (hs : Summable f) (N : ℕ) :
    ‖(∑' n : ℕ, f n)-(∑ n ∈ range N, f n)‖ ≤ ∑' k : ℕ, ‖f (k+N)‖ := by
  have H := hs.sum_add_tsum_nat_add N
  have E : (∑' n : ℕ, f n)-(∑ n ∈ range N, f n) = ∑' k : ℕ, f (k+N) := by
    linear_combination -H
  rw [E]
  exact norm_tsum_le_tsum_norm ((hs.comp_injective (fun a b h => Nat.add_right_cancel h)).norm)

theorem residue_partial_sums_tendsto (a b c t : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (hc : ‖c‖ ≤ r) (hr1 : r ≤ 1) (ht : r*‖t‖ < 1) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, residuePoly a b c n*t^n) atTop
      (𝓝 (∑' n : ℕ, residuePoly a b c n*t^n)) :=
  (residue_weighted_summable a b c t r hr ha hb hc hr1 ht).hasSum.tendsto_sum_nat

theorem weightedResidue_partial_sums_tendsto (ai a b c x t : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ha : ‖x*a/ai‖ ≤ r) (hb : ‖x*b/ai‖ ≤ r) (hc : ‖x*c/ai‖ ≤ r) (hr1 : r ≤ 1)
    (ht : (‖ai‖*r)*‖t‖ < 1) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, weightedResidue ai a b c x n*t^n) atTop
      (𝓝 (∑' n : ℕ, weightedResidue ai a b c x n*t^n)) :=
  (weightedResidue_summable ai a b c x t r hr ha hb hc hr1 ht).hasSum.tendsto_sum_nat

theorem weightedResidue_truncation_error_tendsto (ai a b c x t : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ha : ‖x*a/ai‖ ≤ r) (hb : ‖x*b/ai‖ ≤ r) (hc : ‖x*c/ai‖ ≤ r) (hr1 : r ≤ 1)
    (ht : (‖ai‖*r)*‖t‖ < 1) :
    Tendsto (fun N : ℕ => (∑' n : ℕ, weightedResidue ai a b c x n*t^n)-
      ∑ n ∈ range N, weightedResidue ai a b c x n*t^n) atTop (𝓝 0) := by
  have H := weightedResidue_partial_sums_tendsto ai a b c x t r hr ha hb hc hr1 ht
  simpa only [sub_self] using ((tendsto_const_nhds (x := (∑' n : ℕ, weightedResidue ai a b c x n*t^n))).sub H)

end Sechstmoment.Source.NoDPResidues
