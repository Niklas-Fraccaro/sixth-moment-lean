import Sechstmoment.Arithmetic.Euler.Bivariate.UniformRegion

/-! Bridge to the unscaled prime-power tail appearing in PDF (6.1). -/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Sechstmoment.Source.NoDPLocalClosure
open NoDPLocal NoDPResidues
open scoped BigOperators

noncomputable def originalPoleTail (ai a b c t q : ℂ) (h : ℕ) : ℂ :=
  denom ai a b c t * (t^h*localSeries ai a b c t h -
    if h = 0 then 0 else q*t^(h-1)*coeff4 ai a b c (h-1))

theorem localSeries_scaled_unit (ai a b c t : ℂ) (h : ℕ) :
    t^h*localSeries ai a b c t h = localSeries (t*ai) (t*a) (t*b) (t*c) 1 h := by
  unfold localSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [coeff4_scaled, pow_add]
  simp only [one_pow, mul_one]
  ring

theorem originalPoleTail_eq_scaled (ai a b c x : ℂ) (hai : ai ≠ 0) (h : ℕ) :
    originalPoleTail ai a b c (x/ai) (x/(1-x)) h =
      residueLocal x (x*a/ai) (x*b/ai) (x*c/ai) h := by
  have H0 : (x/ai)*ai = x := div_mul_cancel₀ x hai
  have Ha : (x/ai)*a = x*a/ai := by ring
  have Hb : (x/ai)*b = x*b/ai := by ring
  have Hc : (x/ai)*c = x*c/ai := by ring
  have HD : denom ai a b c (x/ai) = denom x (x*a/ai) (x*b/ai) (x*c/ai) 1 := by
    simpa only [H0, Ha, Hb, Hc, mul_one] using (denom_scaled ai a b c (x/ai) 1).symm
  have HS := localSeries_scaled_unit ai a b c (x/ai) h
  rw [H0, Ha, Hb, Hc] at HS
  have HC := coeff4_scaled ai a b c (x/ai) (h-1)
  rw [H0, Ha, Hb, Hc] at HC
  unfold originalPoleTail residueLocal
  rw [HD, HS]
  by_cases hh : h = 0
  · simp only [hh, ite_true]
  · simp only [hh, ite_false]
    rw [HC]
    ring

theorem original_tail_absolute (ai a b c x : ℂ) (M : ℝ) (hM : 1 ≤ M)
    (haiM : ‖ai‖ ≤ M) (hi : ‖ai⁻¹‖ ≤ M) (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (hc : ‖c‖ ≤ M)
    (hq : ‖x‖*M^4 < 1) (h : ℕ) :
    Summable (fun n => ‖coeff4 ai a b c (h+n)*(x/ai)^(h+n)‖) := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have ht : M*‖x/ai‖ < 1 := by
    calc
      _ = M*(‖x‖*‖ai⁻¹‖) := by simp only [div_eq_mul_inv, norm_mul]
      _ ≤ M*(‖x‖*M) := by gcongr
      _ = ‖x‖*M^2 := by ring
      _ < 1 := quadratic_region_lt x M hM hq
  have H := ((coeff4_tail_summable ai a b c (x/ai) M hM0 haiM ha hb hc ht h).mul_left ((x/ai)^h)).norm
  convert H using 1
  funext n
  congr 1
  rw [pow_add]
  ring

theorem originalPoleTail_uniform (ai a b c x : ℂ) (hai : ai ≠ 0) (M : ℝ) (hM : 1 ≤ M)
    (hi : ‖ai⁻¹‖ ≤ M) (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (hc : ‖c‖ ≤ M)
    (hq : ‖x‖*M^4 < 1) (h : ℕ) :
    ai^h*originalPoleTail ai a b c (x/ai) (x/(1-x)) h = weightedResidue ai a b c x h := by
  rw [originalPoleTail_eq_scaled ai a b c x hai]
  exact actual_residue_tail_uniform ai a b c x M hM hi ha hb hc hq h

end Sechstmoment.Source.NoDPLocalClosure
