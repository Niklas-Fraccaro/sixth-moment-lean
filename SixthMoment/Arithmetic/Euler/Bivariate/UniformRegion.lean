import SixthMoment.Arithmetic.Euler.Bivariate.RestNorms

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace SixthMoment.Source.NoDPLocalClosure
open NoDPLocal NoDPResidues
open scoped BigOperators

theorem normalized_root_bound (ai z x : ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hi : ‖ai⁻¹‖ ≤ M) (hz : ‖z‖ ≤ M) : ‖x*z/ai‖ ≤ ‖x‖*M^2 := by
  calc
    _ = ‖x‖*‖z‖*‖ai⁻¹‖ := by simp only [div_eq_mul_inv, norm_mul]
    _ ≤ ‖x‖*M*M := by gcongr
    _ = _ := by ring

theorem weightedResidue_uniform_bound (ai a b c x : ℂ) (M : ℝ) (hM : 1 ≤ M)
    (haiM : ‖ai‖ ≤ M) (hi : ‖ai⁻¹‖ ≤ M) (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (hc : ‖c‖ ≤ M)
    (hq : ‖x‖*M^2 ≤ 1) (h : ℕ) :
    ‖weightedResidue ai a b c x h‖ ≤ 12*quadraticHeight h*(‖x‖*M^3)^h := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have Hr : 0 ≤ ‖x‖*M^2 := by positivity
  have H := weightedResidue_bound ai a b c x (‖x‖*M^2) Hr
    (normalized_root_bound ai a x M hM0 hi ha) (normalized_root_bound ai b x M hM0 hi hb)
    (normalized_root_bound ai c x M hM0 hi hc) hq h
  apply H.trans
  have HH : 0 ≤ quadraticHeight h := by unfold quadraticHeight; positivity
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 12*quadraticHeight h)
  apply pow_le_pow_left₀ (by positivity)
  calc
    _ ≤ M*(‖x‖*M^2) := mul_le_mul_of_nonneg_right haiM Hr
    _ = _ := by ring

theorem quadratic_region_lt (x : ℂ) (M : ℝ) (hM : 1 ≤ M) (hq : ‖x‖*M^4 < 1) :
    ‖x‖*M^2 < 1 := by
  calc
    _ ≤ ‖x‖*M^4 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM (by omega : 2 ≤ 4)) (norm_nonneg x)
    _ < 1 := hq

theorem weightedResidue_double_uniform (ai a b c x U V : ℂ) (M : ℝ) (hM : 1 ≤ M)
    (haiM : ‖ai‖ ≤ M) (hi : ‖ai⁻¹‖ ≤ M) (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (hc : ‖c‖ ≤ M)
    (hq : ‖x‖*M^4 < 1) (hU : ‖U‖ ≤ M) (hV : ‖V‖ ≤ M) :
    Summable (diagonalTerm (weightedResidue ai a b c x) U V) := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hq2 := (quadratic_region_lt x M hM hq).le
  apply diagonal_summable _ 12 (‖x‖*M^3) (by norm_num) (by positivity)
    (fun n => by simpa only [quadraticHeight] using weightedResidue_uniform_bound ai a b c x M hM haiM hi ha hb hc hq2 n)
  · calc
      _ ≤ (‖x‖*M^3)*M := mul_le_mul_of_nonneg_left hU (by positivity)
      _ = ‖x‖*M^4 := by ring
      _ < 1 := hq
  · calc
      _ ≤ (‖x‖*M^3)*M := mul_le_mul_of_nonneg_left hV (by positivity)
      _ = ‖x‖*M^4 := by ring
      _ < 1 := hq

theorem weightedResidue_double_absolute (ai a b c x U V : ℂ) (M : ℝ) (hM : 1 ≤ M)
    (haiM : ‖ai‖ ≤ M) (hi : ‖ai⁻¹‖ ≤ M) (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (hc : ‖c‖ ≤ M)
    (hq : ‖x‖*M^4 < 1) (hU : ‖U‖ ≤ M) (hV : ‖V‖ ≤ M) :
    Summable (fun p : ℕ × ℕ => ‖diagonalTerm (weightedResidue ai a b c x) U V p‖) :=
  (weightedResidue_double_uniform ai a b c x U V M hM haiM hi ha hb hc hq hU hV).norm

theorem local_denominator_ne_zero (a b c x U : ℂ) (M : ℝ) (hM : 1 ≤ M)
    (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (hc : ‖c‖ ≤ M)
    (hq : ‖x‖*M^4 < 1) (hU : ‖U‖ ≤ M) : den3 (x*a) (x*b) (x*c) U ≠ 0 := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  apply den3_ne_zero (x*a) (x*b) (x*c) U (‖x‖*M)
  · rw [norm_mul]; gcongr
  · rw [norm_mul]; gcongr
  · rw [norm_mul]; gcongr
  · calc
      _ ≤ (‖x‖*M)*M := mul_le_mul_of_nonneg_left hU (by positivity)
      _ = ‖x‖*M^2 := by ring
      _ < 1 := quadratic_region_lt x M hM hq

theorem restPolynomial_factorization_uniform (ai a b c x U V : ℂ) (hai : ai ≠ 0)
    (M : ℝ) (hM : 1 ≤ M) (haiM : ‖ai‖ ≤ M) (hi : ‖ai⁻¹‖ ≤ M)
    (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (hc : ‖c‖ ≤ M)
    (hq : ‖x‖*M^4 < 1) (hU : ‖U‖ ≤ M) (hV : ‖V‖ ≤ M) :
    restPolynomial ai a b c x U V = den3 (x*a) (x*b) (x*c) U*den3 (x*a) (x*b) (x*c) V*
      doubleSeries (weightedResidue ai a b c x) U V :=
  restPolynomial_factorization_of_summable ai a b c x U V hai
    (weightedResidue_double_uniform ai a b c x U V M hM haiM hi ha hb hc hq hU hV)

theorem doubleSeries_rational_uniform (ai a b c x U V : ℂ) (hai : ai ≠ 0)
    (M : ℝ) (hM : 1 ≤ M) (haiM : ‖ai‖ ≤ M) (hi : ‖ai⁻¹‖ ≤ M)
    (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (hc : ‖c‖ ≤ M)
    (hq : ‖x‖*M^4 < 1) (hU : ‖U‖ ≤ M) (hV : ‖V‖ ≤ M) :
    doubleSeries (weightedResidue ai a b c x) U V =
      restPolynomial ai a b c x U V/(den3 (x*a) (x*b) (x*c) U*den3 (x*a) (x*b) (x*c) V) := by
  apply (eq_div_iff (mul_ne_zero (local_denominator_ne_zero a b c x U M hM ha hb hc hq hU)
    (local_denominator_ne_zero a b c x V M hM ha hb hc hq hV))).2
  simpa only [mul_comm] using (restPolynomial_factorization_uniform ai a b c x U V hai M hM haiM hi ha hb hc hq hU hV).symm

theorem actual_residue_tail_uniform (ai a b c x : ℂ) (M : ℝ) (hM : 1 ≤ M)
    (hi : ‖ai⁻¹‖ ≤ M) (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (hc : ‖c‖ ≤ M)
    (hq : ‖x‖*M^4 < 1) (h : ℕ) :
    ai^h*residueLocal x (x*a/ai) (x*b/ai) (x*c/ai) h = weightedResidue ai a b c x h := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  apply weightedResidue_from_actual_tail ai a b c x (‖x‖*M^2) (by positivity)
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ hM : 1 ≤ M^2) (norm_nonneg x)
  · exact normalized_root_bound ai a x M hM0 hi ha
  · exact normalized_root_bound ai b x M hM0 hi hb
  · exact normalized_root_bound ai c x M hM0 hi hc
  · exact quadratic_region_lt x M hM hq

@[fun_prop] theorem restPolynomial_entire_left (ai a b c x V : ℂ) :
    Differentiable ℂ (fun U => restPolynomial ai a b c x U V) := by
  unfold restPolynomial
  fun_prop

@[fun_prop] theorem restPolynomial_entire_right (ai a b c x U : ℂ) :
    Differentiable ℂ (fun V => restPolynomial ai a b c x U V) := by
  unfold restPolynomial
  fun_prop

theorem restPolynomial_error_uniform (ai a b c x U V : ℂ) (hai : ai ≠ 0)
    (M : ℝ) (hM : 1 ≤ M) (hi : ‖ai⁻¹‖ ≤ M) (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (hc : ‖c‖ ≤ M)
    (hq : ‖x‖*M^2 ≤ 1) (hU : ‖U‖ ≤ M) (hV : ‖V‖ ≤ M) :
    ‖restPolynomial ai a b c x U V-1‖ ≤ 35*‖x‖^2*M^4 :=
  (restPolynomial_error_le_mass ai a b c x U V hai M (le_trans zero_le_one hM) hU hV).trans
    (errorMass_bound ai a b c x M (le_trans zero_le_one hM) hi ha hb hc hai hq)

end SixthMoment.Source.NoDPLocalClosure
