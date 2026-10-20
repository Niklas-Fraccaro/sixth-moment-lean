import SixthMoment.Arithmetic.Euler.Bivariate.SeriesOperators

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
namespace SixthMoment.Source.NoDPLocalClosure
open NoDPLocal NoDPResidues Finset
open scoped BigOperators

noncomputable def errorCoeff (ai a b c x : ℂ) (m n : ℕ) : ℂ :=
  residueRest ai a b c x m n - if m = 0 ∧ n = 0 then 1 else 0
noncomputable def errorMass (ai a b c x : ℂ) (M : ℝ) : ℝ :=
  ∑' p : ℕ × ℕ, ‖errorCoeff ai a b c x p.1 p.2‖*M^(p.1+p.2)

theorem errorCoeff_outside_box (ai a b c x : ℂ) (hai : ai ≠ 0) (p : ℕ × ℕ)
    (hp : p ∉ restBox) : errorCoeff ai a b c x p.1 p.2 = 0 := by
  have h00 : ¬ (p.1 = 0 ∧ p.2 = 0) := by
    rintro ⟨h1,h2⟩
    apply hp
    simp [restBox, h1, h2]
  simp only [errorCoeff, residueRest_outside_box ai a b c x hai p hp, ite_eq_right h00, sub_zero]

theorem error_mass_summable (ai a b c x : ℂ) (hai : ai ≠ 0) (M : ℝ) :
    Summable (fun p : ℕ × ℕ => ‖errorCoeff ai a b c x p.1 p.2‖*M^(p.1+p.2)) := by
  apply summable_of_ne_finset_zero (s := restBox)
  intro p hp
  rw [errorCoeff_outside_box ai a b c x hai p hp]
  simp

theorem errorMass_explicit (ai a b c x : ℂ) (hai : ai ≠ 0) (M : ℝ) :
    errorMass ai a b c x M =
      2*‖restA ai a b c x‖*M+2*‖restB ai a b c x‖*M^2+‖restC ai a b c x‖*M^2+
      2*‖restD ai a b c x‖*M^3+‖restE ai a b c x‖*M^4 := by
  unfold errorMass
  rw [tsum_eq_sum (s := restBox) (fun p hp => by rw [errorCoeff_outside_box ai a b c x hai p hp]; simp)]
  norm_num [restBox, Finset.sum_product, Finset.sum_range_succ, errorCoeff,
    residueRest_10 ai a b c x hai, residueRest_01 ai a b c x hai,
    residueRest_20 ai a b c x hai, residueRest_02 ai a b c x hai,
    residueRest_11 ai a b c x hai, residueRest_21 ai a b c x hai,
    residueRest_12 ai a b c x hai, residueRest_22 ai a b c x hai]
  ring

section Bounds
variable (ai a b c x : ℂ) (M : ℝ) (hM : 0 ≤ M)
  (hi : ‖ai⁻¹‖ ≤ M) (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (hc : ‖c‖ ≤ M)
include hM hi ha hb hc

theorem restA_weighted_bound :
    ‖restA ai a b c x‖*M ≤ 3*(‖x‖*M^2)^2+(‖x‖*M^2)^3 := by
  have H2 := three_e2_bound a b c M hM ha hb hc
  have H3 := three_product_bound a b c M hM ha hb hc
  calc
    _ ≤ (‖x‖^2*‖ai⁻¹‖*‖a*b+a*c+b*c‖+‖x‖^3*‖ai⁻¹‖^2*‖a*b*c‖)*M := by
      apply mul_le_mul_of_nonneg_right _ hM
      change ‖-x^2/ai*(a*b+a*c+b*c)+x^3/ai^2*(a*b*c)‖ ≤ _
      calc
        _ ≤ ‖-x^2/ai*(a*b+a*c+b*c)‖+‖x^3/ai^2*(a*b*c)‖ := norm_add_le _ _
        _ = _ := by simp only [div_eq_mul_inv, inv_pow, norm_mul, norm_pow, norm_neg, norm_inv]
    _ ≤ (‖x‖^2*M*(3*M^2)+‖x‖^3*M^2*M^3)*M := by gcongr
    _ = _ := by ring

theorem restB_weighted_bound : ‖restB ai a b c x‖*M^2 ≤ (‖x‖*M^2)^3 := by
  have H3 := three_product_bound a b c M hM ha hb hc
  calc
    _ = ‖x‖^3*‖ai⁻¹‖*‖a*b*c‖*M^2 := by simp [restB, div_eq_mul_inv, norm_mul, norm_pow]
    _ ≤ ‖x‖^3*M*M^3*M^2 := by gcongr
    _ = _ := by ring

omit hi in
theorem mixed_symmetric_bound : ‖(a+b+c)*(a*b+a*c+b*c)+a*b*c‖ ≤ 10*M^3 := by
  have H1 := three_e1_bound a b c M hM ha hb hc
  have H2 := three_e2_bound a b c M hM ha hb hc
  have H3 := three_product_bound a b c M hM ha hb hc
  calc
    _ ≤ ‖a+b+c‖*‖a*b+a*c+b*c‖+‖a*b*c‖ := by simpa only [norm_mul] using norm_add_le ((a+b+c)*(a*b+a*c+b*c)) (a*b*c)
    _ ≤ (3*M)*(3*M^2)+M^3 := by gcongr
    _ = _ := by ring

theorem restC_weighted_bound :
    ‖restC ai a b c x‖*M^2 ≤ 3*(‖x‖*M^2)^2+10*(‖x‖*M^2)^3+3*(‖x‖*M^2)^4 := by
  have H1 := three_e1_bound a b c M hM ha hb hc
  have H2 := three_e2_bound a b c M hM ha hb hc
  have H3 := three_product_bound a b c M hM ha hb hc
  have H4 := mixed_symmetric_bound a b c M hM ha hb hc
  have HT : ‖restC ai a b c x‖ ≤ ‖x‖^2*‖a*b+a*c+b*c‖+
      ‖x‖^3*‖ai⁻¹‖*‖(a+b+c)*(a*b+a*c+b*c)+a*b*c‖+
      ‖x‖^4*‖ai⁻¹‖^2*(‖a+b+c‖*‖a*b*c‖) := by
    unfold restC
    calc
      _ ≤ ‖-x^2*(a*b+a*c+b*c)+x^3/ai*((a+b+c)*(a*b+a*c+b*c)+a*b*c)‖+
        ‖x^4/ai^2*((a+b+c)*a*b*c)‖ := norm_sub_le _ _
      _ ≤ (‖-x^2*(a*b+a*c+b*c)‖+‖x^3/ai*((a+b+c)*(a*b+a*c+b*c)+a*b*c)‖)+
        ‖x^4/ai^2*((a+b+c)*a*b*c)‖ := add_le_add (norm_add_le _ _) le_rfl
      _ = _ := by simp only [div_eq_mul_inv, inv_pow, norm_mul, norm_pow, norm_neg, norm_inv]; ring
  calc
    _ ≤ (‖x‖^2*‖a*b+a*c+b*c‖+‖x‖^3*‖ai⁻¹‖*‖(a+b+c)*(a*b+a*c+b*c)+a*b*c‖+
      ‖x‖^4*‖ai⁻¹‖^2*(‖a+b+c‖*‖a*b*c‖))*M^2 := mul_le_mul_of_nonneg_right HT (sq_nonneg M)
    _ ≤ (‖x‖^2*(3*M^2)+‖x‖^3*M*(10*M^3)+‖x‖^4*M^2*((3*M)*M^3))*M^2 := by gcongr
    _ = _ := by ring

theorem restD_weighted_bound : ‖restD ai a b c x‖*M^3 ≤ (‖x‖*M^2)^3+3*(‖x‖*M^2)^4 := by
  have H1 := three_e1_bound a b c M hM ha hb hc
  have H3 := three_product_bound a b c M hM ha hb hc
  calc
    _ ≤ (‖x‖^3*‖a*b*c‖+‖x‖^4*‖ai⁻¹‖*(‖a+b+c‖*‖a*b*c‖))*M^3 := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hM 3)
      change ‖x^3*(a*b*c)-x^4/ai*((a+b+c)*a*b*c)‖ ≤ _
      calc
        _ ≤ ‖x^3*(a*b*c)‖+‖x^4/ai*((a+b+c)*a*b*c)‖ := norm_sub_le _ _
        _ = _ := by simp only [div_eq_mul_inv, norm_mul, norm_pow, norm_inv]; ring
    _ ≤ (‖x‖^3*M^3+‖x‖^4*M*((3*M)*M^3))*M^3 := by gcongr
    _ = _ := by ring

theorem restE_weighted_bound : ‖restE ai a b c x‖*M^4 ≤ (‖x‖*M^2)^6 := by
  have H3 := three_product_bound a b c M hM ha hb hc
  calc
    _ = ‖x‖^6*‖ai⁻¹‖^2*‖a*b*c‖^2*M^4 := by simp [restE, div_eq_mul_inv, inv_pow, norm_mul, norm_pow]
    _ ≤ ‖x‖^6*M^2*(M^3)^2*M^4 := by gcongr
    _ = _ := by ring

theorem errorMass_bound_polynomial (hai : ai ≠ 0) :
    errorMass ai a b c x M ≤
      9*(‖x‖*M^2)^2+16*(‖x‖*M^2)^3+9*(‖x‖*M^2)^4+(‖x‖*M^2)^6 := by
  rw [errorMass_explicit ai a b c x hai]
  have HA := restA_weighted_bound ai a b c x M hM hi ha hb hc
  have HB := restB_weighted_bound ai a b c x M hM hi ha hb hc
  have HC := restC_weighted_bound ai a b c x M hM hi ha hb hc
  have HD := restD_weighted_bound ai a b c x M hM hi ha hb hc
  have HE := restE_weighted_bound ai a b c x M hM hi ha hb hc
  linarith

theorem errorMass_bound (hai : ai ≠ 0) (hq : ‖x‖*M^2 ≤ 1) :
    errorMass ai a b c x M ≤ 35*‖x‖^2*M^4 := by
  have H := errorMass_bound_polynomial ai a b c x M hM hi ha hb hc hai
  have hq0 : 0 ≤ ‖x‖*M^2 := by positivity
  have H3 : (‖x‖*M^2)^3 ≤ (‖x‖*M^2)^2 := pow_le_pow_of_le_one hq0 hq (by omega)
  have H4 : (‖x‖*M^2)^4 ≤ (‖x‖*M^2)^2 := pow_le_pow_of_le_one hq0 hq (by omega)
  have H6 : (‖x‖*M^2)^6 ≤ (‖x‖*M^2)^2 := pow_le_pow_of_le_one hq0 hq (by omega)
  nlinarith

end Bounds

theorem error_series_summable (ai a b c x U V : ℂ) (hai : ai ≠ 0) :
    Summable (fun p : ℕ × ℕ => errorCoeff ai a b c x p.1 p.2*U^p.1*V^p.2) := by
  apply summable_of_ne_finset_zero (s := restBox)
  intro p hp
  rw [errorCoeff_outside_box ai a b c x hai p hp]
  simp

theorem error_series_eq (ai a b c x U V : ℂ) (hai : ai ≠ 0) :
    (∑' p : ℕ × ℕ, errorCoeff ai a b c x p.1 p.2*U^p.1*V^p.2) = restPolynomial ai a b c x U V-1 := by
  rw [tsum_eq_sum (s := restBox) (fun p hp => by rw [errorCoeff_outside_box ai a b c x hai p hp]; simp)]
  norm_num [restBox, Finset.sum_product, Finset.sum_range_succ, errorCoeff,
    residueRest_10 ai a b c x hai, residueRest_01 ai a b c x hai,
    residueRest_20 ai a b c x hai, residueRest_02 ai a b c x hai,
    residueRest_11 ai a b c x hai, residueRest_21 ai a b c x hai,
    residueRest_12 ai a b c x hai, residueRest_22 ai a b c x hai]
  unfold restPolynomial
  ring

theorem restPolynomial_error_le_mass (ai a b c x U V : ℂ) (hai : ai ≠ 0) (M : ℝ)
    (hM : 0 ≤ M) (hU : ‖U‖ ≤ M) (hV : ‖V‖ ≤ M) :
    ‖restPolynomial ai a b c x U V-1‖ ≤ errorMass ai a b c x M := by
  rw [← error_series_eq ai a b c x U V hai]
  apply (norm_tsum_le_tsum_norm (error_series_summable ai a b c x U V hai).norm).trans
  apply Summable.tsum_le_tsum _ (error_series_summable ai a b c x U V hai).norm (error_mass_summable ai a b c x hai M)
  intro p
  simp only [norm_mul, norm_pow, pow_add]
  calc
    _ ≤ ‖errorCoeff ai a b c x p.1 p.2‖*M^p.1*M^p.2 := by gcongr
    _ = _ := by ring

end SixthMoment.Source.NoDPLocalClosure
