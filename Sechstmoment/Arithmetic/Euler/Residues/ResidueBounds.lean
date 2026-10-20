import Sechstmoment.Arithmetic.Euler.Residues.FourBounds

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
namespace Sechstmoment.Source.NoDPResidues
open NoDPLocal
noncomputable def quadraticHeight (h : ℕ) : ℝ := ((h:ℝ)+4)^2

section Bounds
variable (a b c : ℂ) (r : ℝ) (hr : 0 ≤ r)
  (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (hc : ‖c‖ ≤ r)
include hr ha hb hc

theorem three_e1_bound : ‖a+b+c‖ ≤ 3*r := by
  calc
    _ ≤ ‖a‖+‖b‖+‖c‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 3*r := by linarith

theorem three_e2_bound : ‖a*b+a*c+b*c‖ ≤ 3*r^2 := by
  calc
    _ ≤ ‖a*b‖+‖a*c‖+‖b*c‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ r*r+r*r+r*r := by simp only [norm_mul]; gcongr
    _ = _ := by ring

theorem three_product_bound : ‖a*b*c‖ ≤ r^3 := by
  simp only [norm_mul]
  calc
    _ ≤ r*r*r := by gcongr
    _ = _ := by ring

theorem coeff3_closed_bound (n : ℕ) :
    ‖coeff3 a b c n‖ ≤ ((n:ℝ)+1)*((n:ℝ)+2)/2*r^n := by
  simpa only [coeff3_equal_roots] using norm_coeff3_le a b c r hr ha hb hc n

theorem coeff3_polynomial_bound (n : ℕ) :
    ‖coeff3 a b c n‖ ≤ ((n:ℝ)+2)^2*r^n := by
  apply (coeff3_closed_bound a b c r hr ha hb hc n).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr n)
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [sq_nonneg (n:ℝ)]

theorem coeff3_offset_bound (h k : ℕ) (hk : k ≤ 2) :
    ‖coeff3 a b c (h+k)‖ ≤ quadraticHeight h*r^(h+k) := by
  apply (coeff3_polynomial_bound a b c r hr ha hb hc (h+k)).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr _)
  unfold quadraticHeight
  apply pow_le_pow_left₀ (by positivity)
  push_cast
  have hk' : (k:ℝ) ≤ 2 := by exact_mod_cast hk
  linarith

theorem triQ1_growth (h : ℕ) : ‖triQ1 a b c h‖ ≤ 4*quadraticHeight h*r^(h+1) := by
  have H0 := coeff3_offset_bound a b c r hr ha hb hc h 0 (by omega)
  have H1 := coeff3_offset_bound a b c r hr ha hb hc h 1 (by omega)
  have E1 := three_e1_bound a b c r hr ha hb hc
  have HH : 0 ≤ quadraticHeight h := by unfold quadraticHeight; positivity
  simp only [Nat.add_zero] at H0
  calc
    _ ≤ ‖coeff3 a b c (h+1)‖+‖a+b+c‖*‖coeff3 a b c h‖ := by
      simpa [triQ1, norm_mul] using norm_sub_le (coeff3 a b c (h+1)) ((a+b+c)*coeff3 a b c h)
    _ ≤ quadraticHeight h*r^(h+1)+(3*r)*(quadraticHeight h*r^h) := by gcongr
    _ = _ := by rw [pow_succ]; ring

theorem triQ2_growth (h : ℕ) : ‖triQ2 a b c h‖ ≤ 7*quadraticHeight h*r^(h+2) := by
  have H0 := coeff3_offset_bound a b c r hr ha hb hc h 0 (by omega)
  have H1 := coeff3_offset_bound a b c r hr ha hb hc h 1 (by omega)
  have H2 := coeff3_offset_bound a b c r hr ha hb hc h 2 (by omega)
  have E1 := three_e1_bound a b c r hr ha hb hc
  have E2 := three_e2_bound a b c r hr ha hb hc
  have HH : 0 ≤ quadraticHeight h := by unfold quadraticHeight; positivity
  simp only [Nat.add_zero] at H0
  calc
    _ ≤ ‖coeff3 a b c (h+2)-(a+b+c)*coeff3 a b c (h+1)‖+
      ‖(a*b+a*c+b*c)*coeff3 a b c h‖ := norm_add_le _ _
    _ ≤ (‖coeff3 a b c (h+2)‖+‖a+b+c‖*‖coeff3 a b c (h+1)‖)+
      ‖a*b+a*c+b*c‖*‖coeff3 a b c h‖ := by
      simpa only [norm_mul] using add_le_add
        (norm_sub_le (coeff3 a b c (h+2)) ((a+b+c)*coeff3 a b c (h+1)))
        (le_refl ‖(a*b+a*c+b*c)*coeff3 a b c h‖)
    _ ≤ quadraticHeight h*r^(h+2)+(3*r)*(quadraticHeight h*r^(h+1))+
      (3*r^2)*(quadraticHeight h*r^h) := by gcongr
    _ = _ := by simp only [pow_add, pow_one]; ring

end Bounds

theorem triNumerator_norm (a b c t : ℂ) (h : ℕ) :
    ‖triNumerator a b c h t‖ ≤ ‖coeff3 a b c h‖+‖triQ1 a b c h‖*‖t‖+
      ‖triQ2 a b c h‖*‖t‖^2 := by
  unfold triNumerator
  calc
    _ ≤ (‖coeff3 a b c h‖+‖triQ1 a b c h*t‖)+‖triQ2 a b c h*t^2‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = _ := by simp only [norm_mul, norm_pow]

section Bounds
variable (a b c t : ℂ) (r : ℝ) (hr : 0 ≤ r)
  (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (hc : ‖c‖ ≤ r)
include hr ha hb hc

theorem triNumerator_growth (h : ℕ) :
    ‖triNumerator a b c h t‖ ≤ quadraticHeight h*r^h*(1+4*(r*‖t‖)+7*(r*‖t‖)^2) := by
  have H0 := coeff3_offset_bound a b c r hr ha hb hc h 0 (by omega)
  have H1 := triQ1_growth a b c r hr ha hb hc h
  have H2 := triQ2_growth a b c r hr ha hb hc h
  have HH : 0 ≤ quadraticHeight h := by unfold quadraticHeight; positivity
  simp only [Nat.add_zero] at H0
  calc
    _ ≤ ‖coeff3 a b c h‖+‖triQ1 a b c h‖*‖t‖+‖triQ2 a b c h‖*‖t‖^2 := triNumerator_norm a b c t h
    _ ≤ quadraticHeight h*r^h+(4*quadraticHeight h*r^(h+1))*‖t‖+
      (7*quadraticHeight h*r^(h+2))*‖t‖^2 := by gcongr
    _ = _ := by simp only [pow_add, pow_one]; ring

theorem triNumerator_unit_bound (hu : r*‖t‖ ≤ 1) (h : ℕ) :
    ‖triNumerator a b c h t‖ ≤ 12*quadraticHeight h*r^h := by
  have H := triNumerator_growth a b c t r hr ha hb hc h
  have hu0 : 0 ≤ r*‖t‖ := mul_nonneg hr (norm_nonneg t)
  have hu2 : (r*‖t‖)^2 ≤ 1 := by simpa using pow_le_pow_left₀ hu0 hu 2
  have HH : 0 ≤ quadraticHeight h*r^h := by unfold quadraticHeight; positivity
  calc
    _ ≤ quadraticHeight h*r^h*(1+4*(r*‖t‖)+7*(r*‖t‖)^2) := H
    _ ≤ quadraticHeight h*r^h*12 := mul_le_mul_of_nonneg_left (by linarith) HH
    _ = _ := by ring

theorem residuePoly_bound (hr1 : r ≤ 1) (h : ℕ) :
    ‖residuePoly a b c h‖ ≤ 12*quadraticHeight h*r^h := by
  simpa only [residuePoly] using
    triNumerator_unit_bound a b c 1 r hr ha hb hc (by simpa using hr1) h

end Bounds

theorem weightedResidue_bound (ai a b c x : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ha : ‖x*a/ai‖ ≤ r) (hb : ‖x*b/ai‖ ≤ r) (hc : ‖x*c/ai‖ ≤ r)
    (hr1 : r ≤ 1) (h : ℕ) :
    ‖weightedResidue ai a b c x h‖ ≤ 12*quadraticHeight h*(‖ai‖*r)^h := by
  simp only [weightedResidue, norm_mul, norm_pow]
  calc
    _ ≤ ‖ai‖^h*(12*quadraticHeight h*r^h) :=
      mul_le_mul_of_nonneg_left (residuePoly_bound (x*a/ai) (x*b/ai) (x*c/ai) r hr ha hb hc hr1 h) (by positivity)
    _ = _ := by rw [mul_pow]; ring

theorem weightedResidue_first_error_bound (ai a b c x : ℂ) (hai : ai ≠ 0)
    (r : ℝ) (hr : 0 ≤ r) (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (hc : ‖c‖ ≤ r) :
    ‖weightedResidue ai a b c x 1-x*(a+b+c)‖ ≤
      ‖x‖^2/‖ai‖*(3*r^2+(‖x‖/‖ai‖)*r^3) := by
  rw [weightedResidue_first_error ai a b c x hai, norm_mul, norm_div, norm_pow]
  have H2 := three_e2_bound a b c r hr ha hb hc
  have H3 := three_product_bound a b c r hr ha hb hc
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ‖-(a*b+a*c+b*c)‖+‖(x/ai)*a*b*c‖ := norm_add_le _ _
    _ = ‖a*b+a*c+b*c‖+(‖x‖/‖ai‖)*‖a*b*c‖ := by simp only [norm_neg, norm_mul, norm_div]; ring
    _ ≤ _ := by gcongr

end Sechstmoment.Source.NoDPResidues
