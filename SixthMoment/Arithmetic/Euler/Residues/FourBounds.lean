import SixthMoment.Arithmetic.Euler.Residues.WeightedResidue

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

set_option linter.unusedSectionVars false
namespace SixthMoment.Source.NoDPResidues
open NoDPLocal
noncomputable def cubicHeight (h : ℕ) : ℝ := ((h:ℝ)+6)^3

section Bounds
variable (a b c d : ℂ) (r : ℝ) (hr : 0 ≤ r)
  (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (hc : ‖c‖ ≤ r) (hd : ‖d‖ ≤ r)
include hr ha hb hc hd

theorem e1_uniform : ‖e1 a b c d‖ ≤ 4*r := by
  calc
    _ ≤ ‖a‖+‖b‖+‖c‖+‖d‖ := e1_norm_le a b c d
    _ ≤ 4*r := by linarith

theorem e2_uniform : ‖e2 a b c d‖ ≤ 6*r^2 := by
  calc
    _ ≤ ‖a*b‖+‖a*c‖+‖a*d‖+‖b*c‖+‖b*d‖+‖c*d‖ := e2_norm_le a b c d
    _ ≤ r*r+r*r+r*r+r*r+r*r+r*r := by simp only [norm_mul]; gcongr
    _ = 6*r^2 := by ring

theorem e3_uniform : ‖e3 a b c d‖ ≤ 4*r^3 := by
  calc
    _ ≤ ‖a*b*c‖+‖a*b*d‖+‖a*c*d‖+‖b*c*d‖ := e3_norm_le a b c d
    _ ≤ r*r*r+r*r*r+r*r*r+r*r*r := by simp only [norm_mul]; gcongr
    _ = 4*r^3 := by ring

theorem coeff4_offset_bound (h k : ℕ) (hk : k ≤ 3) :
    ‖coeff4 a b c d (h+k)‖ ≤ cubicHeight h*r^(h+k) := by
  apply (norm_coeff4_polynomial a b c d r hr ha hb hc hd (h+k)).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr _)
  unfold cubicHeight
  apply pow_le_pow_left₀ (by positivity)
  push_cast
  have hk' : (k:ℝ) ≤ 3 := by exact_mod_cast hk
  linarith

theorem q1_growth (h : ℕ) : ‖q1 a b c d h‖ ≤ 5*cubicHeight h*r^(h+1) := by
  have H0 := coeff4_offset_bound a b c d r hr ha hb hc hd h 0 (by omega)
  have H1 := coeff4_offset_bound a b c d r hr ha hb hc hd h 1 (by omega)
  have E1 := e1_uniform a b c d r hr ha hb hc hd
  have HH : 0 ≤ cubicHeight h := by unfold cubicHeight; positivity
  simp only [Nat.add_zero] at H0
  calc
    _ ≤ ‖coeff4 a b c d (h+1)‖+‖e1 a b c d‖*‖coeff4 a b c d h‖ := q1_norm_le a b c d h
    _ ≤ cubicHeight h*r^(h+1)+(4*r)*(cubicHeight h*r^h) := by gcongr
    _ = _ := by rw [pow_succ]; ring

theorem q2_growth (h : ℕ) : ‖q2 a b c d h‖ ≤ 11*cubicHeight h*r^(h+2) := by
  have H0 := coeff4_offset_bound a b c d r hr ha hb hc hd h 0 (by omega)
  have H1 := coeff4_offset_bound a b c d r hr ha hb hc hd h 1 (by omega)
  have H2 := coeff4_offset_bound a b c d r hr ha hb hc hd h 2 (by omega)
  have E1 := e1_uniform a b c d r hr ha hb hc hd
  have E2 := e2_uniform a b c d r hr ha hb hc hd
  have HH : 0 ≤ cubicHeight h := by unfold cubicHeight; positivity
  simp only [Nat.add_zero] at H0
  calc
    _ ≤ ‖coeff4 a b c d (h+2)‖+‖e1 a b c d‖*‖coeff4 a b c d (h+1)‖+
        ‖e2 a b c d‖*‖coeff4 a b c d h‖ := q2_norm_le a b c d h
    _ ≤ cubicHeight h*r^(h+2)+(4*r)*(cubicHeight h*r^(h+1))+
        (6*r^2)*(cubicHeight h*r^h) := by gcongr
    _ = _ := by simp only [pow_add, pow_one]; ring

end Bounds

theorem q3_triangle (a b c d : ℂ) (h : ℕ) :
    ‖q3 a b c d h‖ ≤ ‖coeff4 a b c d (h+3)‖+
      ‖e1 a b c d‖*‖coeff4 a b c d (h+2)‖+
      ‖e2 a b c d‖*‖coeff4 a b c d (h+1)‖+
      ‖e3 a b c d‖*‖coeff4 a b c d h‖ := by
  unfold q3
  calc
    _ ≤ ‖coeff4 a b c d (h+3)-e1 a b c d*coeff4 a b c d (h+2)+
      e2 a b c d*coeff4 a b c d (h+1)‖+‖e3 a b c d*coeff4 a b c d h‖ := norm_sub_le _ _
    _ ≤ (‖coeff4 a b c d (h+3)-e1 a b c d*coeff4 a b c d (h+2)‖+
      ‖e2 a b c d*coeff4 a b c d (h+1)‖)+‖e3 a b c d*coeff4 a b c d h‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ((‖coeff4 a b c d (h+3)‖+‖e1 a b c d*coeff4 a b c d (h+2)‖)+
      ‖e2 a b c d*coeff4 a b c d (h+1)‖)+‖e3 a b c d*coeff4 a b c d h‖ := by
      gcongr
      exact norm_sub_le _ _
    _ = _ := by simp only [norm_mul]

section Bounds
variable (a b c d t : ℂ) (r : ℝ) (hr : 0 ≤ r)
  (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (hc : ‖c‖ ≤ r) (hd : ‖d‖ ≤ r)
include hr ha hb hc hd

theorem q3_growth (h : ℕ) : ‖q3 a b c d h‖ ≤ 15*cubicHeight h*r^(h+3) := by
  have H0 := coeff4_offset_bound a b c d r hr ha hb hc hd h 0 (by omega)
  have H1 := coeff4_offset_bound a b c d r hr ha hb hc hd h 1 (by omega)
  have H2 := coeff4_offset_bound a b c d r hr ha hb hc hd h 2 (by omega)
  have H3 := coeff4_offset_bound a b c d r hr ha hb hc hd h 3 (by omega)
  have E1 := e1_uniform a b c d r hr ha hb hc hd
  have E2 := e2_uniform a b c d r hr ha hb hc hd
  have E3 := e3_uniform a b c d r hr ha hb hc hd
  have HH : 0 ≤ cubicHeight h := by unfold cubicHeight; positivity
  simp only [Nat.add_zero] at H0
  calc
    _ ≤ ‖coeff4 a b c d (h+3)‖+‖e1 a b c d‖*‖coeff4 a b c d (h+2)‖+
        ‖e2 a b c d‖*‖coeff4 a b c d (h+1)‖+‖e3 a b c d‖*‖coeff4 a b c d h‖ := q3_triangle a b c d h
    _ ≤ cubicHeight h*r^(h+3)+(4*r)*(cubicHeight h*r^(h+2))+
        (6*r^2)*(cubicHeight h*r^(h+1))+(4*r^3)*(cubicHeight h*r^h) := by gcongr
    _ = _ := by simp only [pow_add, pow_one]; ring

theorem numerator_growth (h : ℕ) :
    ‖numerator a b c d h t‖ ≤ cubicHeight h*r^h*
      (1+5*(r*‖t‖)+11*(r*‖t‖)^2+15*(r*‖t‖)^3) := by
  have H0 := coeff4_offset_bound a b c d r hr ha hb hc hd h 0 (by omega)
  have H1 := q1_growth a b c d r hr ha hb hc hd h
  have H2 := q2_growth a b c d r hr ha hb hc hd h
  have H3 := q3_growth a b c d r hr ha hb hc hd h
  have HH : 0 ≤ cubicHeight h := by unfold cubicHeight; positivity
  simp only [Nat.add_zero] at H0
  calc
    _ ≤ ‖q0 a b c d h‖+‖q1 a b c d h‖*‖t‖+
      ‖q2 a b c d h‖*‖t‖^2+‖q3 a b c d h‖*‖t‖^3 := numerator_norm_le a b c d t h
    _ ≤ cubicHeight h*r^h+(5*cubicHeight h*r^(h+1))*‖t‖+
      (11*cubicHeight h*r^(h+2))*‖t‖^2+(15*cubicHeight h*r^(h+3))*‖t‖^3 := by
      change ‖coeff4 a b c d h‖+_+_+_ ≤ _
      gcongr
    _ = _ := by simp only [pow_add, pow_one]; ring

theorem numerator_unit_bound (hu : r*‖t‖ ≤ 1) (h : ℕ) :
    ‖numerator a b c d h t‖ ≤ 32*cubicHeight h*r^h := by
  have H := numerator_growth a b c d t r hr ha hb hc hd h
  have hu0 : 0 ≤ r*‖t‖ := mul_nonneg hr (norm_nonneg t)
  have hu2 : (r*‖t‖)^2 ≤ 1 := by simpa using pow_le_pow_left₀ hu0 hu 2
  have hu3 : (r*‖t‖)^3 ≤ 1 := by simpa using pow_le_pow_left₀ hu0 hu 3
  have HH : 0 ≤ cubicHeight h*r^h := by unfold cubicHeight; positivity
  calc
    _ ≤ cubicHeight h*r^h*(1+5*(r*‖t‖)+11*(r*‖t‖)^2+15*(r*‖t‖)^3) := H
    _ ≤ cubicHeight h*r^h*32 := mul_le_mul_of_nonneg_left (by linarith) HH
    _ = _ := by ring

theorem denominator_unit_bound (hu : r*‖t‖ ≤ 1) : ‖denom a b c d t‖ ≤ 16 := by
  have H (z : ℂ) (hz : ‖z‖ ≤ r) : ‖1-z*t‖ ≤ 2 := by
    calc
      _ ≤ 1+‖z‖*‖t‖ := by simpa only [norm_one, norm_mul] using norm_sub_le (1:ℂ) (z*t)
      _ ≤ 2 := by nlinarith [mul_le_mul_of_nonneg_right hz (norm_nonneg t)]
  simp only [denom, norm_mul]
  calc
    ‖1-a*t‖*‖1-b*t‖*‖1-c*t‖*‖1-d*t‖ ≤ 2*2*2*2 := by gcongr <;> apply H <;> assumption
    _ = 16 := by norm_num

theorem numerator_subconstant_bound (hu : r*‖t‖ ≤ 1) (h : ℕ) :
    ‖numerator a b c d h t-coeff4 a b c d h‖ ≤ 31*cubicHeight h*r^h*(r*‖t‖) := by
  have H1 := q1_growth a b c d r hr ha hb hc hd h
  have H2 := q2_growth a b c d r hr ha hb hc hd h
  have H3 := q3_growth a b c d r hr ha hb hc hd h
  have HH : 0 ≤ cubicHeight h := by unfold cubicHeight; positivity
  have hu0 : 0 ≤ r*‖t‖ := mul_nonneg hr (norm_nonneg t)
  have hu2 : (r*‖t‖)^2 ≤ r*‖t‖ := by nlinarith
  have hu3 : (r*‖t‖)^3 ≤ r*‖t‖ := by
    calc
      _ = (r*‖t‖)^2*(r*‖t‖) := by ring
      _ ≤ (r*‖t‖)*1 := mul_le_mul hu2 hu hu0 hu0
      _ = _ := by ring
  have E : numerator a b c d h t-coeff4 a b c d h =
      q1 a b c d h*t+q2 a b c d h*t^2+q3 a b c d h*t^3 := by unfold numerator q0; ring
  rw [E]
  calc
    _ ≤ (‖q1 a b c d h*t‖+‖q2 a b c d h*t^2‖)+‖q3 a b c d h*t^3‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (5*cubicHeight h*r^(h+1))*‖t‖+(11*cubicHeight h*r^(h+2))*‖t‖^2+
      (15*cubicHeight h*r^(h+3))*‖t‖^3 := by simp only [norm_mul, norm_pow]; gcongr
    _ = cubicHeight h*r^h*(5*(r*‖t‖)+11*(r*‖t‖)^2+15*(r*‖t‖)^3) := by simp only [pow_add, pow_one]; ring
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hu2 (by positivity : 0 ≤ cubicHeight h*r^h),
      mul_le_mul_of_nonneg_left hu3 (by positivity : 0 ≤ cubicHeight h*r^h)]

end Bounds
end SixthMoment.Source.NoDPResidues
