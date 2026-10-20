import Sechstmoment.Numerator.U.Separation.ActualGapPhase

namespace Sechstmoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem phase_log_one_add_comparable {x : ℝ} (hx : |x| ≤ 1/2) :
    |x|/2 ≤ |Real.log (1+x)| ∧ |Real.log (1+x)| ≤ 2*|x| := by
  have hx₁ := (abs_le.mp hx).1
  have hx₂ := (abs_le.mp hx).2
  have hp : 0<1+x := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos hp
  have hu := Real.log_le_sub_one_of_pos hp
  have hi : (1+x)*(1+x)⁻¹=1 := mul_inv_cancel₀ hp.ne'
  by_cases h0 : 0≤x
  · have hlog : 0≤Real.log (1+x) := Real.log_nonneg (by linarith)
    rw [abs_of_nonneg h0,abs_of_nonneg hlog]
    constructor
    · have hbase : x/2≤1-(1+x)⁻¹ := by
        nlinarith [mul_nonneg h0 (by linarith : 0≤1-x)]
      exact hbase.trans hl
    · linarith
  · have h0' : x≤0 := (lt_of_not_ge h0).le
    have hlog : Real.log (1+x)≤0 := Real.log_nonpos hp.le (by linarith)
    rw [abs_of_nonpos h0',abs_of_nonpos hlog]
    constructor
    · linarith
    · have hbase : 2*x≤1-(1+x)⁻¹ := by
        nlinarith [mul_nonneg (neg_nonneg.mpr h0') (by linarith : 0≤1+2*x)]
      linarith

theorem phase_gap_ratio_abs (positive : Bool) (b h : ℕ) (n : Fin 4 → ℕ) :
    |rectangularGapRatio positive b h n|=
      (h:ℝ)/((b*(n 2+1)*(n 3+1):ℕ):ℝ) := by
  have h₂ : 0≤(n 2:ℝ)+1 := by positivity
  have h₃ : 0≤(n 3:ℝ)+1 := by positivity
  cases positive <;> simp [rectangularGapRatio,rectangularGapSign,abs_div,abs_mul,abs_of_nonneg h₂,abs_of_nonneg h₃]

theorem phase_gap_ratio_ne_zero (positive : Bool) {b h : ℕ}
    (hb : 0<b) (hh : 0<h) (n : Fin 4 → ℕ) :
    rectangularGapRatio positive b h n≠0 := by
  have hd : (0:ℝ)<((b*(n 2+1)*(n 3+1):ℕ):ℝ) := by positivity
  have hp : 0 < |rectangularGapRatio positive b h n| := by
    rw [phase_gap_ratio_abs]
    exact div_pos (by exact_mod_cast hh) hd
  exact abs_pos.mp hp

theorem phase_gap_log_frequency_bounds (positive : Bool) {b h : ℕ}
    (hb : 0<b) (hh : 0<h) (n : Fin 4 → ℕ)
    (hr : |rectangularGapRatio positive b h n|≤1/2) :
    (h:ℝ)/(2*((b*(n 2+1)*(n 3+1):ℕ):ℝ))≤
        |Real.log (1+rectangularGapRatio positive b h n)| ∧
      |Real.log (1+rectangularGapRatio positive b h n)|≤
        2*(h:ℝ)/((b*(n 2+1)*(n 3+1):ℕ):ℝ) ∧
      Real.log (1+rectangularGapRatio positive b h n)≠0 := by
  have hc := phase_log_one_add_comparable hr
  have hpos : 0 < |rectangularGapRatio positive b h n| :=
    abs_pos.mpr (phase_gap_ratio_ne_zero positive hb hh n)
  have hlpos : 0 < |Real.log (1+rectangularGapRatio positive b h n)| := by
    exact (half_pos hpos).trans_le hc.1
  rw [phase_gap_ratio_abs] at hc
  refine ⟨?_,?_,abs_pos.mp hlpos⟩
  · simpa only [div_div,mul_comm (2:ℝ)] using hc.1
  · simpa only [mul_div_assoc] using hc.2

theorem phase_exact_gap_power_eq_exp {x : ℝ} (hx : -1<x) (t : ℝ) :
    (1+(x:ℂ))^(-(t:ℂ)*I)=Complex.exp (-(t*Real.log (1+x):ℝ)*I) := by
  have hp : 0<1+x := by linarith
  have hz : (1+(x:ℂ))≠0 := by
    exact_mod_cast hp.ne'
  rw [Complex.cpow_def_of_ne_zero hz]
  have he : Complex.log (1+(x:ℂ))=(Real.log (1+x):ℂ) := by
    simpa only [Complex.ofReal_add,Complex.ofReal_one] using (Complex.ofReal_log hp.le).symm
  rw [he]
  congr 1
  push_cast
  ring

theorem phase_actual_gap_power_eq_exp (positive : Bool) (a b : ℕ)
    (hb : 0<b) (t : ℝ) (n : Fin 4 → ℕ)
    (hn : if positive then rectangularPositiveQuadGap a b n else rectangularNegativeQuadGap a b n)
    (hr : |rectangularGapRatio positive b (rectangularAFEGap positive a b n) n|≤1/2) :
    rectangularTwistedQuadPhase t a b n=
      Complex.exp (-(t*Real.log
        (1+rectangularGapRatio positive b (rectangularAFEGap positive a b n) n):ℝ)*I) := by
  rw [rectangular_actual_signed_gap_phase positive a b hb t n hn]
  apply phase_exact_gap_power_eq_exp
  have h := (abs_le.mp hr).1
  linarith

theorem phase_gap_scaled_log_lower {T R x : ℝ} (hT : 0≤T)
    (hx : |x|≤1/2) (hR : R≤T*|x|) :
    R/2≤T*|Real.log (1+x)| := by
  have h := mul_le_mul_of_nonneg_left (phase_log_one_add_comparable hx).1 hT
  nlinarith

end
end Sechstmoment
