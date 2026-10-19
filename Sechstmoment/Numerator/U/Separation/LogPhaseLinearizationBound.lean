import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! The actual quadratic logarithmic error on the supported near range. -/
namespace Sechstmoment
open Real

theorem a03_log_one_add_sub_self_quadratic {x : ℝ} (hx : |x|≤1/2) :
    |Real.log (1+x)-x|≤2*x^2 := by
  have ht : |(-x)|<1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le ht 1
  norm_num only [Finset.sum_range_one,pow_one,pow_two,Nat.cast_one,div_one,
    Nat.cast_add,abs_neg,neg_neg] at h
  have he : -x+Real.log (1- -x)=Real.log (1+x)-x := by ring
  rw [he] at h
  have hb : (1/2:ℝ)≤1-|x| := by linarith
  have habs : |x| * |x|=x^2 := by nlinarith [sq_abs x]
  rw [habs] at h
  calc
    _≤x^2/(1-|x|) := h
    _≤x^2/(1/2) := div_le_div_of_nonneg_left (sq_nonneg x) (by norm_num) hb
    _=_ := by ring

theorem a03_scaled_log_one_add_sub_self_quadratic {T x : ℝ} (hT : 0≤T) (hx : |x|≤1/2) :
    |T*Real.log (1+x)-T*x|≤2*T*x^2 := by
  rw [←mul_sub,abs_mul,abs_of_nonneg hT]
  exact (mul_le_mul_of_nonneg_left (a03_log_one_add_sub_self_quadratic hx) hT).trans_eq (by ring)
end Sechstmoment
