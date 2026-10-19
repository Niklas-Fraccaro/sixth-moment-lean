import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Sechstmoment

theorem rectangular_pair_length {a b : ℝ} (hab : a ≤ b) (h : 3*a + 5*b < 2) :
    a+b < 1/2 := by linarith

theorem rectangular_first_error {a b : ℝ} (hab : a ≤ b) (h : 3*a + 5*b < 2) :
    1/2 + a+b < 1 := by linarith

theorem rectangular_second_error {a b : ℝ} (h : 3*a + 5*b < 2) :
    3/4 + 3*a/8 + 5*b/8 < 1 := by linarith

theorem four_profile_length {a b c d : ℝ} (h₁ : a+b < 1/2) (h₂ : c+d < 1/2) :
    a+b+c+d < 1 := by linarith

theorem three_profile_length {a b c d : ℝ} (hd : 0 ≤ d) (h : a+b+c+d < 1) :
    a+b+c < 1 := by linarith

noncomputable def eta : ℝ := 19999/80000

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_quarter : eta < 1/4 := by norm_num [eta]
theorem v_endpoint_lt_eta : (9999 : ℝ)/40000 < eta := by norm_num [eta]
theorem beta_four_length : 4*eta = 1-1/20000 := by norm_num [eta]
theorem beta_four_length_lt_one : 4*eta < 1 := by norm_num [eta]

end Sechstmoment
