import Sechstmoment.Arithmetic.Euler.Local.Prime.PrincipalEulerExpansion


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem principal_euler_error_bound (x : ℂ) (hx : ‖x‖≤1) : ‖(1-x)^4*(1+4*x+x^2)-1‖≤35*‖x‖^2 := by
  have h0 := norm_nonneg x
  have h2 : ‖x‖^2≤1 := by simpa using pow_le_pow_left₀ h0 hx 2
  have h4 : ‖x‖^4≤1 := by simpa using pow_le_pow_left₀ h0 hx 4
  have H : ‖(-9:ℂ)+16*x-9*x^2+x^4‖≤35 := by
    calc
      _ ≤ ‖(-9:ℂ)+16*x-9*x^2‖+‖x^4‖ := norm_add_le _ _
      _ ≤ (‖(-9:ℂ)+16*x‖+‖9*x^2‖)+‖x^4‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ((‖(-9:ℂ)‖+‖16*x‖)+‖9*x^2‖)+‖x^4‖ := by gcongr; exact norm_add_le _ _
      _ ≤ 35 := by norm_num [norm_mul,norm_pow]; nlinarith
  rw [principal_euler_error_factored,norm_mul,norm_pow]
  nlinarith [mul_le_mul_of_nonneg_left H (sq_nonneg ‖x‖)]

end Sechstmoment.Source.NoDPLocal
