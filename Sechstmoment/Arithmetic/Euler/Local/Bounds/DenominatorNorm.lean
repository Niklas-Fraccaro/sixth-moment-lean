import Sechstmoment.Arithmetic.Euler.Local.Bounds.NumeratorNorm

/-! A product norm majorant for the four Euler denominator factors. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem denominator_norm_le (a b c d t : ℂ) :
    ‖denom a b c d t‖≤(1+‖a‖*‖t‖)*(1+‖b‖*‖t‖)*(1+‖c‖*‖t‖)*(1+‖d‖*‖t‖) := by
  have H (x : ℂ) : ‖1-x*t‖≤1+‖x‖*‖t‖ := by simpa only [norm_one,norm_mul] using norm_sub_le (1:ℂ) (x*t)
  simp only [denom,norm_mul]
  exact mul_le_mul (mul_le_mul (mul_le_mul (H a) (H b) (norm_nonneg _) (by positivity))
    (H c) (norm_nonneg _) (by positivity)) (H d) (norm_nonneg _) (by positivity)

end Sechstmoment.Source.NoDPLocal
