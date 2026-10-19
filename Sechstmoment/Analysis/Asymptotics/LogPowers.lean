import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Elementary uniform power budgets on logarithmically displaced lines. -/

namespace Sechstmoment.Source
open Real
noncomputable section

theorem logarithmic_line_scaled_power_bound {T b c A : ℝ}
    (hT : 1 < T) (hb : 0 ≤ b) (hc : c ≤ 1+A/Real.log T) :
    (T^b)^c ≤ Real.exp (b*A)*T^b := by
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  have hscale : T^(b*A/Real.log T) = Real.exp (b*A) := by
    rw [Real.rpow_def_of_pos hT0]
    congr 1
    field_simp [hL.ne']
  calc
    _ = T^(b*c) := (Real.rpow_mul hT0.le b c).symm
    _ ≤ T^(b+b*A/Real.log T) := by
      apply Real.rpow_le_rpow_of_exponent_le hT.le
      have H := mul_le_mul_of_nonneg_left hc hb
      calc
        _ ≤ b*(1+A/Real.log T) := H
        _ = _ := by ring
    _ = _ := by rw [Real.rpow_add hT0,hscale]; ring

theorem logarithmic_line_quarter_power_bound {T c A : ℝ}
    (hT : 1 < T) (hc : c ≤ 1+A/Real.log T) :
    (T^(5/4:ℝ))^c ≤ Real.exp ((5/4:ℝ)*A)*T^(5/4:ℝ) :=
  logarithmic_line_scaled_power_bound hT (by norm_num) hc

end
end Sechstmoment.Source
