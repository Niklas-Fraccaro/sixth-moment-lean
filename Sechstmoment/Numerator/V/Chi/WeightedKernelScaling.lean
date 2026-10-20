import Sechstmoment.Analysis.Asymptotics.LogPowers


namespace Sechstmoment.Source
open Real
noncomputable section

theorem logarithmic_line_near_kernel_budget {T c A r : ℝ} (hT : 1 < T)
    (hc : 0 ≤ c) (hcline : c ≤ 1+A/Real.log T) (hr : 0 < r)
    (hnear : r ≤ T^(5/4:ℝ)) :
    r^c*(1/T+r/T^2) ≤ 2*Real.exp ((5/4:ℝ)*A)*T^(1/2:ℝ) := by
  have hT0 : 0 < T := by linarith
  have hpow : r^c ≤ Real.exp ((5/4:ℝ)*A)*T^(5/4:ℝ) :=
    (Real.rpow_le_rpow hr.le hnear hc).trans (logarithmic_line_quarter_power_bound hT hcline)
  have hmul : r^c*r ≤ Real.exp ((5/4:ℝ)*A)*(T^(5/4:ℝ))^2 := by
    calc
      _ ≤ (Real.exp ((5/4:ℝ)*A)*T^(5/4:ℝ))*T^(5/4:ℝ) :=
        mul_le_mul hpow hnear hr.le (by positivity)
      _ = _ := by ring
  have hfirst : T^(5/4:ℝ)/T ≤ T^(1/2:ℝ) := by
    rw [← Real.rpow_sub_one hT0.ne']
    norm_num
    exact Real.rpow_le_rpow_of_exponent_le hT.le (by norm_num : (1/4:ℝ) ≤ 1/2)
  have hsquare : (T^(5/4:ℝ))^2/T^2 = T^(1/2:ℝ) := by
    have he : (T^(5/4:ℝ))^2 = T^(5/2:ℝ) := by
      rw [← Real.rpow_two,← Real.rpow_mul hT0.le]
      norm_num
    rw [he,← Real.rpow_two,← Real.rpow_sub hT0]
    norm_num
  calc
    _ = r^c/T+(r^c*r)/T^2 := by ring
    _ ≤ (Real.exp ((5/4:ℝ)*A)*T^(5/4:ℝ))/T+
        (Real.exp ((5/4:ℝ)*A)*(T^(5/4:ℝ))^2)/T^2 :=
      add_le_add (div_le_div_of_nonneg_right hpow hT0.le)
        (div_le_div_of_nonneg_right hmul (sq_nonneg T))
    _ = Real.exp ((5/4:ℝ)*A)*(T^(5/4:ℝ)/T+(T^(5/4:ℝ))^2/T^2) := by ring
    _ ≤ Real.exp ((5/4:ℝ)*A)*(T^(1/2:ℝ)+T^(1/2:ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add hfirst hsquare.le) (Real.exp_nonneg _)
    _ = _ := by ring

theorem logarithmic_line_far_kernel_budget {T c A r : ℝ} (hT : 1 < T)
    (hc : c ≤ 8) (hcline : c ≤ 1+A/Real.log T)
    (hfar : T^(5/4:ℝ) ≤ r) :
    r^c*(T^9/r^8) ≤ Real.exp ((5/4:ℝ)*A)*T^(1/2:ℝ) := by
  have hT0 : 0 < T := by linarith
  have hX : 0 < T^(5/4:ℝ) := Real.rpow_pos_of_pos hT0 _
  have hr : 0 < r := hX.trans_le hfar
  have hpow := logarithmic_line_quarter_power_bound hT hcline
  have hmon := Real.rpow_le_rpow_of_nonpos hX hfar (show c-8 ≤ 0 by linarith)
  have he : (T^(5/4:ℝ))^8 = T^(10:ℝ) := by
    rw [← Real.rpow_natCast (T^(5/4:ℝ)) 8,← Real.rpow_mul hT0.le]
    norm_num
  have hratio : T^9*T^(5/4:ℝ)/(T^(5/4:ℝ))^8 ≤ T^(1/2:ℝ) := by
    have heq : T^9*T^(5/4:ℝ)/(T^(5/4:ℝ))^8 = T^(1/4:ℝ) := by
      rw [he,← Real.rpow_natCast T 9,← Real.rpow_add hT0,← Real.rpow_sub hT0]
      norm_num
    rw [heq]
    exact Real.rpow_le_rpow_of_exponent_le hT.le (by norm_num : (1/4:ℝ) ≤ 1/2)
  calc
    _ = T^9*r^(c-8) := by
      simp only [Real.rpow_sub hr,Real.rpow_ofNat,div_eq_mul_inv]
      ring
    _ ≤ T^9*(T^(5/4:ℝ))^(c-8) := mul_le_mul_of_nonneg_left hmon (pow_nonneg hT0.le _)
    _ = T^9*((T^(5/4:ℝ))^c/(T^(5/4:ℝ))^8) := by
      simp only [Real.rpow_sub hX,Real.rpow_ofNat]
    _ ≤ T^9*((Real.exp ((5/4:ℝ)*A)*T^(5/4:ℝ))/(T^(5/4:ℝ))^8) := by gcongr
    _ = Real.exp ((5/4:ℝ)*A)*(T^9*T^(5/4:ℝ)/(T^(5/4:ℝ))^8) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hratio (Real.exp_nonneg _)

end
end Sechstmoment.Source
