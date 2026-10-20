import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.SpatialMass

namespace Sechstmoment.Source
open Complex Real Set Filter MeasureTheory
open scoped Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem a03NativeGCDSpatialBroadBudget_integrable {Y : ℝ} (hY : 0<Y) :
    IntegrableOn (fun X : ℝ => (X^(5/2:ℝ)+X^(7/2:ℝ))*
      a03NativeGCDSpatialEnvelope Y X) (Ioi 0) := by
  have h₁ := a03NativeGCDSpatialEnvelope_weight_integrable (r:=7/2) hY (by norm_num) (by norm_num)
  have h₂ := a03NativeGCDSpatialEnvelope_weight_integrable (r:=9/2) hY (by norm_num) (by norm_num)
  norm_num only [show (7/2:ℝ)-1=5/2 by norm_num,show (9/2:ℝ)-1=7/2 by norm_num] at h₁ h₂
  simpa only [IntegrableOn,Integrable,HasFiniteIntegral,add_mul,
    enorm_eq_nnnorm] using h₁.fun_add h₂

theorem a03NativeGCDSpatialBroadBudget_integral {Y : ℝ} (hY : 0<Y) :
    (∫ X : ℝ in Ioi 0,(X^(5/2:ℝ)+X^(7/2:ℝ))*a03NativeGCDSpatialEnvelope Y X)=
      (40/91:ℝ)*Y^(7/2:ℝ)+(40/99:ℝ)*Y^(9/2:ℝ) := by
  have h₁ := a03NativeGCDSpatialEnvelope_weight_integrable (r:=7/2) hY (by norm_num) (by norm_num)
  have h₂ := a03NativeGCDSpatialEnvelope_weight_integrable (r:=9/2) hY (by norm_num) (by norm_num)
  have e₁ := a03NativeGCDSpatialEnvelope_weight_integral (r:=7/2) hY (by norm_num) (by norm_num)
  have e₂ := a03NativeGCDSpatialEnvelope_weight_integral (r:=9/2) hY (by norm_num) (by norm_num)
  norm_num at h₁ h₂ e₁ e₂
  simp_rw [add_mul]
  rw [integral_add h₁ h₂,e₁,e₂]
  ring

theorem a03NativeGCDSpatialBroadBudget_uniform_power {Y T q : ℝ}
    (hT : 1≤T) (hY : 1≤Y) (hupper : Y≤T^q) :
    (∫ X : ℝ in Ioi 0,(X^(5/2:ℝ)+X^(7/2:ℝ))*a03NativeGCDSpatialEnvelope Y X)≤
      T^(q*(9/2:ℝ)) := by
  have hYp : 0<Y := zero_lt_one.trans_le hY
  rw [a03NativeGCDSpatialBroadBudget_integral hYp]
  have he : Y^(7/2:ℝ)≤Y^(9/2:ℝ) := Real.rpow_le_rpow_of_exponent_le hY (by norm_num)
  calc
    _≤((40/91:ℝ)+(40/99:ℝ))*Y^(9/2:ℝ) := by nlinarith
    _≤Y^(9/2:ℝ) := mul_le_of_le_one_left (by positivity) (by norm_num)
    _≤T^(q*(9/2:ℝ)) := by
      rw [Real.rpow_mul (zero_le_one.trans hT)]
      exact Real.rpow_le_rpow hYp.le hupper (by norm_num)

end
end Sechstmoment.Source
