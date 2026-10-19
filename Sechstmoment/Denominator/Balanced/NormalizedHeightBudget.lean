import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Sechstmoment.Denominator.Balanced.MomentErrorBudget

/-! Normalization of a proved physical height power bound. -/
namespace Sechstmoment
open Complex Real MeasureTheory Filter Set
open scoped Topology
noncomputable section

theorem d02PowerHeight_normalized_norm_le {T C e : ℝ} {z : ℂ}
    (hT : 1<T) (hL : 1≤Real.log T) (hz : ‖z‖≤C*T^e) :
    ‖z/(T*(Real.log T)^9:ℂ)‖≤C*T^(e-1) := by
  have hTp : 0<T := zero_lt_one.trans hT
  have hpow : 1≤(Real.log T)^9 := one_le_pow₀ hL
  rw [norm_div,show (T*(Real.log T)^9:ℂ)=((T*(Real.log T)^9:ℝ):ℂ) by push_cast; rfl,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0<T*(Real.log T)^9)]
  calc
    _ ≤ ‖z‖/T := div_le_div_of_nonneg_left (norm_nonneg _) hTp (by nlinarith)
    _ ≤ (C*T^e)/T := div_le_div_of_nonneg_right hz hTp.le
    _ = C*T^(e-1) := by rw [Real.rpow_sub hTp,Real.rpow_one]; ring

theorem d02PowerHeight_normalized_uniform_small {β : Type*}
    (F : ℝ → β → ℂ) (P : β → Prop) {C e : ℝ} (he : e<1)
    (hb : ∀ᶠ T : ℝ in atTop,∀ u,P u → ‖F T u‖≤C*T^e)
    {η : ℝ} (hη : 0<η) :
    ∀ᶠ T : ℝ in atTop,∀ u,P u → ‖F T u/(T*(Real.log T)^9:ℂ)‖<η := by
  have hlim : Tendsto (fun T : ℝ => C*T^(e-1)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : 0<1-e)).const_mul C
    simpa only [show -(1-e)=e-1 by ring,mul_zero] using h
  filter_upwards [hb,eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (1:ℝ)),hlim.eventually_lt_const hη] with T hb hT hL hsmall
  intro u hu
  exact (d02PowerHeight_normalized_norm_le hT hL (hb u hu)).trans_lt hsmall

theorem d02PowerHeight_normalized_tendsto (F : ℝ → ℂ) {C e : ℝ} (he : e<1)
    (hb : ∀ᶠ T : ℝ in atTop,‖F T‖≤C*T^e) :
    Tendsto (fun T : ℝ => F T/(T*(Real.log T)^9:ℂ)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  have h := d02PowerHeight_normalized_uniform_small (fun T (_u : Unit) => F T)
    (fun _ => True) he (hb.mono (fun T hT _ _ => hT)) hη
  filter_upwards [h] with T hT
  simpa only [dist_eq_norm,sub_zero] using hT () trivial

end
end Sechstmoment
