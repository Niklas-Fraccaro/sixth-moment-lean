import SixthMoment.Numerator.U.Separation.ActualGapPhase
import SixthMoment.Numerator.U.ZeroModes.GapMellinReconstruction

namespace SixthMoment
open Complex Real Set Filter MeasureTheory Source
open scoped Topology ContDiff BigOperators
noncomputable section
set_option maxHeartbeats 1000000

theorem a03NativeGapSign_time_integral (Ψ : ℝ→ℂ) (ξ : ℝ) (positive : Bool) :
    (∫ t : ℝ,Complex.exp (((-(ξ*rectangularGapSign positive):ℝ):ℂ)*I*(t:ℂ))*Ψ t)=
      profileLaplaceTransform Ψ (((-(ξ*rectangularGapSign positive):ℝ):ℂ)*I) := rfl

theorem a03NativeGapSigns_eq_two_cosine (Ψ : ℝ→ℂ) (ξ : ℝ) :
    (∑ positive : Bool,∫ t : ℝ,
      Complex.exp (((-(ξ*rectangularGapSign positive):ℝ):ℂ)*I*(t:ℂ))*Ψ t)=
        2*a03SmoothedCosine Ψ ξ := by
  simp_rw [a03NativeGapSign_time_integral]
  rw [Fintype.sum_bool]
  simp only [rectangularGapSign,Bool.false_eq_true,ite_false,ite_true,mul_neg_one,mul_one,neg_neg]
  unfold a03SmoothedCosine
  push_cast
  ring

theorem a03ProfileLaplace_positive_gap_norm_summable {Ψ : ℝ→ℂ}
    (hK : HasCompactSupport Ψ) (hΨ : ContDiff ℝ ∞ Ψ) {R : ℝ} (hR : 0<R) :
    Summable (fun h : ℕ => ‖profileLaplaceTransform Ψ
      (((R*((h:ℝ)+1):ℝ):ℂ)*I)‖) := by
  obtain ⟨C,_hC,hB⟩ := a03_profile_frequency_power_bound hK hΨ 2
  have hs : Summable (fun h : ℕ => (C/R^2)*((h:ℝ)+1)^(-(2:ℝ))) :=
    (a03GapPower_summable (by norm_num : (1:ℝ)<2)).mul_left _
  apply hs.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro h
  have hHp : (0:ℝ)<(h:ℝ)+1 := by positivity
  have hP := hB (R*((h:ℝ)+1))
  rw [abs_of_pos (mul_pos hR hHp),mul_pow] at hP
  have hquot : ‖profileLaplaceTransform Ψ (((R*((h:ℝ)+1):ℝ):ℂ)*I)‖≤C/(R^2*((h:ℝ)+1)^2) :=
    (le_div_iff₀ (mul_pos (pow_pos hR 2) (pow_pos hHp 2))).mpr (by convert hP using 1; ring)
  calc
    _≤C/(R^2*((h:ℝ)+1)^2) := hquot
    _=(C/R^2)*((h:ℝ)+1)^(-(2:ℝ)) := by
      rw [Real.rpow_neg hHp.le,Real.rpow_ofNat]
      rw [div_mul_eq_div_div,div_eq_mul_inv]

theorem a03ProfileLaplace_negative_gap_norm_summable {Ψ : ℝ→ℂ}
    (hK : HasCompactSupport Ψ) (hΨ : ContDiff ℝ ∞ Ψ) {R : ℝ} (hR : 0<R) :
    Summable (fun h : ℕ => ‖profileLaplaceTransform Ψ
      (((-(R*((h:ℝ)+1)):ℝ):ℂ)*I)‖) := by
  obtain ⟨C,_hC,hB⟩ := a03_profile_frequency_power_bound hK hΨ 2
  have hs : Summable (fun h : ℕ => (C/R^2)*((h:ℝ)+1)^(-(2:ℝ))) :=
    (a03GapPower_summable (by norm_num : (1:ℝ)<2)).mul_left _
  apply hs.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro h
  have hHp : (0:ℝ)<(h:ℝ)+1 := by positivity
  have hP := hB (-(R*((h:ℝ)+1)))
  rw [abs_neg,abs_of_pos (mul_pos hR hHp),mul_pow] at hP
  have hquot : ‖profileLaplaceTransform Ψ (((-(R*((h:ℝ)+1)):ℝ):ℂ)*I)‖≤C/(R^2*((h:ℝ)+1)^2) :=
    (le_div_iff₀ (mul_pos (pow_pos hR 2) (pow_pos hHp 2))).mpr (by convert hP using 1; ring)
  calc
    _≤C/(R^2*((h:ℝ)+1)^2) := hquot
    _=(C/R^2)*((h:ℝ)+1)^(-(2:ℝ)) := by
      rw [Real.rpow_neg hHp.le,Real.rpow_ofNat]
      rw [div_mul_eq_div_div,div_eq_mul_inv]

theorem a03NativeGapSign_norm_summable {Ψ : ℝ→ℂ}
    (hK : HasCompactSupport Ψ) (hΨ : ContDiff ℝ ∞ Ψ) {R : ℝ} (hR : 0<R)
    (positive : Bool) :
    Summable (fun h : ℕ => ‖∫ t : ℝ,
      Complex.exp (((-(R*((h:ℝ)+1)*rectangularGapSign positive):ℝ):ℂ)*I*(t:ℂ))*Ψ t‖) := by
  simp_rw [a03NativeGapSign_time_integral]
  cases positive
  · simp only [rectangularGapSign,Bool.false_eq_true,ite_false,mul_neg_one,neg_neg]
    exact a03ProfileLaplace_positive_gap_norm_summable hK hΨ hR
  · simp only [rectangularGapSign,ite_true,mul_one]
    exact a03ProfileLaplace_negative_gap_norm_summable hK hΨ hR

theorem a03NativeGapSigns_gap_sum {Ψ : ℝ→ℂ}
    (hK : HasCompactSupport Ψ) (hΨ : ContDiff ℝ ∞ Ψ) {R : ℝ} (hR : 0<R) :
    (∑ positive : Bool,∑' h : ℕ,∫ t : ℝ,
      Complex.exp (((-(R*((h:ℝ)+1)*rectangularGapSign positive):ℝ):ℂ)*I*(t:ℂ))*Ψ t)=
        2*(∑' h : ℕ,a03SmoothedCosine Ψ (R*((h:ℝ)+1))) := by
  rw [Fintype.sum_bool,←(a03NativeGapSign_norm_summable hK hΨ hR true).of_norm.tsum_add
    (a03NativeGapSign_norm_summable hK hΨ hR false).of_norm]
  have he (h : ℕ) : (∫ t : ℝ,
      Complex.exp (((-(R*((h:ℝ)+1)*rectangularGapSign true):ℝ):ℂ)*I*(t:ℂ))*Ψ t)+
      (∫ t : ℝ,Complex.exp (((-(R*((h:ℝ)+1)*rectangularGapSign false):ℝ):ℂ)*I*(t:ℂ))*Ψ t)=
      2*a03SmoothedCosine Ψ (R*((h:ℝ)+1)) := by
    simpa only [Fintype.sum_bool] using a03NativeGapSigns_eq_two_cosine Ψ (R*((h:ℝ)+1))
  simp_rw [he]
  rw [tsum_mul_left]

end
end SixthMoment
