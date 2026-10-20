import SixthMoment.Numerator.U.Replacement.VStar.ActualBranchTimeFourierEnvelope
import SixthMoment.Numerator.U.ZeroModes.GCDMasks.SpatialPowerTail

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 700000

theorem a03ArithmeticFrequency_power_tail {L C z ξ : ℝ} (hL : 0<L)
    (hz : 0≤z) (N : ℕ) (hξ : L≤|ξ|)
    (hFour : (1+|ξ|)^(N+2)*z≤C) : (1+|ξ|)^2*z≤C/L^N := by
  apply (le_div_iff₀ (pow_pos hL N)).mpr
  have hp : L^N≤(1+|ξ|)^N :=
    pow_le_pow_left₀ hL.le (hξ.trans (by linarith [abs_nonneg ξ])) N
  calc
    _=L^N*((1+|ξ|)^2*z) := by ring
    _≤(1+|ξ|)^N*((1+|ξ|)^2*z) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _=(1+|ξ|)^(N+2)*z := by rw [pow_add]; ring
    _≤C := hFour

theorem a03VStarActualBranchTimeFourier_highFrequency_uniform_rapid
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ s : ℝ}
    (hκ : 0<κ) (hs : 0<s) (M : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ dual : Bool,∀ Y x ξ : ℝ,0<Y → 0<x → T^s≤|ξ| →
      (1+|ξ|)^2*‖a03VStarActualBranchTimeFourier dual Φ T σ Y x ξ‖≤
        C*T^(-M)*(Real.log T)^48*a03NativeGCDSpatialEnvelope Y x := by
  obtain ⟨N,hN⟩ := exists_nat_gt (M/s)
  have hNM : M≤s*(N:ℝ) := by
    have h := (div_lt_iff₀ hs).mp hN
    nlinarith only [h]
  obtain ⟨C,hC,hFour⟩ := a03VStarActualBranchTimeFourier_uniform_degreeTen_log_envelope
    hΦ hSupp K hK hκ (N+2)
  refine ⟨C,hC,?_⟩
  filter_upwards [hFour,eventually_ge_atTop (1:ℝ)] with T hFT hT
  intro σ hσ hroot dual Y x ξ hY hx hξ
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hh := a03ArithmeticFrequency_power_tail (Real.rpow_pos_of_pos hTp s)
    (norm_nonneg (a03VStarActualBranchTimeFourier dual Φ T σ Y x ξ)) N hξ
      (hFT σ hσ hroot dual Y x ξ hY hx)
  have he : (T^s)^N=T^(s*(N:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hTp.le]
  have hp : T^(-(s*(N:ℝ)))≤T^(-M) :=
    Real.rpow_le_rpow_of_exponent_le hT (by linarith only [hNM])
  calc
    _≤C*(Real.log T)^48*a03NativeGCDSpatialEnvelope Y x/(T^s)^N := hh
    _=(C*(Real.log T)^48*a03NativeGCDSpatialEnvelope Y x)*T^(-(s*(N:ℝ))) := by
      rw [he,div_eq_mul_inv,←Real.rpow_neg hTp.le]
    _≤(C*(Real.log T)^48*a03NativeGCDSpatialEnvelope Y x)*T^(-M) :=
      mul_le_mul_of_nonneg_left hp (by unfold a03NativeGCDSpatialEnvelope; positivity)
    _=_ := by ring

theorem a03VStarActualBranchTimeFourier_highSpatial_uniform_rapid
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ δ : ℝ}
    (hκ : 0<κ) (hδ : 0<δ) (M : ℝ) (N : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ dual : Bool,∀ Y x ξ : ℝ,0<Y → 0<x → Y*T^δ≤x →
      (1+|ξ|)^N*‖a03VStarActualBranchTimeFourier dual Φ T σ Y x ξ‖≤
        C*T^(-M)*(Real.log T)^48*a03NativeGCDSpatialEnvelope Y x := by
  let p : ℝ := 10+max M 0/δ
  have hkp : 10≤p := by
    have hn : 0≤max M 0/δ := div_nonneg (le_max_right _ _) hδ.le
    dsimp [p]
    linarith only [hn]
  have hcp : 0<p/2 := by linarith only [hkp]
  have hsave : M≤δ*(p-10) := by
    have he : δ*(p-10)=max M 0 := by dsimp [p]; field_simp [hδ.ne']; ring
    rw [he]
    exact le_max_left M 0
  obtain ⟨C,hC,hFour⟩ := a03VStarActualBranchTimeFourier_uniform_log_envelope
    hΦ hSupp K hK hcp hκ N
  refine ⟨C,hC,?_⟩
  filter_upwards [hFour,eventually_ge_atTop (1:ℝ)] with T hFT hT
  intro σ hσ hroot dual Y x ξ hY hx htail
  have hp := a03NativeGCDSpatialPower_tail_pointwise_saving hT hY hδ.le htail
    (by norm_num : (0:ℝ)≤10) hkp hsave
  have he : a03VStarPowerXEnvelope (p/2) Y x≤
      T^(-M)*a03NativeGCDSpatialEnvelope Y x := by
    simpa only [a03VStarPowerXEnvelope,a03NativeGCDSpatialEnvelope,
      show (2:ℝ)*(p/2)=p by ring,Real.rpow_ofNat] using hp
  calc
    _≤C*(Real.log T)^48*a03VStarPowerXEnvelope (p/2) Y x :=
      hFT σ hσ hroot dual Y x ξ hY hx
    _≤C*(Real.log T)^48*(T^(-M)*a03NativeGCDSpatialEnvelope Y x) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _=_ := by ring

end
end SixthMoment
