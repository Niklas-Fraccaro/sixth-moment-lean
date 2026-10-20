import SixthMoment.Numerator.U.Replacement.VStar.PowerTimeFourierEnvelope
import SixthMoment.Numerator.U.ZeroModes.GCDMasks.SpatialMass
import SixthMoment.Numerator.U.ZeroModes.RatioLeadingBranchSmooth

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 700000

def a03VStarActualBranchTimeFourier (dual : Bool) (Φ : ℝ→ℂ)
    (T : ℝ) (σ : MomentShifts) (Y x ξ : ℝ) : ℂ :=
  ∫t : ℝ,Complex.exp ((ξ:ℂ)*I*(t:ℂ))*a03RatioLeadingBranchProfile dual Φ T σ t*
    bblrVStar (polarPoleKiller T σ) (x^2/(Y^2*t^2))

theorem a03VStarActualBranchTimeFourier_eq_scalar_power {Φ : ℝ→ℂ}
    (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) {T : ℝ} (hT : 0<T)
    (σ : MomentShifts) (dual : Bool) (Y x ξ : ℝ) :
    a03VStarActualBranchTimeFourier dual Φ T σ Y x ξ=
      a03RatioLeadingScalar dual T σ*a03VStarPowerTimeFourier Φ T σ Y x ξ
        (a03RatioLeadingExponent dual T σ) := by
  unfold a03VStarActualBranchTimeFourier
  rw [a03RatioLeadingBranchProfile_eq_scalar_power hSupp hT σ dual]
  unfold a03VStarPowerTimeFourier a03ProfileProduct
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by ring

theorem a03VStarActualBranchTimeFourier_uniform_log_envelope {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (K : Set MomentShifts) (hK : IsCompact K) {c κ : ℝ}
    (hc : 0<c) (hκ : 0<κ) (N : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ dual : Bool,∀ Y x ξ : ℝ,0<Y → 0<x →
      (1+|ξ|)^N*‖a03VStarActualBranchTimeFourier dual Φ T σ Y x ξ‖≤
        C*(Real.log T)^48*a03VStarPowerXEnvelope c Y x := by
  obtain ⟨D,hD,hbound⟩ := a03VStarPowerTimeFourier_uniform_log_envelope hΦ hSupp hc
    (by norm_num : (0:ℝ)≤1) hκ N
  obtain ⟨E,hE,hscalar⟩ := a03RatioLeadingScalar_uniform_eventually_bound K hK
  refine ⟨E*D,by positivity,?_⟩
  filter_upwards [hscalar,a03RatioLeadingExponent_uniform_eventually_small K hK,
    eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with T hs hr hT hL
  intro σ hσ hroot dual Y x ξ hY hx
  rw [a03VStarActualBranchTimeFourier_eq_scalar_power hSupp (zero_lt_one.trans hT),norm_mul]
  have hp := hbound T hT hL σ hroot Y x ξ hY hx
    (a03RatioLeadingExponent dual T σ) (hr σ hσ dual)
  calc
    _=‖a03RatioLeadingScalar dual T σ‖*((1+|ξ|)^N*
      ‖a03VStarPowerTimeFourier Φ T σ Y x ξ (a03RatioLeadingExponent dual T σ)‖) := by ring
    _≤E*(D*(Real.log T)^48*a03VStarPowerXEnvelope c Y x) :=
      mul_le_mul (hs σ hσ dual) hp (by positivity) hE
    _=_ := by ring

theorem a03VStarActualBranchTimeFourier_uniform_degreeTen_log_envelope {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ) (N : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ dual : Bool,∀ Y x ξ : ℝ,0<Y → 0<x →
      (1+|ξ|)^N*‖a03VStarActualBranchTimeFourier dual Φ T σ Y x ξ‖≤
        C*(Real.log T)^48*a03NativeGCDSpatialEnvelope Y x := by
  obtain ⟨C,hC,hbound⟩ := a03VStarActualBranchTimeFourier_uniform_log_envelope hΦ hSupp K hK
    (c:=5) (by norm_num) hκ N
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with T hb
  intro σ hσ hroot dual Y x ξ hY hx
  have he : a03VStarPowerXEnvelope 5 Y x=a03NativeGCDSpatialEnvelope Y x := by
    unfold a03VStarPowerXEnvelope a03NativeGCDSpatialEnvelope
    norm_num only [show (2:ℝ)*5=10 by norm_num,Real.rpow_ofNat]
  simpa only [he] using hb σ hσ hroot dual Y x ξ hY hx

end
end SixthMoment
