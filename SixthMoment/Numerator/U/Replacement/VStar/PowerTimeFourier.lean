import SixthMoment.Numerator.U.Replacement.VStar.TimeMellinRepresentation
import SixthMoment.Numerator.U.ZeroModes.RatioTimeFourierFubini

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 500000

def a03VStarPowerTimeFourier (Φ : ℝ→ℂ) (T : ℝ) (σ : MomentShifts)
    (Y x ξ : ℝ) (ρ : ℂ) : ℂ :=
  ∫t : ℝ,Complex.exp ((ξ:ℂ)*I*(t:ℂ))*Φ t*(t:ℂ)^ρ*
    bblrVStar (polarPoleKiller T σ) (x^2/(Y^2*t^2))

theorem a03VStarPowerTimeFourier_eq_positive {Φ : ℝ→ℂ} (hΦ : Continuous Φ)
    (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) {Y x c : ℝ} (hY : 0<Y) (hx : 0<x) (hc : 0<c)
    (T : ℝ) (σ : MomentShifts) (ξ : ℝ) (ρ : ℂ) :
    a03VStarPowerTimeFourier Φ T σ Y x ξ ρ=
      a03RatioTimeFourierContour Φ T σ c (a03VStarSpatialLog Y x) (-2) ξ ρ := by
  rw [←(a03RatioTimeFourierMode_integrable_eq hΦ hSupp hc T σ (a03VStarSpatialLog Y x) (-2) ξ ρ).2]
  unfold a03VStarPowerTimeFourier
  apply integral_congr_ae
  apply ae_of_all
  intro t
  dsimp only
  by_cases ht : Φ t=0
  · simp [a03RatioTimeFourierMode,ht]
  · have htp : 0<t := zero_lt_one.trans_le (hSupp (subset_tsupport _ ht)).1
    rw [a03VStar_time_eq_logDerivative hY hx htp T σ,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr htp.ne'),←Complex.ofReal_log htp.le]
    unfold a03RatioTimeFourierMode
    rw [a03ZeroModeRatioPartition_eq_logDerivative _ (Real.exp_pos _),Real.log_exp,
      show a03VStarSpatialLog Y x+(-2)*Real.log t=a03VStarSpatialLog Y x-2*Real.log t by ring]
    ring

theorem a03VStarPowerTimeFourier_eq_reflected {Φ : ℝ→ℂ} (hΦ : Continuous Φ)
    (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) {Y x : ℝ} (hY : 0<Y) (hx : 0<x)
    (T : ℝ) (σ : MomentShifts) (ξ : ℝ) (ρ : ℂ) :
    a03VStarPowerTimeFourier Φ T σ Y x ξ ρ=
      profileLaplaceTransform (a03ProfileProduct Φ (fun t : ℝ => (t:ℂ)^ρ)) ((ξ:ℂ)*I)-
        a03RatioTimeFourierContour Φ T σ 1 (-a03VStarSpatialLog Y x) 2 ξ ρ := by
  have hp := a03RatioTimeFourierMode_integrable_eq hΦ hSupp (by norm_num : (0:ℝ)<1)
    T σ (a03VStarSpatialLog Y x) (-2) ξ ρ
  have hn := a03RatioTimeFourierMode_integrable_eq hΦ hSupp (by norm_num : (0:ℝ)<1)
    T σ (-a03VStarSpatialLog Y x) 2 ξ ρ
  have he : (fun t : ℝ => a03RatioTimeFourierMode Φ T σ (a03VStarSpatialLog Y x) (-2) ξ ρ t+
      a03RatioTimeFourierMode Φ T σ (-a03VStarSpatialLog Y x) 2 ξ ρ t)=
      fun t : ℝ => Complex.exp ((ξ:ℂ)*I*(t:ℂ))*Φ t*(t:ℂ)^ρ := by
    funext t
    by_cases ht : Φ t=0
    · simp [a03RatioTimeFourierMode,ht]
    · have htp : 0<t := zero_lt_one.trans_le (hSupp (subset_tsupport _ ht)).1
      have hr := a03ZeroModeRatioPartition_identity (Real.exp_pos (a03VStarSpatialLog Y x+(-2)*Real.log t))
        (polarPoleKiller T σ) (rawMomentShifts T σ) (polarPoleKiller_BBLREntireWeight T σ _)
      have hneg : (Real.exp (a03VStarSpatialLog Y x+(-2)*Real.log t))⁻¹=
          Real.exp (-a03VStarSpatialLog Y x+2*Real.log t) := by
        rw [←Real.exp_neg]
        congr 1
        ring
      rw [hneg] at hr
      unfold a03RatioTimeFourierMode
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr htp.ne'),←Complex.ofReal_log htp.le]
      calc
        _=(Complex.exp ((ξ:ℂ)*I*(t:ℂ))*Φ t*Complex.exp (ρ*(Real.log t:ℂ)))*
          (a03ZeroModeRatioPartition (polarPoleKiller T σ) (Real.exp (a03VStarSpatialLog Y x+(-2)*Real.log t))+
           a03ZeroModeRatioPartition (polarPoleKiller T σ) (Real.exp (-a03VStarSpatialLog Y x+2*Real.log t))) := by ring
        _=_ := by rw [hr,mul_one]; ring
  have hi := integral_add hp.1 hn.1
  rw [he,hp.2,hn.2] at hi
  have hplain : (∫t : ℝ,Complex.exp ((ξ:ℂ)*I*(t:ℂ))*Φ t*(t:ℂ)^ρ)=
      profileLaplaceTransform (a03ProfileProduct Φ (fun t : ℝ => (t:ℂ)^ρ)) ((ξ:ℂ)*I) := by
    unfold profileLaplaceTransform a03ProfileProduct
    apply integral_congr_ae
    apply ae_of_all
    intro t
    ring
  rw [hplain] at hi
  rw [a03VStarPowerTimeFourier_eq_positive hΦ hSupp hY hx (by norm_num : (0:ℝ)<1) T σ ξ ρ]
  linear_combination -hi

end
end SixthMoment
