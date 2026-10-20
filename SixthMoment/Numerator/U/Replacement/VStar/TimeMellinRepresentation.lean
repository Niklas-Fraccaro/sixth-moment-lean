import SixthMoment.Numerator.U.Replacement.VStar.LogTimeFubini
import SixthMoment.Numerator.U.ZeroModes.ForwardMellin
import SixthMoment.Numerator.U.ZeroModes.Ratio.XEnvelopeMass

namespace SixthMoment
open Complex Real Source Set MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 700000

def a03VStarSpatialLog (Y x : ℝ) : ℝ := Real.log ((2*Real.pi)^2*x^2/Y^2)

def a03VStarSmoothedTimeMellin (Φ : ℝ→ℂ) (T : ℝ) (σ : MomentShifts)
    (Y x : ℝ) (s : ℂ) : ℂ :=
  ∫t : ℝ,Φ t*bblrVStar (polarPoleKiller T σ) (x^2/(Y^2*t^2))*(t:ℂ)^(-s)

theorem a03VStar_time_eq_logDerivative {Y x t : ℝ} (hY : 0<Y) (hx : 0<x) (ht : 0<t)
    (T : ℝ) (σ : MomentShifts) :
    bblrVStar (polarPoleKiller T σ) (x^2/(Y^2*t^2))=
      a03ZeroModeRatioLogDerivative (polarPoleKiller T σ) 0
        (a03VStarSpatialLog Y x-2*Real.log t) := by
  have hy : 0<x^2/(Y^2*t^2) := by positivity
  rw [a03VStar_eq_ratio_scaled hy,a03ZeroModeRatioPartition_eq_logDerivative _ (by positivity)]
  congr 1
  have he : (2*Real.pi)^2*(x^2/(Y^2*t^2))=((2*Real.pi)^2*x^2/Y^2)/t^2 := by ring
  rw [he,Real.log_div (by positivity) (by positivity),Real.log_pow]
  rfl

theorem a03VStarSmoothedTimeMellin_eq_positive {Φ : ℝ→ℂ} (hΦ : Continuous Φ)
    (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) {Y x : ℝ} (hY : 0<Y) (hx : 0<x)
    (T : ℝ) (σ : MomentShifts) (s : ℂ) :
    a03VStarSmoothedTimeMellin Φ T σ Y x s=
      a03GaussianPositiveTimeMellinIntegral Φ T σ (a03VStarSpatialLog Y x) (3-s.re) 2 (-s.im) := by
  have he := (a03VStarLogTimeMode_integrable_eq hΦ hSupp T σ (a03VStarSpatialLog Y x) (-2) (-s)).2
  have hq : 1+(-s).re-(-2)=3-s.re := by simp; ring
  simp only [hq,neg_neg,Complex.neg_im] at he
  rw [←he]
  unfold a03VStarSmoothedTimeMellin
  apply integral_congr_ae
  apply ae_of_all
  intro t
  dsimp only
  by_cases ht : Φ t=0
  · simp [a03VStarLogTimeMode,ht]
  · have htp : 0<t := zero_lt_one.trans_le (hSupp (subset_tsupport _ ht)).1
    rw [a03VStar_time_eq_logDerivative hY hx htp T σ,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr htp.ne'),←Complex.ofReal_log htp.le]
    unfold a03VStarLogTimeMode
    rw [show a03VStarSpatialLog Y x+(-2)*Real.log t=a03VStarSpatialLog Y x-2*Real.log t by ring]
    ring

theorem a03VStarSmoothedTimeMellin_eq_reflected {Φ : ℝ→ℂ} (hΦ : Continuous Φ)
    (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) {Y x : ℝ} (hY : 0<Y) (hx : 0<x)
    (T : ℝ) (σ : MomentShifts) (s : ℂ) :
    a03VStarSmoothedTimeMellin Φ T σ Y x s=
      mellin Φ (1-s)-a03GaussianPositiveTimeMellinIntegral Φ T σ
        (-a03VStarSpatialLog Y x) (-1-s.re) (-2) (-s.im) := by
  have hp := a03VStarLogTimeMode_integrable_eq hΦ hSupp T σ (a03VStarSpatialLog Y x) (-2) (-s)
  have hn := a03VStarLogTimeMode_integrable_eq hΦ hSupp T σ (-a03VStarSpatialLog Y x) 2 (-s)
  have he : (fun t : ℝ => a03VStarLogTimeMode Φ T σ (a03VStarSpatialLog Y x) (-2) (-s) t+
      a03VStarLogTimeMode Φ T σ (-a03VStarSpatialLog Y x) 2 (-s) t)=
      fun t : ℝ => Φ t*Complex.exp (-s*(Real.log t:ℂ)) := by
    funext t
    have hr := a03ZeroModeRatioLogDerivative_partition (polarPoleKiller T σ) (rawMomentShifts T σ)
      (polarPoleKiller_BBLREntireWeight T σ _) (a03VStarSpatialLog Y x+(-2)*Real.log t)
    unfold a03VStarLogTimeMode
    have hh : -(a03VStarSpatialLog Y x+(-2)*Real.log t)= -a03VStarSpatialLog Y x+2*Real.log t := by ring
    rw [hh] at hr
    calc
      _=Φ t*Complex.exp (-s*(Real.log t:ℂ))*(
        a03ZeroModeRatioLogDerivative (polarPoleKiller T σ) 0 (a03VStarSpatialLog Y x+(-2)*Real.log t)+
        a03ZeroModeRatioLogDerivative (polarPoleKiller T σ) 0 (-a03VStarSpatialLog Y x+2*Real.log t)) := by ring
      _=_ := by rw [hr,mul_one]
  have hi := integral_add hp.1 hn.1
  rw [he,a03PositiveTime_logged_integral_eq_mellin hSupp] at hi
  rw [hp.2,hn.2] at hi
  have hs : -s+1=1-s := by ring
  have hpq : 1+(-s).re-(-2)=3-s.re := by simp; ring
  have hnq : 1+(-s).re-2= -1-s.re := by simp; ring
  simp only [hs,hpq,hnq,neg_neg,Complex.neg_im] at hi
  rw [a03VStarSmoothedTimeMellin_eq_positive hΦ hSupp hY hx T σ s]
  linear_combination -hi

end
end SixthMoment
