import SixthMoment.Numerator.U.Separation.Frequency.ActualTimePhase
import SixthMoment.Numerator.U.Separation.Frequency.GlobalGap

namespace SixthMoment
open Complex Real Source MeasureTheory Set
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 1000000

def phaseActualProductRatio (a b : ℕ) (n : Fin 4 → ℕ) : ℝ :=
  ((a*(n 0+1)*(n 1+1):ℕ):ℝ)/((b*(n 2+1)*(n 3+1):ℕ):ℝ)

theorem phase_actual_product_ratio_pos {a b : ℕ} (ha : 0<a) (hb : 0<b)
    (n : Fin 4 → ℕ) : 0<phaseActualProductRatio a b n := by
  unfold phaseActualProductRatio
  positivity

theorem phase_actual_power_eq_exp_unrestricted {a b : ℕ} (ha : 0<a) (hb : 0<b)
    (t : ℝ) (n : Fin 4 → ℕ) :
    rectangularTwistedQuadPhase t a b n=
      Complex.exp (-(t*Real.log (phaseActualProductRatio a b n):ℝ)*I) := by
  have he : (1+((phaseActualProductRatio a b n-1:ℝ):ℂ))^(-(t:ℂ)*I)=
      Complex.exp (-(t*Real.log (phaseActualProductRatio a b n):ℝ)*I) := by
    have hp := phase_actual_product_ratio_pos ha hb n
    simpa only [show 1+(phaseActualProductRatio a b n-1)=phaseActualProductRatio a b n by ring] using
      phase_exact_gap_power_eq_exp (x := phaseActualProductRatio a b n-1) (by linarith) t
  convert he using 1
  unfold rectangularTwistedQuadPhase phaseActualProductRatio
  push_cast
  ring

theorem phase_actual_time_integral_eq_profile_unrestricted (Φ : ℝ → ℂ) (T : ℝ)
    {a b : ℕ} (ha : 0<a) (hb : 0<b) (n : Fin 4 → ℕ) :
    phaseActualTimeIntegral Φ T a b n=a03ProfileTimeFourier Φ T
      (-Real.log (phaseActualProductRatio a b n)) := by
  unfold phaseActualTimeIntegral a03ProfileTimeFourier
  apply integral_congr_ae
  filter_upwards [] with t
  rw [phase_actual_power_eq_exp_unrestricted ha hb]
  congr 2
  push_cast
  ring

theorem phase_actual_selected_far_log_lower (positive : Bool) {a b : ℕ}
    (ha : 0<a) (hb : 0<b) (n : Fin 4 → ℕ)
    (hn : if positive then rectangularPositiveQuadGap a b n else rectangularNegativeQuadGap a b n)
    {η : ℝ} (hη : 0≤η) (hη1 : η≤1)
    (hfar : η*Real.sqrt ((a:ℝ)*b*(n 0+1)*(n 1+1)*(n 2+1)*(n 3+1))≤
      (rectangularAFEGap positive a b n:ℝ)) :
    η/8≤|Real.log (phaseActualProductRatio a b n)| := by
  let m := rectangularAFESourceTuple a b n (rectangularAFEGap positive a b n)
  have hpos : ∀ j : Fin 6, 0<m j.castSucc := by
    intro j
    fin_cases j <;> simp [m,rectangularAFESourceTuple,ha,hb]
  have h := phase_actual_source_far_log_lower positive m hpos
    (rectangular_AFE_gap_source_relation positive a b n hn) hη hη1
    (by simpa [m,rectangularAFESourceTuple] using hfar)
  simpa [m,rectangularAFESourceTuple,rectangularNearLeftProduct,rectangularNearRightProduct,
    phaseActualProductRatio,Nat.cast_mul] using h

theorem phase_actual_all_far_time_rapid {Φ : ℝ → ℂ}
    (hK : HasCompactSupport Φ) (hS : ContDiff ℝ ∞ Φ) {σ : ℝ} (hσ : 0<σ) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ T : ℝ, 1≤T → ∀ η : ℝ, 0≤η → η≤1 →
      8*T^σ≤T*η → ∀ positive : Bool, ∀ a b : ℕ, 0<a → 0<b → ∀ n : Fin 4 → ℕ,
      (if positive then rectangularPositiveQuadGap a b n else rectangularNegativeQuadGap a b n) →
      η*Real.sqrt ((a:ℝ)*b*(n 0+1)*(n 1+1)*(n 2+1)*(n 3+1))≤
        (rectangularAFEGap positive a b n:ℝ) →
      ‖phaseActualTimeIntegral Φ T a b n‖≤C*T^(-M) := by
  obtain ⟨C,hC,hfreq⟩ := a03_profile_polynomial_cutoff_rapid hK hS hσ M
  refine ⟨C,hC,?_⟩
  intro T hT η hη hη1 hcut positive a b ha hb n hn hfar
  rw [phase_actual_time_integral_eq_profile_unrestricted Φ T ha hb]
  apply hfreq T hT
  rw [abs_neg]
  have hlog := phase_actual_selected_far_log_lower positive ha hb n hn hη hη1 hfar
  have hm := mul_le_mul_of_nonneg_left hlog (by linarith : 0≤T)
  nlinarith

end
end SixthMoment
