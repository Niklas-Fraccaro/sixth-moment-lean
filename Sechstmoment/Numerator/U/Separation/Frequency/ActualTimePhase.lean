import Sechstmoment.Analysis.Fourier.ProfileDecay
import Sechstmoment.Numerator.U.Separation.Frequency.LogFrequency

/-! Exact uniform far-frequency estimates for the literal amplifier-adjusted
AFE time phase. The time-dependent Gamma factor is not removed by this file. -/
namespace Sechstmoment
open Complex Real Source MeasureTheory Set
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 1000000

def phaseActualAmplifierPairConstant (T : ℝ) (f g : ℝ → ℝ) (u v : ℕ) : ℂ :=
  (f (Real.log (u+1:ℝ)/Real.log T):ℂ)*
    (g (Real.log (v+1:ℝ)/Real.log T):ℂ)*
    (u+1:ℂ)^(-(1/2:ℂ))*(v+1:ℂ)^(-(1/2:ℂ))

def phaseActualTimeIntegral (Φ : ℝ → ℂ) (T : ℝ) (a b : ℕ) (n : Fin 4 → ℕ) : ℂ :=
  ∫ t : ℝ, Φ (t/T)*rectangularTwistedQuadPhase t a b n

theorem phase_actual_time_integral_eq_profile (Φ : ℝ → ℂ) (T : ℝ)
    (positive : Bool) (a b : ℕ) (hb : 0<b) (n : Fin 4 → ℕ)
    (hn : if positive then rectangularPositiveQuadGap a b n else rectangularNegativeQuadGap a b n)
    (hr : |rectangularGapRatio positive b (rectangularAFEGap positive a b n) n|≤1/2) :
    phaseActualTimeIntegral Φ T a b n=a03ProfileTimeFourier Φ T
      (-Real.log (1+rectangularGapRatio positive b (rectangularAFEGap positive a b n) n)) := by
  unfold phaseActualTimeIntegral a03ProfileTimeFourier
  apply integral_congr_ae
  filter_upwards [] with t
  rw [phase_actual_gap_power_eq_exp positive a b hb t n hn hr]
  congr 2
  push_cast
  ring

theorem phase_actual_pair_time_integral_eq (T : ℝ) (f g Φ : ℝ → ℝ)
    (u v : ℕ) (n : Fin 4 → ℕ) :
    (∫ t : ℝ, rectangularMomentPairWeight T f g Φ u v t*rectangularAFEOscillation t n)=
      phaseActualAmplifierPairConstant T f g u v*
        phaseActualTimeIntegral (fun x => (Φ x:ℂ)) T (u+1) (v+1) n := by
  unfold phaseActualTimeIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [rectangular_actual_pair_weight_oscillation]
  unfold phaseActualAmplifierPairConstant
  ring

theorem phase_actual_time_polynomial_cutoff_rapid {Φ : ℝ → ℂ}
    (hK : HasCompactSupport Φ) (hS : ContDiff ℝ ∞ Φ) {σ : ℝ} (hσ : 0<σ) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ T : ℝ, 1≤T → ∀ positive : Bool, ∀ a b : ℕ, 0<b →
      ∀ n : Fin 4 → ℕ,
      (if positive then rectangularPositiveQuadGap a b n else rectangularNegativeQuadGap a b n) →
      |rectangularGapRatio positive b (rectangularAFEGap positive a b n) n|≤1/2 →
      2*T^σ≤T*|rectangularGapRatio positive b (rectangularAFEGap positive a b n) n| →
      ‖phaseActualTimeIntegral Φ T a b n‖≤C*T^(-M) := by
  obtain ⟨C,hC,hb⟩ := a03_profile_polynomial_cutoff_rapid hK hS hσ M
  refine ⟨C,hC,?_⟩
  intro T hT positive a b hbpos n hn hr hfar
  rw [phase_actual_time_integral_eq_profile Φ T positive a b hbpos n hn hr]
  apply hb T hT
  rw [abs_neg]
  have hfreq := phase_gap_scaled_log_lower (by linarith : 0≤T) hr hfar
  nlinarith

theorem phase_actual_pair_polynomial_cutoff_rapid {Φ : ℝ → ℝ}
    (hK : HasCompactSupport Φ) (hS : ContDiff ℝ ∞ Φ) {σ : ℝ} (hσ : 0<σ) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ T : ℝ, 1≤T → ∀ f g : ℝ → ℝ, ∀ positive : Bool,
      ∀ u v : ℕ, ∀ n : Fin 4 → ℕ,
      (if positive then rectangularPositiveQuadGap (u+1) (v+1) n
        else rectangularNegativeQuadGap (u+1) (v+1) n) →
      |rectangularGapRatio positive (v+1) (rectangularAFEGap positive (u+1) (v+1) n) n|≤1/2 →
      2*T^σ≤T*|rectangularGapRatio positive (v+1) (rectangularAFEGap positive (u+1) (v+1) n) n| →
      ‖∫ t : ℝ, rectangularMomentPairWeight T f g Φ u v t*rectangularAFEOscillation t n‖≤
        ‖phaseActualAmplifierPairConstant T f g u v‖*C*T^(-M) := by
  have hKs : HasCompactSupport (fun x => (Φ x:ℂ)) := hK.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hSs : ContDiff ℝ ∞ (fun x => (Φ x:ℂ)) := Complex.ofRealCLM.contDiff.comp hS
  obtain ⟨C,hC,hb⟩ := phase_actual_time_polynomial_cutoff_rapid hKs hSs hσ M
  refine ⟨C,hC,?_⟩
  intro T hT f g positive u v n hn hr hfar
  rw [phase_actual_pair_time_integral_eq,norm_mul]
  exact (mul_le_mul_of_nonneg_left
    (hb T hT positive (u+1) (v+1) (by omega) n hn hr hfar) (norm_nonneg _)).trans_eq (by ring)

end
end Sechstmoment
