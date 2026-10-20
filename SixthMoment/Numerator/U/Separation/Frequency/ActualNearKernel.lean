import SixthMoment.Numerator.U.Separation.ActualSeparatedGap
import SixthMoment.Numerator.U.Separation.Frequency.GammaDualFar
import SixthMoment.Numerator.U.Separation.Frequency.GammaFar

namespace SixthMoment
open Complex Real Source MeasureTheory Set
open scoped ContDiff BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

def a03ActualArithmeticBlockFactor (T A B H : ℝ) (f g : ℝ → ℝ)
    (α : MomentShifts) (u v : ℕ) (k n : Fin 4 → ℕ) (h : ℕ) (z : ℂ) : ℂ :=
  (∏ j : Fin 4, (rectangularAFESmoothScale (k j) : ℂ) ^ (-(1 / 2 + α j + z))) *
    (phaseActualAmplifierCoefficient T f A (u + 1) *
      phaseActualAmplifierCoefficient T g B (v + 1)) *
    phaseBaseSmoothFactor (phaseActualScales A B H k) α z
      (rectangularAFESourceTuple (u + 1) (v + 1) n h)

theorem a03_actual_kernel_time_integral_factorization (T A B H : ℝ)
    (f g Φ : ℝ → ℝ) (σ α : MomentShifts) (u v : ℕ)
    (k n : Fin 4 → ℕ) (h : ℕ) (z : ℂ) :
    (∫ t : ℝ, phaseActualKernelSummand T A B H f g Φ (polarPoleKiller T σ)
      α u v t k n h z) =
      a03ActualArithmeticBlockFactor T A B H f g α u v k n h z *
        a03GaussianActualTimeIntegral (fun x => (Φ x : ℂ)) T σ α z (u + 1) (v + 1) n := by
  unfold a03GaussianActualTimeIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [phaseActualKernelSummand_exact_phase]
  unfold phaseActualCommonFactor a03ActualArithmeticBlockFactor
  ring

theorem a03_actual_kernel_dual_time_integral_factorization (T A B H : ℝ)
    (f g Φ : ℝ → ℝ) (σ α : MomentShifts) (u v : ℕ)
    (k n : Fin 4 → ℕ) (h : ℕ) (z : ℂ) :
    (∫ t : ℝ, bblrDualMultiplier t (rawMomentShifts T σ) *
      phaseActualKernelSummand T A B H f g Φ (polarPoleKiller T σ)
        α u v t k n h z) =
      a03ActualArithmeticBlockFactor T A B H f g α u v k n h z *
        a03GaussianActualDualTimeIntegral (fun x => (Φ x : ℂ)) T σ α z (u + 1) (v + 1) n := by
  unfold a03GaussianActualDualTimeIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [phaseActualKernelSummand_exact_phase]
  unfold phaseActualCommonFactor a03ActualArithmeticBlockFactor
  ring

theorem a03_actual_kernel_time_frequency_identity {T : ℝ} (hT : 0 < T)
    (A B H : ℝ) (f g Φ : ℝ → ℝ) (σ α : MomentShifts) (u v : ℕ)
    (k n : Fin 4 → ℕ) (h : ℕ) (z : ℂ) :
    (∫ t : ℝ, phaseActualKernelSummand T A B H f g Φ (polarPoleKiller T σ)
      α u v t k n h z) =
      (T : ℂ) * a03ActualArithmeticBlockFactor T A B H f g α u v k n h z *
        a03GaussianFrequencyProfile (fun x => (Φ x : ℂ)) T σ α z
          (-T * Real.log (phaseActualProductRatio (u + 1) (v + 1) n)) := by
  rw [a03_actual_kernel_time_integral_factorization,
    a03_gaussian_actual_time_exact_rescaling _ hT σ α z (by omega) (by omega)]
  ring

theorem a03_actual_kernel_dual_time_frequency_identity {T : ℝ} (hT : 0 < T)
    (A B H : ℝ) (f g Φ : ℝ → ℝ) (σ α : MomentShifts) (u v : ℕ)
    (k n : Fin 4 → ℕ) (h : ℕ) (z : ℂ) :
    (∫ t : ℝ, bblrDualMultiplier t (rawMomentShifts T σ) *
      phaseActualKernelSummand T A B H f g Φ (polarPoleKiller T σ)
        α u v t k n h z) =
      (T : ℂ) * a03ActualArithmeticBlockFactor T A B H f g α u v k n h z *
        a03GaussianDualFrequencyProfile (fun x => (Φ x : ℂ)) T σ α z
          (-T * Real.log (phaseActualProductRatio (u + 1) (v + 1) n)) := by
  rw [a03_actual_kernel_dual_time_integral_factorization,
    a03_gaussian_actual_dual_time_exact_rescaling _ hT σ α z (by omega) (by omega)]
  ring

end
end SixthMoment
