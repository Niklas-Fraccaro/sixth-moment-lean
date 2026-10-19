import Sechstmoment.Numerator.U.Separation.Tensor.DualKernel
import Sechstmoment.Numerator.U.Separation.Tensor.MellinBridge
import Sechstmoment.Numerator.U.Sources.Weights.TensorParameters

/-! The actual original and dual physical time integrals are the literal
six-coordinate raw tensors. The power normalization is restored exactly. -/
namespace Sechstmoment
open Complex Real Source Set MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 2000000

theorem a03_actual_physical_frequency_main (positive : Bool) (T : ℝ) {A B H : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hH : 0 < H)
    (σ α : MomentShifts) (c v : ℝ) (k n : Fin 4 → ℕ) (a b : ℕ) (hb : 0 < b)
    (hn : if positive then rectangularPositiveQuadGap a b n
      else rectangularNegativeQuadGap a b n) :
    a03SixGaussianFrequencyKernel (fun x => (x : ℂ)) T σ α ((c : ℂ)+(v : ℂ)*I)
      (phaseActualNearTensorData T σ α v A B H k positive).r (rectangularGapSign positive)
      (a03SixTensorLogPoint (a03SixSourceArguments (phaseActualScales A B H k)
        (rectangularAFESourceTuple a b n (rectangularAFEGap positive a b n)))) =
      a03GaussianFrequencyProfile (fun x => (x : ℂ)) T σ α ((c : ℂ)+(v : ℂ)*I)
        (-T*Real.log (phaseActualProductRatio a b n)) := by
  unfold a03SixGaussianFrequencyKernel phaseActualNearTensorData
  rw [← mul_assoc B]
  rw [a03_actual_gap_frequency_identity positive T hA hB hH k n a b hb hn]
  congr 1
  ring

theorem a03_actual_physical_gap_frequency (positive : Bool) (T : ℝ) {A B H : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hH : 0 < H)
    (σ α : MomentShifts) (v : ℝ) (k n : Fin 4 → ℕ) (a b : ℕ) (hb : 0 < b)
    (hn : if positive then rectangularPositiveQuadGap a b n
      else rectangularNegativeQuadGap a b n) :
    a03RealLogGapSymbol T (phaseActualNearTensorData T σ α v A B H k positive).r
      (phaseActualNearTensorData T σ α v A B H k positive).s
      (a03SixGapLinear (a03SixTensorLogPoint (a03SixSourceArguments
        (phaseActualScales A B H k)
        (rectangularAFESourceTuple a b n (rectangularAFEGap positive a b n))))) =
      T*Real.log (phaseActualProductRatio a b n) := by
  simpa [phaseActualNearTensorData, mul_assoc] using
    a03_actual_gap_frequency_identity positive T hA hB hH k n a b hb hn

theorem a03_actual_kernel_time_raw_tensor_identity (positive : Bool) {T A B H : ℝ}
    (hT : 0 < T) (hA : 0 < A) (hB : 0 < B) (hH : 0 < H)
    (f g Φ : ℝ → ℝ) (σ α : MomentShifts) (c v : ℝ) (u w : ℕ)
    (k n : Fin 4 → ℕ)
    (hn : if positive then rectangularPositiveQuadGap (u+1) (w+1) n
      else rectangularNegativeQuadGap (u+1) (w+1) n) :
    (∫ t : ℝ, phaseActualKernelSummand T A B H f g Φ (polarPoleKiller T σ)
      α u w t k n (rectangularAFEGap positive (u+1) (w+1) n) ((c : ℂ)+(v : ℂ)*I)) =
      (T : ℂ)*(∏ j : Fin 4, (rectangularAFESmoothScale (k j) : ℂ)^(-(1/2+α j+((c : ℂ)+(v : ℂ)*I)))) *
      (phaseActualAmplifierCoefficient T f A (u+1)*phaseActualAmplifierCoefficient T g B (w+1)) *
      (∏ j : Fin 5, (rectangularSmoothBlockWeight (rectangularWeightArguments
        (phaseActualScales A B H k)
        (rectangularAFESourceTuple (u+1) (w+1) n (rectangularAFEGap positive (u+1) (w+1) n)) j) : ℂ)) *
      a03ActualTensorRawKernel (fun x => (Φ x : ℂ)) c
        (phaseActualNearTensorData T σ α v A B H k positive)
        (a03SixTensorLogPoint (a03SixSourceArguments (phaseActualScales A B H k)
          (rectangularAFESourceTuple (u+1) (w+1) n (rectangularAFEGap positive (u+1) (w+1) n)))) := by
  rw [a03_actual_kernel_time_frequency_identity hT]
  unfold a03ActualArithmeticBlockFactor
  rw [a03_actual_base_mellin_tensor_identity _ _ _ _
    (a03SixSourceArguments_actual_positive hB hH k n (by omega)
      (rectangular_AFE_gap_pos positive (u+1) (w+1) n hn))]
  unfold a03ActualTensorRawKernel a03SixGaussianFrequencyKernel
  have hfreq := a03_actual_physical_gap_frequency positive T hA hB hH σ α v k n (u+1) (w+1) (by omega) hn
  dsimp only [phaseActualNearTensorData] at hfreq ⊢
  rw [hfreq]
  rw [show -(T*Real.log (phaseActualProductRatio (u+1) (w+1) n)) =
    -T*Real.log (phaseActualProductRatio (u+1) (w+1) n) by ring]
  ring

theorem a03_actual_kernel_dual_time_raw_tensor_identity (positive : Bool) {T A B H : ℝ}
    (hT : 0 < T) (hA : 0 < A) (hB : 0 < B) (hH : 0 < H)
    (f g Φ : ℝ → ℝ) (σ α : MomentShifts) (c v : ℝ) (u w : ℕ)
    (k n : Fin 4 → ℕ)
    (hn : if positive then rectangularPositiveQuadGap (u+1) (w+1) n
      else rectangularNegativeQuadGap (u+1) (w+1) n) :
    (∫ t : ℝ, bblrDualMultiplier t (rawMomentShifts T σ)*
      phaseActualKernelSummand T A B H f g Φ (polarPoleKiller T σ)
        α u w t k n (rectangularAFEGap positive (u+1) (w+1) n) ((c : ℂ)+(v : ℂ)*I)) =
      (T : ℂ)*(∏ j : Fin 4, (rectangularAFESmoothScale (k j) : ℂ)^(-(1/2+α j+((c : ℂ)+(v : ℂ)*I)))) *
      (phaseActualAmplifierCoefficient T f A (u+1)*phaseActualAmplifierCoefficient T g B (w+1)) *
      (∏ j : Fin 5, (rectangularSmoothBlockWeight (rectangularWeightArguments
        (phaseActualScales A B H k)
        (rectangularAFESourceTuple (u+1) (w+1) n (rectangularAFEGap positive (u+1) (w+1) n)) j) : ℂ)) *
      a03ActualDualTensorRawKernel (fun x => (Φ x : ℂ)) c
        (phaseActualNearTensorData T σ α v A B H k positive)
        (a03SixTensorLogPoint (a03SixSourceArguments (phaseActualScales A B H k)
          (rectangularAFESourceTuple (u+1) (w+1) n (rectangularAFEGap positive (u+1) (w+1) n)))) := by
  rw [a03_actual_kernel_dual_time_frequency_identity hT]
  unfold a03ActualArithmeticBlockFactor
  rw [a03_actual_base_mellin_tensor_identity _ _ _ _
    (a03SixSourceArguments_actual_positive hB hH k n (by omega)
      (rectangular_AFE_gap_pos positive (u+1) (w+1) n hn))]
  unfold a03ActualDualTensorRawKernel a03SixGaussianDualFrequencyKernel
  have hfreq := a03_actual_physical_gap_frequency positive T hA hB hH σ α v k n (u+1) (w+1) (by omega) hn
  dsimp only [phaseActualNearTensorData] at hfreq ⊢
  rw [hfreq]
  rw [show -(T*Real.log (phaseActualProductRatio (u+1) (w+1) n)) =
    -T*Real.log (phaseActualProductRatio (u+1) (w+1) n) by ring]
  ring

theorem a03ActualTensorNormalizedKernel_restore {T : ℝ} (hT : 0 < T)
    (Φ : ℝ → ℂ) (c ε : ℝ) (σ α : MomentShifts) (v A B H : ℝ)
    (k : Fin 4 → ℕ) (positive : Bool) (y : A03SixTensorSpace) :
    ((T^ε : ℝ) : ℂ)*a03ActualTensorNormalizedKernel Φ c ε
      (phaseActualNearTensorData T σ α v A B H k positive) y =
      a03ActualTensorRawKernel Φ c (phaseActualNearTensorData T σ α v A B H k positive) y := by
  unfold a03ActualTensorNormalizedKernel
  change ((T^ε : ℝ) : ℂ)*((T^(-ε)) • _) = _
  rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    ← Real.rpow_add hT]
  simp

theorem a03ActualDualTensorNormalizedKernel_restore {T : ℝ} (hT : 0 < T)
    (Φ : ℝ → ℂ) (c ε : ℝ) (σ α : MomentShifts) (v A B H : ℝ)
    (k : Fin 4 → ℕ) (positive : Bool) (y : A03SixTensorSpace) :
    ((T^ε : ℝ) : ℂ)*a03ActualDualTensorNormalizedKernel Φ c ε
      (phaseActualNearTensorData T σ α v A B H k positive) y =
      a03ActualDualTensorRawKernel Φ c (phaseActualNearTensorData T σ α v A B H k positive) y := by
  unfold a03ActualDualTensorNormalizedKernel
  change ((T^ε : ℝ) : ℂ)*((T^(-ε)) • _) = _
  rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    ← Real.rpow_add hT]
  simp

end
end Sechstmoment
