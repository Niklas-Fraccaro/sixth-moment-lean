import SixthMoment.Numerator.U.Separation.Tensor.DualKernel
import SixthMoment.Numerator.U.Sources.Weights.TensorParameters

namespace SixthMoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem phase_actual_near_dual_tensor_parameters_valid {s R : ℝ} (hs : s<1)
    (hR : 0≤R) (T0 θ κ : ℝ) (f g : ℝ → ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 0<A → 0<B → 0<H →
      ∀ k : Fin 4 → ℕ, phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
      ∀ σ : MomentShifts, (∀ j, ‖σ j‖≤R) →
      (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v : ℝ, |v|≤θ*Real.log T → ∀ positive : Bool,
      A03DualNearTensorValid T0 θ κ R
        (phaseActualNearTensorData T σ (bblrSixShifts (rawMomentShifts T σ) 1)
          v A B H k positive) := by
  filter_upwards [phase_actual_near_raw_tensor_parameters_valid hs hR T0 θ κ f g]
    with T hvalid
  intro A B H hA hB hH k hactive σ hσ hκ v hv positive
  exact ⟨hvalid A B H hA hB hH k hactive σ hσ hκ v hv positive 1,hσ⟩

theorem phase_actual_near_main_tensor_parameters_valid {s R : ℝ} (hs : s<1)
    (hR : 0≤R) (T0 θ κ : ℝ) (f g : ℝ → ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 0<A → 0<B → 0<H →
      ∀ k : Fin 4 → ℕ, phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
      ∀ σ : MomentShifts, (∀ j, ‖σ j‖≤R) →
      (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v : ℝ, |v|≤θ*Real.log T → ∀ positive : Bool,
      A03NearTensorValid T0 θ κ
        (phaseActualNearTensorData T σ (rawMomentShifts T σ) v A B H k positive) := by
  filter_upwards [phase_actual_near_raw_tensor_parameters_valid hs hR T0 θ κ f g]
    with T hvalid
  intro A B H hA hB hH k hactive σ hσ hκ v hv positive
  simpa only [bblrSixShifts, Matrix.cons_val_zero] using
    hvalid A B H hA hB hH k hactive σ hσ hκ v hv positive 0

end
end SixthMoment
