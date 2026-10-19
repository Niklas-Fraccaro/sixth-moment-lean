import Sechstmoment.Numerator.Polar.RemainderDecay
import Sechstmoment.Numerator.U.Separation.ShapeRelativeGapScale
import Sechstmoment.Numerator.U.Separation.Tensor.Kernel

namespace Sechstmoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

def phaseActualNearTensorData (T : ℝ) (σ α : MomentShifts) (v _A B H : ℝ)
    (k : Fin 4 → ℕ) (positive : Bool) : A03NearTensorData :=
  ⟨T,σ,α,v,H/(B*(rectangularAFESmoothScale (k 2)*rectangularAFESmoothScale (k 3))),
    rectangularGapSign positive⟩

/-- Every actual retained power-near block supplies a valid physical
parameter of the actual tensor family. Its relative-gap smallness is
derived from the genuine supported near tuple. -/
theorem phase_actual_near_tensor_parameters_valid {s : ℝ} (hs : s<1)
    (T0 θ κ : ℝ) (f g : ℝ → ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 0<A → 0<B → 0<H →
      ∀ k : Fin 4 → ℕ, phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
      ∀ σ α : MomentShifts, (∀ j, ‖α j‖≤1/4) →
      (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v : ℝ, |v|≤θ*Real.log T → ∀ positive : Bool,
      A03NearTensorValid T0 θ κ (phaseActualNearTensorData T σ α v A B H k positive) := by
  filter_upwards [phase_actual_near_relative_gap_eventually_small hs
    (by norm_num : (0:ℝ)<1/100) f g,eventually_ge_atTop (1:ℝ),eventually_ge_atTop T0]
    with T hsmall hT hT0
  intro A B H hA hB hH k hactive σ α hα hσ v hv positive
  have hden : 0<B*(rectangularAFESmoothScale (k 2)*rectangularAFESmoothScale (k 3)) :=
    mul_pos hB (mul_pos (boundaryActual_scale_pos _) (boundaryActual_scale_pos _))
  have hr0 : 0≤H/(B*(rectangularAFESmoothScale (k 2)*rectangularAFESmoothScale (k 3))) :=
    div_nonneg hH.le hden.le
  have hsign : |rectangularGapSign positive|=1 := by
    cases positive <;> norm_num [rectangularGapSign]
  exact ⟨hT,hT0,hα,hσ,hv,hr0,hsmall A B H hA hB hH k hactive,hsign⟩

/-- The physical raw shifts and every one of their six functional-equation
permutations satisfy the actual tensor parameter bounds uniformly on the
bounded normalized shift domain. -/
theorem phase_actual_near_raw_tensor_parameters_valid {s R : ℝ} (hs : s<1)
    (hR : 0≤R) (T0 θ κ : ℝ) (f g : ℝ → ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 0<A → 0<B → 0<H →
      ∀ k : Fin 4 → ℕ, phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
      ∀ σ : MomentShifts, (∀ j, ‖σ j‖≤R) →
      (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v : ℝ, |v|≤θ*Real.log T → ∀ positive : Bool, ∀ m : Fin 6,
      A03NearTensorValid T0 θ κ
        (phaseActualNearTensorData T σ (bblrSixShifts (rawMomentShifts T σ) m)
          v A B H k positive) := by
  filter_upwards [phase_actual_near_tensor_parameters_valid hs T0 θ κ f g,
    rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/4)]
    with T hvalid hraw
  intro A B H hA hB hH k hactive σ hσ hκ v hv positive m
  exact hvalid A B H hA hB hH k hactive σ _
    (fun j => bblrSixShifts_norm_le _ (hraw σ hσ) m j) hκ v hv positive

theorem phase_actual_near_tensor_embedded_ratio (T : ℝ) (σ α : MomentShifts)
    (v A B H : ℝ) (k : Fin 4 → ℕ) (positive : Bool) :
    (phaseActualNearTensorData T σ α v A B H k positive).r=
      (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).H/
        ((boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).B*
          (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).N) :=
  (phase_boundary_relative_gap_scale (boundaryActualFlags k) (phaseActualScales A B H k)).symm

end
end Sechstmoment
