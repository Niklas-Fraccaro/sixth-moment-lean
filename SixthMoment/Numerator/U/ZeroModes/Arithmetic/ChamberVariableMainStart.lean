import SixthMoment.Numerator.U.ZeroModes.Contour.VariableStart
import SixthMoment.Numerator.U.ZeroModes.FourChamberMainPair
import SixthMoment.Numerator.U.ZeroModes.PolarChamberGap

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 1000000

theorem a03PhysicalChamberMainContour_start_eq_initial {T δ κ c₀ : ℝ}
    (hT : 1<T) (hδ : 0<δ) (hδ1 : δ<1/4) (hκ : 0<κ) (hc₀ : c₀∈Icc δ 1)
    (σ : MomentShifts) (hα : ∀ j,‖rawMomentShifts T σ j‖≤δ/4)
    (hroot : ∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    (dual m n : Bool) (N₁ N₂ : ℕ) (A B : ℕ→ℂ) :
    verticalIntegral c₀ (a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ A B
      (a03ZeroModeChamberShifts m n (if dual then bblrSixShifts (rawMomentShifts T σ) 1
        else rawMomentShifts T σ)))=
    verticalIntegral 1 (a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ A B
      (a03ZeroModeChamberShifts m n (if dual then bblrSixShifts (rawMomentShifts T σ) 1
        else rawMomentShifts T σ))) := by
  let τ := a03SourceNormalizedChamber dual m n σ
  have hτ : ∀ j,‖rawMomentShifts T τ j‖≤δ/4 := by
    rw [show rawMomentShifts T τ=a03ZeroModeChamberShifts m n
      (if dual then bblrSixShifts (rawMomentShifts T σ) 1 else rawMomentShifts T σ)
      from a03SourceNormalizedChamber_raw dual m n T σ]
    cases dual
    · exact a03ZeroMode_chamber_norm_le m n hα
    · exact a03ZeroMode_chamber_norm_le m n (bblrSixShifts_norm_le _ hα 1)
  have hτρ := a03NormalizedPureRoot_gap_chambers σ hroot dual m n
  have hρ (j : Fin 2) : a03ZeroModeMainPoleRoot T τ j≠0 := by
    change purePolarRoot T τ (a03ZeroModeMainPoleIndex j)≠0
    rw [purePolarRoot_normalized]
    exact div_ne_zero (norm_pos_iff.mp (hκ.trans_le (hτρ (a03ZeroModeMainPoleIndex j))))
      (Complex.ofReal_ne_zero.mpr (Real.log_pos hT).ne')
  have hρb (j : Fin 2) : ‖a03ZeroModeMainPoleRoot T τ j‖≤δ/4 :=
    purePolarRoot_norm_le_of_rawShifts hτ (a03ZeroModeMainPoleIndex j)
  have hG : polarPoleKiller T τ=polarPoleKiller T σ := by
    funext z
    dsimp only [τ,a03SourceNormalizedChamber]
    rw [a03PolarPoleKiller_chamber]
    cases dual
    · rfl
    · exact a03PolarPoleKiller_six T σ 1 z
  have he := a03ZeroModeMainContour_start_eq_initial τ N₁ N₂ A B hδ hδ1 hc₀ hρ hρb
  rw [hG,a03SourceNormalizedChamber_raw] at he
  exact he

theorem a03PhysicalChamberMainContour_start_pair_eq_crossed {T δ κ c₀ c₁ : ℝ}
    (hT : 1<T) (hδ : 0<δ) (hδ1 : δ<1/4) (hκ : 0<κ)
    (hc₀ : c₀∈Icc δ 1) (hc₁ : c₁∈Icc δ 1)
    (σ : MomentShifts) (hα : ∀ j,‖rawMomentShifts T σ j‖≤δ/4)
    (hroot : ∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    (m n : Bool) (N₁ N₂ : ℕ) (A B : ℕ→ℂ) :
    a03ZeroModeContourPrefactor (a03ZeroModeChamberShifts m n (rawMomentShifts T σ))*
      (verticalIntegral c₀ (a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ A B
        (a03ZeroModeChamberShifts m n (rawMomentShifts T σ)))+
      verticalIntegral c₁ (a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ A B
        (a03ZeroModeChamberShifts (!n) (!m) (bblrSixShifts (rawMomentShifts T σ) 1))))=
      a03CrossedArithmeticSum N₁ N₂ A B (a03ZeroModeChamberShifts m n (rawMomentShifts T σ)) := by
  have h₀ := a03PhysicalChamberMainContour_start_eq_initial hT hδ hδ1 hκ hc₀ σ hα hroot
    false m n N₁ N₂ A B
  have h₁ := a03PhysicalChamberMainContour_start_eq_initial hT hδ hδ1 hκ hc₁ σ hα hroot
    true (!n) (!m) N₁ N₂ A B
  simp only [Bool.false_eq_true,ite_false,ite_true] at h₀ h₁
  rw [h₀,h₁]
  exact a03ChamberMainContour_initial_pair_eq_crossed hT hδ hδ1 hκ m n σ hα hroot N₁ N₂ A B

end
end SixthMoment
