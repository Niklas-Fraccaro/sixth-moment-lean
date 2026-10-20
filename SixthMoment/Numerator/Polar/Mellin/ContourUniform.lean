import SixthMoment.Numerator.Polar.ContourShift
import SixthMoment.Numerator.Polar.RemainderDecay


namespace SixthMoment

open Real Complex Filter Set
open scoped BigOperators Topology

noncomputable section

theorem purePolarRoot_ne_zero_of_normalized_gap {T κ : ℝ}
    (hT : 1 < T) (hκ : 0 < κ) (σ : MomentShifts) (k : PurePolarIndex)
    (hgap : κ ≤ ‖Source.normalizedPurePolarRoot σ k‖) :
    purePolarRoot T σ k ≠ 0 := by
  rw [Source.purePolarRoot_normalized]
  apply div_ne_zero
  · exact norm_pos_iff.mp (hκ.trans_le hgap)
  · exact Complex.ofReal_ne_zero.mpr (Real.log_pos hT).ne'

theorem polarMellinWeightedKernel_contour_shift_explicit_residue
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) {δ x : ℝ} {u v : ℂ}
    (hδ : 0 < δ) (hδ1 : δ < 1/4) (hx : 0 < x)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ δ/4)
    (hu : δ ≤ u.re) (hv : δ ≤ v.re)
    (hρ : ∀ ij : Fin 2 × Fin 2, purePolarRoot T σ (m,ij) ≠ 0) :
    Source.verticalIntegral 1 (polarMellinWeightedKernel T σ m u v x) =
      polarArithmeticEntangledFactor (Source.bblrSixShifts (rawMomentShifts T σ) m) u v 0*
        purePolarZetaProduct T σ m 0+polarMellinRemainderIntegral T σ m u v x δ := by
  rw [polarMellinWeightedKernel_contour_shift T σ m hδ hδ1 hx hα hu hv hρ,
    polarMellinRemovedKernel_zero T σ m u v hρ]

theorem polarMellinWeightedKernel_uniform_eventually_power_decay {R δ κ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 < δ) (hδ1 : δ < 1/4) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ σ : MomentShifts, (∀ j : Fin 4, ‖σ j‖ ≤ R) →
      (∀ k : PurePolarIndex, κ ≤ ‖Source.normalizedPurePolarRoot σ k‖) →
      ∀ (m : Fin 6) (u v : ℂ), δ ≤ u.re → δ ≤ v.re →
      ∀ t : ℝ, T ≤ t →
        ‖Source.verticalIntegral 1 (polarMellinWeightedKernel T σ m u v (t/(2*Real.pi)))-
          polarMellinRemovedKernel T σ m u v 0‖ ≤ C*T^(-δ/2) := by
  obtain ⟨C,hC,hbound⟩ :=
    polarMellinRemainderIntegral_uniform_eventually_power_decay hR hδ hδ1 hκ
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (1:ℝ),
    rawMomentShifts_uniform_eventually_small hR (show 0 < δ/4 by linarith)]
    with T hB hT hraw
  intro σ hσ hgap m u v hu hv t ht
  have hx : 0 < t/(2*Real.pi) := div_pos (by linarith) (by positivity)
  have hρ (ij : Fin 2 × Fin 2) : purePolarRoot T σ (m,ij) ≠ 0 :=
    purePolarRoot_ne_zero_of_normalized_gap hT hκ σ (m,ij) (hgap (m,ij))
  rw [polarMellinWeightedKernel_contour_shift T σ m hδ hδ1 hx (hraw σ hσ) hu hv hρ,
    add_sub_cancel_left]
  exact hB σ hσ hgap m u v hu hv t ht

theorem polarMellinWeightedKernel_explicit_residue_uniform_eventually_power_decay
    {R δ κ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hδ1 : δ < 1/4) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ σ : MomentShifts, (∀ j : Fin 4, ‖σ j‖ ≤ R) →
      (∀ k : PurePolarIndex, κ ≤ ‖Source.normalizedPurePolarRoot σ k‖) →
      ∀ (m : Fin 6) (u v : ℂ), δ ≤ u.re → δ ≤ v.re →
      ∀ t : ℝ, T ≤ t →
        ‖Source.verticalIntegral 1 (polarMellinWeightedKernel T σ m u v (t/(2*Real.pi)))-
          polarArithmeticEntangledFactor (Source.bblrSixShifts (rawMomentShifts T σ) m) u v 0*
            purePolarZetaProduct T σ m 0‖ ≤ C*T^(-δ/2) := by
  obtain ⟨C,hC,hbound⟩ :=
    polarMellinWeightedKernel_uniform_eventually_power_decay hR hδ hδ1 hκ
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (1:ℝ)] with T hB hT
  intro σ hσ hgap m u v hu hv t ht
  have hρ (ij : Fin 2 × Fin 2) : purePolarRoot T σ (m,ij) ≠ 0 :=
    purePolarRoot_ne_zero_of_normalized_gap hT hκ σ (m,ij) (hgap (m,ij))
  rw [← polarMellinRemovedKernel_zero T σ m u v hρ]
  exact hB σ hσ hgap m u v hu hv t ht

end

end SixthMoment
