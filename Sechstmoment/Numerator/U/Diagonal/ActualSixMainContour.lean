import Sechstmoment.Numerator.U.Diagonal.ActualMellinContourAdapter


namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 0

theorem actualFiniteAmplifiedDiagonal_eq_shiftedProfiles {T a b t δ : ℝ}
    (hT : 1 < T) (ht : 0 < t) (hδ : 0 < δ) (hδ1 : δ < 1/4)
    (σ : MomentShifts) (m : Fin 6)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ δ/4)
    (hρ : ∀ ij : Fin 2 × Fin 2, purePolarRoot T σ (m,ij) ≠ 0)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    (∑ n₁ ∈ Finset.Icc 1 ⌊T^a⌋₊, ∑ n₂ ∈ Finset.Icc 1 ⌊T^b⌋₊,
      (f (Real.log n₁/Real.log T):ℂ)*(g (Real.log n₂/Real.log T):ℂ)*
        bblrDiagonalTerm (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) m) n₁ n₂ t) =
      ((Real.log T:ℂ)/(2*π))^2*∫ y : ℝ × ℝ,
        (actualProfileTransformLine (fun x => (f x:ℂ)) (Real.log T) δ y.1*
          actualProfileTransformLine (fun x => (g x:ℂ)) (Real.log T) δ y.2)*
          (polarMellinRemovedKernel T σ m ((δ:ℂ)+(y.1:ℂ)*I) ((δ:ℂ)+(y.2:ℂ)*I) 0+
            polarMellinRemainderIntegral T σ m ((δ:ℂ)+(y.1:ℂ)*I)
              ((δ:ℂ)+(y.2:ℂ)*I) (t/(2*π)) δ) ∂(volume.prod volume) := by
  rw [← actualAmplifier_sum_eq_finite hT f g hf hg]
  exact actualAmplifiedDiagonal_eq_shiftedProfiles ht (Real.log_pos hT) hδ hδ1 T σ m hα hρ
    (hf.2.1.comp_left (show Complex.ofReal 0=0 from rfl))
    (Complex.ofRealCLM.contDiff.comp hf.1)
    (hg.2.1.comp_left (show Complex.ofReal 0=0 from rfl))
    (Complex.ofRealCLM.contDiff.comp hg.1)

theorem bblrSixMainTerms_eq_shiftedProfiles {T a b δ : ℝ}
    (hT : 1 < T) (hδ : 0 < δ) (hδ1 : δ < 1/4) (σ : MomentShifts)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ δ/4)
    (hρ : ∀ k : PurePolarIndex, purePolarRoot T σ k ≠ 0)
    (f g Φ : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    bblrSixMainTerms T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ =
      ∫ t : ℝ, ∑ m : Fin 6,
        (Φ (t/T):ℂ)*(t/(2*π):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) m)*
          (((Real.log T:ℂ)/(2*π))^2*∫ y : ℝ × ℝ,
            (actualProfileTransformLine (fun x => (f x:ℂ)) (Real.log T) δ y.1*
              actualProfileTransformLine (fun x => (g x:ℂ)) (Real.log T) δ y.2)*
              (polarMellinRemovedKernel T σ m ((δ:ℂ)+(y.1:ℂ)*I) ((δ:ℂ)+(y.2:ℂ)*I) 0+
                polarMellinRemainderIntegral T σ m ((δ:ℂ)+(y.1:ℂ)*I)
                  ((δ:ℂ)+(y.2:ℂ)*I) (t/(2*π)) δ) ∂(volume.prod volume)) := by
  have hδle : δ ≤ 1 := by linarith
  have hG := polarPoleKiller_BBLREntireWeight T σ (rawMomentShifts T σ)
  rw [bblrSixMainTerms_eq_actualMellinEuler hT hδ hδle _ _ hG hα f g Φ hf hg hΦ]
  apply integral_congr_ae
  filter_upwards [] with t
  apply Finset.sum_congr rfl
  intro m hm
  by_cases ht : 0 < t
  · have hinit := actualFiniteAmplifiedDiagonal_eq_MellinEuler hT ht.ne' hδ hδle
      (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) m) hG f g hf hg
      (bblrSixShifts_norm_le _ hα m)
    rw [← hinit,actualFiniteAmplifiedDiagonal_eq_shiftedProfiles hT ht hδ hδ1 σ m hα
      (fun ij => hρ (m,ij)) f g hf hg]
  · have hΦzero : Φ (t/T)=0 := by
      by_contra hn
      have hlow := (hΦ.2 (subset_tsupport Φ hn)).1
      have hb : T ≤ t := by simpa only [one_mul] using (le_div_iff₀ (zero_lt_one.trans hT)).mp hlow
      linarith
    simp only [hΦzero,Complex.ofReal_zero,zero_mul]

end
end Sechstmoment
