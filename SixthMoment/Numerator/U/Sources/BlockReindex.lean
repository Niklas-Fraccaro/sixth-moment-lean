import SixthMoment.Numerator.U.Sources.FiniteReindex
import SixthMoment.Numerator.U.Sources.MomentJoin
import SixthMoment.Numerator.U.Sources.NearPartition

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology FourierTransform
open Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem a03_actual_physical_source_finite_reindex {a b T A B H : ℝ}
    (hT : 1<T) (hA : 0<A) (hB : 0<B) (hH : 0<H)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (σ : MomentShifts) (c v : ℝ) (k : Fin 4→ℕ) (dual positive : Bool) :
    (T:ℂ)*a03SourceMellinScaleFactor c v (a03SourceShifts dual T σ) k*
      a03EndpointPhysicalTensorSum (a03SourceRawKernel dual (fun x => (Φ x:ℂ)) c)
        positive T A B H σ (a03SourceShifts dual T σ) v f g k=
      ∑ i∈((Finset.range ⌊T^a⌋₊).product (Finset.range ⌊T^b⌋₊)).product (rectangularAFESmoothBox k),
        if (if positive then rectangularPositiveQuadGap (i.1.1+1) (i.1.2+1) i.2
          else rectangularNegativeQuadGap (i.1.1+1) (i.1.2+1) i.2) then
          ∫ t : ℝ, (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
            phaseActualKernelSummand T A B H f g Φ (polarPoleKiller T σ)
              (a03SourceShifts dual T σ) i.1.1 i.1.2 t k i.2
              (rectangularAFEGap positive (i.1.1+1) (i.1.2+1) i.2) ((c:ℂ)+(v:ℂ)*I) else 0 := by
  cases dual
  · simpa only [a03SourceRawKernel,a03SourceShifts,a03SourceMellinScaleFactor,
      Bool.false_eq_true,ite_false,one_mul] using
      a03_actual_main_physical_source_finite_reindex hT hA hB hH f g Φ hf hg σ
        (rawMomentShifts T σ) c v k positive
  · simpa only [a03SourceRawKernel,a03SourceShifts,a03SourceMellinScaleFactor,ite_true] using
      a03_actual_dual_physical_source_finite_reindex hT hA hB hH f g Φ hf hg σ
        (bblrSixShifts (rawMomentShifts T σ) 1) c v k positive

theorem a03_actual_localized_time_integral_eq_amp_gap_weight
    (dual : Bool) (T : ℝ) (f g Φ : ℝ→ℝ) (σ α : MomentShifts)
    (u w : ℕ) (j : Fin 3→ℕ) (k n : Fin 4→ℕ) (h : ℕ) (z : ℂ) :
    (∫ t : ℝ, (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
      phaseActualKernelSummand T (rectangularAFESmoothScale (j 0))
        (rectangularAFESmoothScale (j 1)) (rectangularAFESmoothScale (j 2)) f g Φ
        (polarPoleKiller T σ) α u w t k n h z)=
      (a03SourceAmplifierGapWeight (u+1) (w+1) h j:ℂ)*(rectangularAFESmoothWeight k n:ℂ)*
        ∫ t : ℝ, rectangularMomentPairWeight T f g Φ u w t*
          (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
            rectangularAFEMellinKernel (polarPoleKiller T σ) α t n z := by
  have he : (a03SourceAmplifierGapWeight (u+1) (w+1) h j:ℂ)=
      (rectangularSmoothBlockWeight ((u+1:ℝ)/rectangularAFESmoothScale (j 0)):ℂ)*
      (rectangularSmoothBlockWeight ((w+1:ℝ)/rectangularAFESmoothScale (j 1)):ℂ)*
      (rectangularSmoothBlockWeight ((h:ℝ)/rectangularAFESmoothScale (j 2)):ℂ) := by
    simp [a03SourceAmplifierGapWeight,Fin.prod_univ_three]
  rw [he,←integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  unfold phaseActualKernelSummand
  ring

theorem a03ActualSourceBlockValue_finite_reindex {a b T : ℝ} (hT : 1<T)
    (dual positive : Bool) (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (σ : MomentShifts) (c s v : ℝ)
    (j : Fin 3→ℕ) (k : Fin 4→ℕ) :
    a03ActualSourceBlockValue false dual positive (fun x => (Φ x:ℂ)) c T s v σ f g (j,k)=
      if phaseActualActiveNearBlock T (rectangularAFESmoothScale (j 0))
        (rectangularAFESmoothScale (j 1)) (rectangularAFESmoothScale (j 2)) (T^(s-1)) f g k then
        ∑ i∈((Finset.range ⌊T^a⌋₊).product (Finset.range ⌊T^b⌋₊)).product (rectangularAFESmoothBox k),
          if (if positive then rectangularPositiveQuadGap (i.1.1+1) (i.1.2+1) i.2
            else rectangularNegativeQuadGap (i.1.1+1) (i.1.2+1) i.2) then
            (a03SourceAmplifierGapWeight (i.1.1+1) (i.1.2+1)
              (rectangularAFEGap positive (i.1.1+1) (i.1.2+1) i.2) j:ℂ)*
              (rectangularAFESmoothWeight k i.2:ℂ)*
                ∫ t : ℝ, rectangularMomentPairWeight T f g Φ i.1.1 i.1.2 t*
                  (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
                    rectangularAFEMellinKernel (polarPoleKiller T σ) (a03SourceShifts dual T σ) t i.2
                      ((c:ℂ)+(v:ℂ)*I) else 0
      else 0 := by
  unfold a03ActualSourceBlockValue
  simp only [Bool.false_eq_true,ite_false]
  by_cases hactive : phaseActualActiveNearBlock T (rectangularAFESmoothScale (j 0))
    (rectangularAFESmoothScale (j 1)) (rectangularAFESmoothScale (j 2)) (T^(s-1)) f g k
  · simp only [hactive,ite_true]
    rw [a03_actual_physical_source_finite_reindex hT (boundaryActual_scale_pos _)
      (boundaryActual_scale_pos _) (boundaryActual_scale_pos _) f g Φ hf hg σ c v k dual positive]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hsel : if positive then rectangularPositiveQuadGap (i.1.1+1) (i.1.2+1) i.2
      else rectangularNegativeQuadGap (i.1.1+1) (i.1.2+1) i.2
    · simp only [hsel,ite_true]
      exact a03_actual_localized_time_integral_eq_amp_gap_weight dual T f g Φ σ
        (a03SourceShifts dual T σ) i.1.1 i.1.2 j k i.2 _ _
    · simp only [hsel,ite_false]
  · simp only [hactive,ite_false]

end
end SixthMoment
