import Sechstmoment.Numerator.U.ZeroModes.Ratio.DiscreteFrontJoin
import Sechstmoment.Numerator.U.ZeroModes.Ratio.SourceMomentJoin

/-! The actual ratio tensor at the literal discrete source coordinate is
exactly the ratio-weighted finite AFE time source. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem a03_ratio_exp_log_scaled {M N x y : ℝ}
    (hM : 0<M) (hN : 0<N) (hx : 0<x) (hy : 0<y) :
    Real.exp (Real.log (M/N)+Real.log (x/M)-Real.log (y/N))=x/y := by
  rw [Real.exp_sub,Real.exp_add,Real.exp_log (div_pos hM hN),
    Real.exp_log (div_pos hx hM),Real.exp_log (div_pos hy hN)]
  field_simp

theorem a03RatioEuclideanMultiplier_source_logPoint (α : MomentShifts)
    (q : QuadraticScales) (n : Fin 7→ℕ) (hM₁ : 0<q.M₁) (hM₂ : 0<q.M₂)
    (hN₁ : 0<q.N₁) (hN₂ : 0<q.N₂)
    (hn₂ : 0<n 2) (hn₃ : 0<n 3) (hn₄ : 0<n 4) (hn₅ : 0<n 5) :
    a03RatioEuclideanMultiplier α (Real.log (q.M₁/q.M₂)) (Real.log (q.N₁/q.N₂))
      (a03SixTensorLogPoint (a03SixSourceArguments q n))=
      a03ZeroModeRatioFourWeight (a03ZeroModeRatioWeight α) false false (n 2) (n 3) (n 4) (n 5) := by
  rw [a03RatioEuclideanMultiplier_eq_partition]
  simp [a03SixTensorLogPoint_apply,a03SixSourceArguments_eq,a03ZeroModeRatioFourWeight]
  rw [a03_ratio_exp_log_scaled hM₁ hM₂ (by exact_mod_cast hn₂) (by exact_mod_cast hn₃),
    a03_ratio_exp_log_scaled hN₁ hN₂ (by exact_mod_cast hn₄) (by exact_mod_cast hn₅)]

theorem a03_actual_kernel_source_time_raw_identity (dual positive : Bool) {T A B H : ℝ}
    (hT : 0<T) (hA : 0<A) (hB : 0<B) (hH : 0<H) (f g Φ : ℝ→ℝ)
    (σ α : MomentShifts) (c v : ℝ) (u w : ℕ) (k n : Fin 4→ℕ)
    (hn : if positive then rectangularPositiveQuadGap (u+1) (w+1) n
      else rectangularNegativeQuadGap (u+1) (w+1) n) :
    (∫ t : ℝ,(if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
      phaseActualKernelSummand T A B H f g Φ (polarPoleKiller T σ)
        α u w t k n (rectangularAFEGap positive (u+1) (w+1) n) ((c:ℂ)+(v:ℂ)*I))=
      (T:ℂ)*a03SourceMellinScaleFactor c v α k*
      (phaseActualAmplifierCoefficient T f A (u+1)*phaseActualAmplifierCoefficient T g B (w+1))*
      (∏ j : Fin 5,(rectangularSmoothBlockWeight (rectangularWeightArguments (phaseActualScales A B H k)
        (rectangularAFESourceTuple (u+1) (w+1) n (rectangularAFEGap positive (u+1) (w+1) n)) j):ℂ))*
      a03SourceRawKernel dual (fun x => (Φ x:ℂ)) c (phaseActualNearTensorData T σ α v A B H k positive)
        (a03SixTensorLogPoint (a03SixSourceArguments (phaseActualScales A B H k)
          (rectangularAFESourceTuple (u+1) (w+1) n (rectangularAFEGap positive (u+1) (w+1) n)))) := by
  cases dual
  · simpa only [a03SourceMellinScaleFactor,a03SourceRawKernel,Bool.false_eq_true,ite_false,one_mul] using
      a03_actual_kernel_time_raw_tensor_identity positive hT hA hB hH f g Φ σ α c v u w k n hn
  · simpa only [a03SourceMellinScaleFactor,a03SourceRawKernel,ite_true] using
      a03_actual_kernel_dual_time_raw_tensor_identity positive hT hA hB hH f g Φ σ α c v u w k n hn

/-- Natural ratio offsets restore the actual ratio-weighted source time
integral, with all finite amplifier and AFE supports retained. -/
theorem a03_actual_ratio_raw_physical_source_finite_reindex {a b T A B H : ℝ}
    (hT : 1<T) (hA : 0<A) (hB : 0<B) (hH : 0<H) (f g Φ : ℝ→ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (σ α : MomentShifts) (c v : ℝ) (k : Fin 4→ℕ) (dual positive : Bool) :
    (T:ℂ)*a03SourceMellinScaleFactor c v α k*
      a03EndpointPhysicalTensorSum (a03RatioSourceRawFamilyKernel dual (fun x => (Φ x:ℂ)) c
        (Real.log (rectangularAFESmoothScale (k 0)/rectangularAFESmoothScale (k 1)))
        (Real.log (rectangularAFESmoothScale (k 2)/rectangularAFESmoothScale (k 3))))
        positive T A B H σ α v f g k=
      ∑ i∈((Finset.range ⌊T^a⌋₊).product (Finset.range ⌊T^b⌋₊)).product (rectangularAFESmoothBox k),
        if (if positive then rectangularPositiveQuadGap (i.1.1+1) (i.1.2+1) i.2
          else rectangularNegativeQuadGap (i.1.1+1) (i.1.2+1) i.2) then
          a03ZeroModeRatioFourWeight (a03ZeroModeRatioWeight (rawMomentShifts T σ)) false false
            (i.2 0+1) (i.2 1+1) (i.2 2+1) (i.2 3+1)*
            ∫ t : ℝ,(if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
              phaseActualKernelSummand T A B H f g Φ (polarPoleKiller T σ)
                α i.1.1 i.1.2 t k i.2 (rectangularAFEGap positive (i.1.1+1) (i.1.2+1) i.2)
                  ((c:ℂ)+(v:ℂ)*I) else 0 := by
  unfold a03EndpointPhysicalTensorSum
  rw [a03_actual_source_signed_finite_reindex hT hA hB hH f g hf hg k positive,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hs : if positive then rectangularPositiveQuadGap (i.1.1+1) (i.1.2+1) i.2
    else rectangularNegativeQuadGap (i.1.1+1) (i.1.2+1) i.2
  · simp only [hs,ite_true]
    unfold a03RatioSourceRawFamilyKernel a03ActualRatioTensorRawKernel
    dsimp only [phaseActualNearTensorData]
    have he := a03RatioEuclideanMultiplier_source_logPoint (rawMomentShifts T σ)
      (phaseActualScales A B H k) (rectangularAFESourceTuple (i.1.1+1) (i.1.2+1) i.2
        (rectangularAFEGap positive (i.1.1+1) (i.1.2+1) i.2))
      (boundaryActual_scale_pos _) (boundaryActual_scale_pos _) (boundaryActual_scale_pos _) (boundaryActual_scale_pos _)
      (by simp [rectangularAFESourceTuple]) (by simp [rectangularAFESourceTuple])
      (by simp [rectangularAFESourceTuple]) (by simp [rectangularAFESourceTuple])
    dsimp only [phaseActualScales] at he ⊢
    erw [he,a03_actual_kernel_source_time_raw_identity dual positive (zero_lt_one.trans hT) hA hB hH
      f g Φ σ α c v i.1.1 i.1.2 k i.2 hs]
    simp [rectangularAFESourceTuple,phaseActualScales,phaseActualNearTensorData,Nat.cast_add,Nat.cast_one]
    ring
  · simp only [hs,ite_false,mul_zero]

/-- Exact attachment of the source-estimate good mask to the finite
ratio time block. The same actual primary Gaussian weight is retained. -/
theorem a03ActualRatioSourceBlockValue_eq_time_block {a b T : ℝ} (hT : 1<T)
    (dual positive : Bool) (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (σ α : MomentShifts) (c s εsource v : ℝ)
    (j : Fin 3→ℕ) (k : Fin 4→ℕ) :
    a03ActualRatioSourceBlockValue false dual positive (fun x => (Φ x:ℂ)) c T s εsource v σ α f g (j,k)=
      if a03ActualRatioSourceGoodBlock T s εsource f g (j,k) then
        a03ActualRatioTimeBlock false false dual positive (a03ZeroModeRatioWeight (rawMomentShifts T σ))
          c T a b s v σ α f g Φ j k else 0 := by
  unfold a03ActualRatioSourceBlockValue
  dsimp only
  by_cases hgood : a03ActualRatioSourceGoodBlock T s εsource f g (j,k)
  · simp only [hgood,ite_true,Bool.false_eq_true,ite_false]
    erw [a03_actual_ratio_raw_physical_source_finite_reindex hT (boundaryActual_scale_pos _)
      (boundaryActual_scale_pos _) (boundaryActual_scale_pos _) f g Φ hf hg σ α c v k dual positive]
    unfold a03ActualRatioTimeBlock
    simp only [hgood.1,ite_true]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hs : if positive then rectangularPositiveQuadGap (i.1.1+1) (i.1.2+1) i.2
      else rectangularNegativeQuadGap (i.1.1+1) (i.1.2+1) i.2
    · simp only [hs,ite_true]
      rw [a03_actual_localized_time_integral_eq_amp_gap_weight]
      ring
    · simp only [hs,ite_false]
  · simp only [hgood,ite_false]

end
end Sechstmoment
