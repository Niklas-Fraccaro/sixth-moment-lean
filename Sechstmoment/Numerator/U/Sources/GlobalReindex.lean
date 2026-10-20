import Sechstmoment.Numerator.U.Sources.BlockReindex
import Sechstmoment.Numerator.U.Sources.FarResidual

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem a03_source_near_partition_finite_sum (T a b s u : ℝ) (f g : ℝ→ℝ)
    (k : Fin 4→ℕ) (positive : Bool) (S : ℕ→ℕ→(Fin 4→ℕ)→ℂ) :
    (∑ j∈a03SourceAmplifierGapGrid T a b s u,
      if phaseActualActiveNearBlock T (rectangularAFESmoothScale (j 0))
        (rectangularAFESmoothScale (j 1)) (rectangularAFESmoothScale (j 2)) (T^(s-1)) f g k then
        ∑ i∈((Finset.range ⌊T^a⌋₊).product (Finset.range ⌊T^b⌋₊)).product (rectangularAFESmoothBox k),
          if (if positive then rectangularPositiveQuadGap (i.1.1+1) (i.1.2+1) i.2
            else rectangularNegativeQuadGap (i.1.1+1) (i.1.2+1) i.2) then
            (a03SourceAmplifierGapWeight (i.1.1+1) (i.1.2+1)
              (rectangularAFEGap positive (i.1.1+1) (i.1.2+1) i.2) j:ℂ)*S i.1.1 i.1.2 i.2 else 0
      else 0)=
    ∑ i∈((Finset.range ⌊T^a⌋₊).product (Finset.range ⌊T^b⌋₊)).product (rectangularAFESmoothBox k),
      if (if positive then rectangularPositiveQuadGap (i.1.1+1) (i.1.2+1) i.2
        else rectangularNegativeQuadGap (i.1.1+1) (i.1.2+1) i.2) then
        (a03ActualSourceNearPartition T a b s u f g k (i.1.1+1) (i.1.2+1)
          (rectangularAFEGap positive (i.1.1+1) (i.1.2+1) i.2):ℂ)*S i.1.1 i.1.2 i.2 else 0 := by
  simp_rw [Finset.ite_sum_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hsel : if positive then rectangularPositiveQuadGap (i.1.1+1) (i.1.2+1) i.2
    else rectangularNegativeQuadGap (i.1.1+1) (i.1.2+1) i.2
  · simp only [hsel,ite_true]
    unfold a03ActualSourceNearPartition
    rw [Complex.ofReal_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp only [Complex.ofReal_zero,zero_mul]
  · simp only [hsel,ite_false,ite_self,Finset.sum_const_zero]

theorem a03ActualSourceFiniteValue_eq_near_finite_grid {T a b : ℝ} (hT : 1<T)
    (dual : Bool) (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (σ : MomentShifts) (c s u v : ℝ) :
    a03ActualSourceFiniteValue false dual (fun x => (Φ x:ℂ)) c T a b s u v σ f g=
      ∑ positive : Bool,a03ActualNearBlockFiniteMellinGrid dual positive c T a b s u v f g Φ σ
        (a03SourceShifts dual T σ) := by
  unfold a03ActualSourceFiniteValue
  apply Finset.sum_congr rfl
  intro positive _
  unfold a03ActualSourceBlockGrid
  change (∑ i∈(a03SourceAmplifierGapGrid T a b s u).product (rectangularAFEProductScaleGrid (T^(2+u))),
    a03ActualSourceBlockValue false dual positive (fun x => (Φ x:ℂ)) c T s v σ f g i)=_
  simp only [Finset.product_eq_sprod]
  rw [Finset.sum_product (a03SourceAmplifierGapGrid T a b s u)
    (rectangularAFEProductScaleGrid (T^(2+u)))
    (fun i => a03ActualSourceBlockValue false dual positive (fun x => (Φ x:ℂ)) c T s v σ f g i),
    Finset.sum_comm]
  calc
    _=∑ k∈rectangularAFEProductScaleGrid (T^(2+u)),
      ∑ i∈((Finset.range ⌊T^a⌋₊).product (Finset.range ⌊T^b⌋₊)).product (rectangularAFESmoothBox k),
        if (if positive then rectangularPositiveQuadGap (i.1.1+1) (i.1.2+1) i.2
          else rectangularNegativeQuadGap (i.1.1+1) (i.1.2+1) i.2) then
          (a03ActualSourceNearPartition T a b s u f g k (i.1.1+1) (i.1.2+1)
            (rectangularAFEGap positive (i.1.1+1) (i.1.2+1) i.2):ℂ)*(rectangularAFESmoothWeight k i.2:ℂ)*
          ∫ t : ℝ,rectangularMomentPairWeight T f g Φ i.1.1 i.1.2 t*
            (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
            rectangularAFEMellinKernel (polarPoleKiller T σ) (a03SourceShifts dual T σ) t i.2 ((c:ℂ)+(v:ℂ)*I) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      simp_rw [a03ActualSourceBlockValue_finite_reindex hT dual positive f g Φ hf hg σ c s v]
      have he := a03_source_near_partition_finite_sum T a b s u f g k positive
        (fun p q n => (rectangularAFESmoothWeight k n:ℂ)*∫ t : ℝ,rectangularMomentPairWeight T f g Φ p q t*
          (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
          rectangularAFEMellinKernel (polarPoleKiller T σ) (a03SourceShifts dual T σ) t n ((c:ℂ)+(v:ℂ)*I))
      simpa only [mul_assoc] using he
    _=_ := by
      unfold a03ActualNearBlockFiniteMellinGrid
      simp only [Finset.product_eq_sprod,Finset.sum_product]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]

end
end Sechstmoment
