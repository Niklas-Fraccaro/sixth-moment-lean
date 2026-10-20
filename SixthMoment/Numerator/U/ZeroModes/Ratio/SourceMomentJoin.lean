import SixthMoment.Numerator.U.Sources.MomentIntegrability
import SixthMoment.Numerator.U.ZeroModes.Ratio.SourceErrorAggregate
import SixthMoment.Numerator.U.ZeroModes.Ratio.TensorMellinIntegrability

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03ActualRatioSourceBlockValue (zeroMode dual positive : Bool) (Φ : ℝ→ℂ)
    (c T s εsource v : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ)
    (i : (Fin 3→ℕ)×(Fin 4→ℕ)) : ℂ :=
  let A := rectangularAFESmoothScale (i.1 0)
  let B := rectangularAFESmoothScale (i.1 1)
  let H := rectangularAFESmoothScale (i.1 2)
  let native := phaseActualScales A B H i.2
  let F := a03RatioSourceRawFamilyKernel dual Φ c (Real.log (native.M₁/native.M₂)) (Real.log (native.N₁/native.N₂))
  let p := phaseActualNearTensorData T σ α v A B H i.2 positive
  if a03ActualRatioSourceGoodBlock T s εsource f g i then
    (T:ℂ)*a03SourceMellinScaleFactor c v α i.2*
      (if zeroMode then a03EndpointPhysicalUnsortedZeroMode (F p) T A B H f g i.2
        else a03EndpointPhysicalTensorSum F positive T A B H σ α v f g i.2)
  else 0

def a03ActualRatioSourceFiniteValue (zeroMode dual : Bool) (Φ : ℝ→ℂ)
    (c T a b s u εsource v : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∑ positive : Bool,∑ i∈a03ActualSourceBlockGrid (T^a) (T^b)
    (8*T^((a+b)/2+s+u/2)) (T^(2+u)),a03ActualRatioSourceBlockValue zeroMode dual positive Φ c T s εsource v σ α f g i

def a03ActualRatioSourceValueMoment (zeroMode dual : Bool) (Φ : ℝ→ℂ)
    (c T a b s u εsource θ : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∫ v in Icc (-θ*Real.log T) (θ*Real.log T),
    a03ActualRatioSourceFiniteValue zeroMode dual Φ c T a b s u εsource v σ α f g

theorem a03_actual_ratio_raw_tensor_mellin_integrableOn
    (dual : Bool) {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c e κ θ R s : ℝ} (hc : 0<c) (hc1 : c≤1) (he : 12*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hs : s<1) (f g : ℝ→ℝ) :
    ∀ᶠ T : ℝ in atTop,∀ A B H : ℝ,0<A → 0<B → 0<H →
      ∀ k : Fin 4→ℕ,phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
      ∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) → (∀ j,‖α j‖≤1/4) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ positive : Bool,∀ tM tN : ℝ,
      IntegrableOn (fun v : ℝ => a03EndpointPhysicalTensorSum
        (a03RatioSourceRawFamilyKernel dual Φ c tM tN) positive T A B H σ α v f g k)
        (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      IntegrableOn (fun v : ℝ => a03EndpointPhysicalUnsortedZeroMode
        (a03RatioSourceRawFamilyKernel dual Φ c tM tN (phaseActualNearTensorData T σ α v A B H k positive))
        T A B H f g k) (Icc (-θ*Real.log T) (θ*Real.log T)) := by
  filter_upwards [a03_actual_ratio_tensor_mellin_integrableOn dual hΦ hΦs hc hc1 he hκ hθ hR hs f g,
    eventually_gt_atTop (0:ℝ)] with T hint hT
  intro A B H hA hB hH k hactive σ α hσ hα hroot positive tM tN
  obtain ⟨hi,hz⟩ := hint A B H hA hB hH k hactive σ α hσ hα hroot positive tM tN
  have heq (v : ℝ) (y : A03SixTensorSpace) :
      a03RatioSourceRawFamilyKernel dual Φ c tM tN (phaseActualNearTensorData T σ α v A B H k positive) y=
        ((T^e:ℝ):ℂ)*a03RatioSourceFamilyKernel dual Φ c e tM tN (phaseActualNearTensorData T σ α v A B H k positive) y :=
    (a03ActualRatioTensorNormalizedKernel_restore hT dual Φ c e _ rfl y).symm
  have hsum (v : ℝ) : ((T^e:ℝ):ℂ)*a03EndpointPhysicalTensorSum
      (a03RatioSourceFamilyKernel dual Φ c e tM tN) positive T A B H σ α v f g k=
      a03EndpointPhysicalTensorSum (a03RatioSourceRawFamilyKernel dual Φ c tM tN) positive T A B H σ α v f g k := by
    unfold a03EndpointPhysicalTensorSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs
    · rw [heq]
      ring
    · ring
  have hzero (v : ℝ) : ((T^e:ℝ):ℂ)*a03EndpointPhysicalUnsortedZeroMode
      (a03RatioSourceFamilyKernel dual Φ c e tM tN (phaseActualNearTensorData T σ α v A B H k positive)) T A B H f g k=
      a03EndpointPhysicalUnsortedZeroMode
      (a03RatioSourceRawFamilyKernel dual Φ c tM tN (phaseActualNearTensorData T σ α v A B H k positive)) T A B H f g k := by
    have heqfun : a03RatioSourceRawFamilyKernel dual Φ c tM tN
        (phaseActualNearTensorData T σ α v A B H k positive)=
        fun y => ((T^e:ℝ):ℂ)*a03RatioSourceFamilyKernel dual Φ c e tM tN
          (phaseActualNearTensorData T σ α v A B H k positive) y := funext (heq v)
    rw [heqfun,a03EndpointPhysicalUnsortedZeroMode_const_mul]
  exact ⟨(hi.const_mul ((T^e:ℝ):ℂ)).congr (ae_of_all _ hsum),
    (hz.const_mul ((T^e:ℝ):ℂ)).congr (ae_of_all _ hzero)⟩

theorem a03_actual_ratio_source_finite_values_integrableOn (dual : Bool)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c e κ θ R s : ℝ} (hc : 0<c) (hc1 : c≤1) (he : 12*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hs : s<1)
    (a b u εsource : ℝ) (f g : ℝ→ℝ) :
    ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) → (∀ j,‖α j‖≤1/4) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ zeroMode : Bool,
      IntegrableOn (fun v : ℝ => a03ActualRatioSourceFiniteValue zeroMode dual Φ c T a b s u εsource v σ α f g)
        (Icc (-θ*Real.log T) (θ*Real.log T)) := by
  filter_upwards [a03_actual_ratio_raw_tensor_mellin_integrableOn dual hΦ hΦs hc hc1 he hκ hθ hR hs f g]
    with T hactual
  intro σ α hσ hα hroot zeroMode
  unfold a03ActualRatioSourceFiniteValue
  apply integrable_finsetSum
  intro positive _
  apply integrable_finsetSum
  intro i _
  unfold a03ActualRatioSourceBlockValue
  dsimp only
  by_cases hgood : a03ActualRatioSourceGoodBlock T s εsource f g i
  · simp only [hgood,ite_true]
    have hi := hactual _ _ _ (boundaryActual_scale_pos (i.1 0)) (boundaryActual_scale_pos (i.1 1))
      (boundaryActual_scale_pos (i.1 2)) i.2 hgood.1 σ α hσ hα hroot positive
      (Real.log ((phaseActualScales (rectangularAFESmoothScale (i.1 0)) (rectangularAFESmoothScale (i.1 1))
        (rectangularAFESmoothScale (i.1 2)) i.2).M₁/(phaseActualScales (rectangularAFESmoothScale (i.1 0))
        (rectangularAFESmoothScale (i.1 1)) (rectangularAFESmoothScale (i.1 2)) i.2).M₂))
      (Real.log ((phaseActualScales (rectangularAFESmoothScale (i.1 0)) (rectangularAFESmoothScale (i.1 1))
        (rectangularAFESmoothScale (i.1 2)) i.2).N₁/(phaseActualScales (rectangularAFESmoothScale (i.1 0))
        (rectangularAFESmoothScale (i.1 1)) (rectangularAFESmoothScale (i.1 2)) i.2).N₂))
    have hw : Continuous (fun v : ℝ => (T:ℂ)*a03SourceMellinScaleFactor c v α i.2) :=
      (a03SourceMellinScaleFactor_continuous c α i.2).const_mul _
    cases zeroMode
    · simp only [Bool.false_eq_true,ite_false]
      exact IntegrableOn.continuousOn_mul hw.continuousOn hi.1 isCompact_Icc
    · simp only [ite_true]
      exact IntegrableOn.continuousOn_mul hw.continuousOn hi.2 isCompact_Icc
  · simp only [hgood,ite_false]
    exact integrable_zero _ _ _

theorem a03ActualRatioSourceFiniteError_eq_physical_sub_zero {T : ℝ} (hT : 0<T)
    (dual : Bool) (Φ : ℝ→ℂ) (c e a b s u εsource v : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ) :
    a03ActualRatioSourceFiniteError dual Φ c e T a b s u εsource v σ α f g=
      a03ActualRatioSourceFiniteValue false dual Φ c T a b s u εsource v σ α f g-
        a03ActualRatioSourceFiniteValue true dual Φ c T a b s u εsource v σ α f g := by
  unfold a03ActualRatioSourceFiniteError a03ActualRatioSourceFiniteValue
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro positive _
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [a03ActualRatioSourceBlockError_eq_raw hT]
  unfold a03ActualRatioSourceBlockValue
  dsimp only
  simp only [Bool.false_eq_true,ite_false,ite_true]
  split_ifs <;> ring

theorem a03ActualRatioSourceErrorMoment_eq_physical_sub_zero {T : ℝ} (hT : 0<T)
    (dual : Bool) (Φ : ℝ→ℂ) (c e a b s u εsource θ : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ)
    (hi : IntegrableOn (fun v => a03ActualRatioSourceFiniteValue false dual Φ c T a b s u εsource v σ α f g)
      (Icc (-θ*Real.log T) (θ*Real.log T)))
    (hz : IntegrableOn (fun v => a03ActualRatioSourceFiniteValue true dual Φ c T a b s u εsource v σ α f g)
      (Icc (-θ*Real.log T) (θ*Real.log T))) :
    a03ActualRatioSourceErrorMoment dual Φ c e T a b s u εsource θ σ α f g=
      a03ActualRatioSourceValueMoment false dual Φ c T a b s u εsource θ σ α f g-
        a03ActualRatioSourceValueMoment true dual Φ c T a b s u εsource θ σ α f g := by
  unfold a03ActualRatioSourceErrorMoment a03ActualRatioSourceValueMoment
  simp_rw [a03ActualRatioSourceFiniteError_eq_physical_sub_zero hT]
  exact integral_sub hi hz

end
end SixthMoment
