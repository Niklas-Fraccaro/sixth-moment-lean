import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Sechstmoment.Numerator.U.Separation.ActualTensorMellinIntegrability
import Sechstmoment.Numerator.U.Sources.MomentJoin

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03SourceMellinScaleFactor_continuous (c : ℝ) (α : MomentShifts) (k : Fin 4→ℕ) :
    Continuous (fun v : ℝ => a03SourceMellinScaleFactor c v α k) := by
  unfold a03SourceMellinScaleFactor
  apply continuous_finsetProd
  intro j _
  apply Continuous.const_cpow
  · fun_prop
  · exact Or.inl (Complex.ofReal_ne_zero.mpr (boundaryActual_scale_pos (k j)).ne')

theorem a03_actual_raw_tensor_mellin_integrableOn (dual : Bool)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c e κ θ R s : ℝ} (hc : 0<c) (hc1 : c≤1) (he : 4*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hs : s<1) (f g : ℝ→ℝ) :
    ∀ᶠ T : ℝ in atTop,∀ A B H : ℝ,0<A → 0<B → 0<H →
      ∀ k : Fin 4→ℕ,phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
      ∀ σ : MomentShifts,(∀ j,‖σ j‖≤R) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ positive : Bool,
      IntegrableOn (fun v : ℝ => a03EndpointPhysicalTensorSum (a03SourceRawKernel dual Φ c)
        positive T A B H σ (a03SourceShifts dual T σ) v f g k) (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      IntegrableOn (fun v : ℝ => a03EndpointPhysicalSortedZeroMode
        (a03SourceRawKernel dual Φ c (phaseActualNearTensorData T σ (a03SourceShifts dual T σ) v A B H k positive))
        T A B H f g k) (Icc (-θ*Real.log T) (θ*Real.log T)) := by
  cases dual
  · simpa [a03SourceRawKernel,a03SourceShifts] using
      a03_actual_main_raw_tensor_mellin_integrableOn hΦ hΦs hc hc1 he hκ hθ hR hs f g
  · simpa [a03SourceRawKernel,a03SourceShifts] using
      a03_actual_dual_raw_tensor_mellin_integrableOn hΦ hΦs hc hc1 he hκ hθ hR hs f g

theorem a03_actual_source_finite_values_integrableOn (dual : Bool)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c e κ θ R s : ℝ} (hc : 0<c) (hc1 : c≤1) (he : 4*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hs : s<1)
    (a b u : ℝ) (f g : ℝ→ℝ) :
    ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,(∀ j,‖σ j‖≤R) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ zero : Bool,
      IntegrableOn (fun v : ℝ => a03ActualSourceFiniteValue zero dual Φ c T a b s u v σ f g)
        (Icc (-θ*Real.log T) (θ*Real.log T)) := by
  filter_upwards [a03_actual_raw_tensor_mellin_integrableOn dual hΦ hΦs hc hc1 he hκ hθ hR hs f g]
    with T hactual
  intro σ hσ hroot zero
  unfold a03ActualSourceFiniteValue
  apply integrable_finsetSum
  intro positive _
  apply integrable_finsetSum
  intro i _
  unfold a03ActualSourceBlockValue
  dsimp only
  by_cases hactive : phaseActualActiveNearBlock T (rectangularAFESmoothScale (i.1 0))
    (rectangularAFESmoothScale (i.1 1)) (rectangularAFESmoothScale (i.1 2)) (T^(s-1)) f g i.2
  · simp only [hactive,ite_true]
    have hi := hactual _ _ _ (boundaryActual_scale_pos (i.1 0)) (boundaryActual_scale_pos (i.1 1))
      (boundaryActual_scale_pos (i.1 2)) i.2 hactive σ hσ hroot positive
    have hw : Continuous (fun v : ℝ => (T:ℂ)*a03SourceMellinScaleFactor c v (a03SourceShifts dual T σ) i.2) :=
      (a03SourceMellinScaleFactor_continuous c (a03SourceShifts dual T σ) i.2).const_mul _
    cases zero
    · simp only [Bool.false_eq_true,ite_false]
      exact IntegrableOn.continuousOn_mul hw.continuousOn hi.1 isCompact_Icc
    · simp only [ite_true]
      exact IntegrableOn.continuousOn_mul hw.continuousOn hi.2 isCompact_Icc
  · simp only [hactive,ite_false]
    exact integrable_zero _ _ _

theorem a03_actual_source_physical_moment_sub_Gamma_zero (dual : Bool)
    (hinput : SeparatedQuadraticInput) {a b εsource εkernel c κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hεsource : 0<εsource)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    (hc : 0<c) (hc1 : c≤1) (hεkernel : 4*c<εkernel)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R)
    (hloss : 4*εsource+εkernel<rectangularSlack a b) :
    ∃ s u : ℝ,0<s ∧ s<1/2 ∧ s≤1/8 ∧ 0<u ∧ u≤1/8 ∧
      ∀ σ : MomentShifts,(∀ j,‖σ j‖≤R) →
        (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
        (fun T : ℝ => a03ActualSourcePhysicalMoment dual Φ c T a b s u θ σ f g-
          a03ActualSourceGammaZeroMoment dual Φ c T a b s u θ σ f g)=o[atTop] (fun T : ℝ => T) := by
  obtain ⟨s,u,C,hs,hs2,hscap,hu,hucap,_hloss1,_hloss2,_hC,_hbound,hsmall⟩ :=
    a03_actual_source_physical_error_aggregate dual hinput ha hab hlen hεsource f g hf hg
      hΦ hΦs hc hc1 hεkernel hκ hθ hR hloss
  refine ⟨s,u,hs,hs2,hscap,hu,hucap,?_⟩
  intro σ hσ hroot
  apply (hsmall σ hσ hroot).congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [a03_actual_source_finite_values_integrableOn dual hΦ hΦs hc hc1 hεkernel hκ hθ hR
    (hs2.trans (by norm_num)) a b u f g,eventually_gt_atTop (0:ℝ)] with T hi hT
  exact a03ActualSourceErrorMoment_eq_physical_sub_zero hT dual Φ c εkernel a b s u θ σ f g
    (hi σ hσ hroot false) (hi σ hσ hroot true)

end
end Sechstmoment
