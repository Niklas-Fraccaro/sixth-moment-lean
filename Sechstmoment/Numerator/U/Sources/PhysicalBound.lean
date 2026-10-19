import Sechstmoment.Numerator.U.Sources.FactoryRestriction
import Sechstmoment.Numerator.U.ZeroModes.SixTensorZeroMode

/-! Genuine main and dual source bounds expressed entirely through the
physical tensor sum and its uncut native sorted zero mode. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology FourierTransform
open Classical
noncomputable section
set_option maxHeartbeats 3000000

/-- The genuine main source estimate with both rectangular loss budgets,
after physical reconstruction of the native GCD zero mode. -/
theorem a03_actual_main_tensor_source_physical_bound
    (hinput : SeparatedQuadraticInput) {a b εsource εkernel c κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hεsource : 0<εsource)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc 1 2)
    (hc : 0<c) (hc1 : c≤1) (hεkernel : 4*c<εkernel)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R)
    (hloss : 4*εsource+εkernel<rectangularSlack a b) :
    ∃ s u C : ℝ, 0<s ∧ s<1/2 ∧ s≤1/8 ∧ 0<u ∧ u≤1/8 ∧
      s/2+4*εsource+εkernel≤rectangularSlack a b ∧
      3*s/4+u/4+4*εsource+εkernel≤rectangularSlack a b ∧ 0≤C ∧
      ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 2/3≤A → 2/3≤B → 2/3≤H →
        ∀ k : Fin 4 → ℕ, k∈rectangularAFEProductScaleGrid (T^(2+u)) →
        phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
        ∀ σ : MomentShifts, (∀ j, ‖σ j‖≤R) →
        (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
        ∀ v : ℝ, |v|≤θ*Real.log T → ∀ positive : Bool,
        ‖a03EndpointPhysicalTensorSum (a03ActualTensorNormalizedKernel Φ c εkernel)
            positive T A B H σ (rawMomentShifts T σ) v f g k-
          a03EndpointPhysicalSortedZeroMode
            (a03ActualTensorNormalizedKernel Φ c εkernel
              (phaseActualNearTensorData T σ (rawMomentShifts T σ) v A B H k positive))
            T A B H f g k‖≤
          (C/Real.sqrt (A*B))*phaseSourceMajorant εsource
            (phaseNormalizedScales
              (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k))) := by
  obtain ⟨T0,kernels,s,u,Ccoef,Csource,normalizer,hgraph,hs,hs2,hscap,hu,hucap,
    hloss1,hloss2,hCcoef,hCsource,hm,hn,hD,_hW,hcoef,hfuture⟩ :=
    a03_actual_main_tensor_source_endpoint_sqrt_restricted hinput ha hab hlen hεsource
      f g hf hg hΦ hΦs hc hc1 hεkernel hκ hθ hR hloss
  obtain ⟨D,hD,hweight⟩ := hD
  refine ⟨s,u,Csource*Ccoef,hs,hs2,hscap,hu,hucap,hloss1,hloss2,
    mul_nonneg hCsource hCcoef,?_⟩
  filter_upwards [hfuture,
    a03_actual_endpoint_zero_integral_eventually_eq_uncut_physical ha hab hlen hs2 f g hf hg]
      with T hactual hzero
  intro A B H hA hB hH k hk hactive σ hσ hroot v hv positive
  obtain ⟨hvalid,_hphysical,_hint,_hdiff,hbound⟩ :=
    hactual A B H hA hB hH k hk hactive σ hσ hroot v hv positive
  let p := (⟨phaseActualNearTensorData T σ (rawMomentShifts T σ) v A B H k positive,hvalid⟩ :
    {p : A03NearTensorData // A03NearTensorValid T0 θ κ p})
  have hAp : 0<A := by linarith
  have hBp : 0<B := by linarith
  have hHp : 0<H := by linarith
  have heq := (hzero A B H hAp hBp hHp k hactive (kernels p)
    (a03ActualTensorNormalizedKernel Φ c εkernel p.val) (hgraph p)
    normalizer hm hn (hcoef p).1 D hD hweight).2
  rw [←heq]
  exact hbound

/-- The genuine dual source estimate with both rectangular loss budgets,
after physical reconstruction of the native GCD zero mode. -/
theorem a03_actual_dual_tensor_source_physical_bound
    (hinput : SeparatedQuadraticInput) {a b εsource εkernel c κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hεsource : 0<εsource)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc 1 2)
    (hc : 0<c) (hc1 : c≤1) (hεkernel : 4*c<εkernel)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R)
    (hloss : 4*εsource+εkernel<rectangularSlack a b) :
    ∃ s u C : ℝ, 0<s ∧ s<1/2 ∧ s≤1/8 ∧ 0<u ∧ u≤1/8 ∧
      s/2+4*εsource+εkernel≤rectangularSlack a b ∧
      3*s/4+u/4+4*εsource+εkernel≤rectangularSlack a b ∧ 0≤C ∧
      ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 2/3≤A → 2/3≤B → 2/3≤H →
        ∀ k : Fin 4 → ℕ, k∈rectangularAFEProductScaleGrid (T^(2+u)) →
        phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
        ∀ σ : MomentShifts, (∀ j, ‖σ j‖≤R) →
        (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
        ∀ v : ℝ, |v|≤θ*Real.log T → ∀ positive : Bool,
        ‖a03EndpointPhysicalTensorSum (a03ActualDualTensorNormalizedKernel Φ c εkernel)
            positive T A B H σ (bblrSixShifts (rawMomentShifts T σ) 1) v f g k-
          a03EndpointPhysicalSortedZeroMode
            (a03ActualDualTensorNormalizedKernel Φ c εkernel
              (phaseActualNearTensorData T σ (bblrSixShifts (rawMomentShifts T σ) 1) v A B H k positive))
            T A B H f g k‖≤
          (C/Real.sqrt (A*B))*phaseSourceMajorant εsource
            (phaseNormalizedScales
              (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k))) := by
  obtain ⟨T0,kernels,s,u,Ccoef,Csource,normalizer,hgraph,hs,hs2,hscap,hu,hucap,
    hloss1,hloss2,hCcoef,hCsource,hm,hn,hD,_hW,hcoef,hfuture⟩ :=
    a03_actual_dual_tensor_source_endpoint_sqrt_restricted hinput ha hab hlen hεsource
      f g hf hg hΦ hΦs hc hc1 hεkernel hκ hθ hR hloss
  obtain ⟨D,hD,hweight⟩ := hD
  refine ⟨s,u,Csource*Ccoef,hs,hs2,hscap,hu,hucap,hloss1,hloss2,
    mul_nonneg hCsource hCcoef,?_⟩
  filter_upwards [hfuture,
    a03_actual_endpoint_zero_integral_eventually_eq_uncut_physical ha hab hlen hs2 f g hf hg]
      with T hactual hzero
  intro A B H hA hB hH k hk hactive σ hσ hroot v hv positive
  obtain ⟨hvalid,_hphysical,_hint,_hdiff,hbound⟩ :=
    hactual A B H hA hB hH k hk hactive σ hσ hroot v hv positive
  let p := (⟨phaseActualNearTensorData T σ (bblrSixShifts (rawMomentShifts T σ) 1) v A B H k positive,hvalid⟩ :
    {p : A03NearTensorData // A03DualNearTensorValid T0 θ κ R p})
  have hAp : 0<A := by linarith
  have hBp : 0<B := by linarith
  have hHp : 0<H := by linarith
  have heq := (hzero A B H hAp hBp hHp k hactive (kernels p)
    (a03ActualDualTensorNormalizedKernel Φ c εkernel p.val) (hgraph p)
    normalizer hm hn (hcoef p).1 D hD hweight).2
  rw [←heq]
  exact hbound

end
end Sechstmoment
