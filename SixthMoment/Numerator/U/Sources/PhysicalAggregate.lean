import SixthMoment.Numerator.U.Sources.ErrorAggregate
import SixthMoment.Numerator.U.Sources.PhysicalBound

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_actual_tensor_source_physical_bound (dual : Bool)
    (hinput : SeparatedQuadraticInput) {a b εsource εkernel c κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hεsource : 0<εsource)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    (hc : 0<c) (hc1 : c≤1) (hεkernel : 4*c<εkernel)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R)
    (hloss : 4*εsource+εkernel<rectangularSlack a b) :
    ∃ s u C : ℝ, 0<s ∧ s<1/2 ∧ s≤1/8 ∧ 0<u ∧ u≤1/8 ∧
      s/2+4*εsource+εkernel≤rectangularSlack a b ∧
      3*s/4+u/4+4*εsource+εkernel≤rectangularSlack a b ∧ 0≤C ∧
      ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 2/3≤A → 2/3≤B → 2/3≤H →
        ∀ k : Fin 4→ℕ, k∈rectangularAFEProductScaleGrid (T^(2+u)) →
        phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
        ∀ σ : MomentShifts, (∀ j,‖σ j‖≤R) →
        (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
        ∀ v : ℝ, |v|≤θ*Real.log T → ∀ positive : Bool,
        ‖a03EndpointPhysicalTensorSum (a03SourceKernel dual Φ c εkernel)
            positive T A B H σ (a03SourceShifts dual T σ) v f g k-
          a03EndpointPhysicalSortedZeroMode
            (a03SourceKernel dual Φ c εkernel
              (phaseActualNearTensorData T σ (a03SourceShifts dual T σ) v A B H k positive))
            T A B H f g k‖≤
          (C/Real.sqrt (A*B))*phaseSourceMajorant εsource
            (phaseNormalizedScales (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k))) := by
  cases dual
  · simpa [a03SourceKernel,a03SourceShifts] using
      a03_actual_main_tensor_source_physical_bound hinput ha hab hlen hεsource
        f g hf hg hΦ hΦs hc hc1 hεkernel hκ hθ hR hloss
  · simpa [a03SourceKernel,a03SourceShifts] using
      a03_actual_dual_tensor_source_physical_bound hinput ha hab hlen hεsource
        f g hf hg hΦ hΦs hc hc1 hεkernel hκ hθ hR hloss

theorem a03_actual_source_physical_error_aggregate (dual : Bool)
    (hinput : SeparatedQuadraticInput) {a b εsource εkernel c κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hεsource : 0<εsource)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    (hc : 0<c) (hc1 : c≤1) (hεkernel : 4*c<εkernel)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R)
    (hloss : 4*εsource+εkernel<rectangularSlack a b) :
    ∃ s u C : ℝ, 0<s ∧ s<1/2 ∧ s≤1/8 ∧ 0<u ∧ u≤1/8 ∧
      s/2+4*εsource+εkernel≤rectangularSlack a b ∧
      3*s/4+u/4+4*εsource+εkernel≤rectangularSlack a b ∧ 0≤C ∧
      (∀ᶠ T : ℝ in atTop, ∀ σ : MomentShifts, (∀ j,‖σ j‖≤R) →
        (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
        ‖a03ActualSourceErrorMoment dual Φ c εkernel T a b s u θ σ f g‖≤
          C*T^εkernel*a03ActualSourceGlobalMajorant T a b s u εsource θ f g) ∧
      ∀ σ : MomentShifts, (∀ j,‖σ j‖≤R) →
        (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
        (fun T : ℝ => a03ActualSourceErrorMoment dual Φ c εkernel T a b s u θ σ f g)=o[atTop]
          (fun T : ℝ => T) := by
  obtain ⟨s,u,C,hs,hs2,hscap,hu,hucap,hloss1,hloss2,hC,hphysical⟩ :=
    a03_actual_tensor_source_physical_bound dual hinput ha hab hlen hεsource f g hf hg
      hΦ hΦs hc hc1 hεkernel hκ hθ hR hloss
  let D := C*a03SourceMellinBound R u
  have hD : 0≤D := by dsimp [D,a03SourceMellinBound]; positivity
  have hbound : ∀ᶠ T : ℝ in atTop, ∀ σ : MomentShifts, (∀ j,‖σ j‖≤R) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ‖a03ActualSourceErrorMoment dual Φ c εkernel T a b s u θ σ f g‖≤
        D*T^εkernel*a03ActualSourceGlobalMajorant T a b s u εsource θ f g := by
    filter_upwards [hphysical,eventually_ge_atTop (1:ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hphysical hT hlog
    intro σ hσ hroot
    apply a03_actual_source_error_moment_bound hT hθ dual Φ c σ f g
    intro v hv positive i hi
    have hk := (Finset.mem_product.mp hi).2
    apply a03_actual_source_restored_block_bound (zero_lt_one.trans_le hT) hlog hR hc.le hc1 hC
      dual positive Φ σ hσ v f g i hk
    intro hactive
    exact hphysical _ _ _ (boundaryActual_scale_ge_two_thirds (i.1 0))
      (boundaryActual_scale_ge_two_thirds (i.1 1)) (boundaryActual_scale_ge_two_thirds (i.1 2))
      i.2 hk hactive σ hσ hroot v hv positive
  refine ⟨s,u,D,hs,hs2,hscap,hu,hucap,hloss1,hloss2,hD,hbound,?_⟩
  intro σ hσ hroot
  have hsmall := a03_actual_source_restored_global_majorant_isLittleO
    ha hab hlen hs.le hscap hu hucap hεsource.le hθ hloss1 hloss2 f g hf hg
  apply (IsBigO.of_bound D ?_).trans_isLittleO hsmall
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ)] with T hbound hT
  have hfinite : 0≤a03ActualSourceFiniteMajorant T a b s u εsource f g :=
    Finset.sum_nonneg (fun i _ => a03ActualSourceBlockMajorant_nonneg (zero_le_one.trans hT) s εsource f g i)
  have hglobal : 0≤a03ActualSourceGlobalMajorant T a b s u εsource θ f g := by
    unfold a03ActualSourceGlobalMajorant
    exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by norm_num) hθ)
      (Real.log_nonneg hT))) hfinite
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hT) εkernel) hglobal)]
  simpa only [mul_assoc] using hbound σ hσ hroot

end
end SixthMoment
