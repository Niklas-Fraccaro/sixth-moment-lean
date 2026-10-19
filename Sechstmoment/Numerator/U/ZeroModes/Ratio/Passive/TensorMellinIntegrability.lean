import Sechstmoment.Numerator.U.Sources.PassiveActualTensorParameters

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_actual_passive_ratio_tensor_mellin_integrableOn
    (dual : Bool) {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c e κ θ R s : ℝ} (hc : 0<c) (hc1 : c≤1) (he : 12*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hs : s<1) (f g : ℝ→ℝ) :
    ∀ᶠ T : ℝ in atTop,∀ A B H : ℝ,0<A → 0<B → 0<H →
      ∀ k : Fin 4→ℕ,A03ActualPassiveNearZeroBlock T A B H (T^(s-1)) f g k →
      ∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) → (∀ j,‖α j‖≤1/4) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ positive : Bool,∀ tM tN : ℝ,
      IntegrableOn (fun v : ℝ => a03EndpointPhysicalTensorSum
        (a03RatioSourceFamilyKernel dual Φ c e tM tN) positive T A B H σ α v f g k)
        (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      IntegrableOn (fun v : ℝ => a03EndpointPhysicalUnsortedZeroMode
        (a03RatioSourceFamilyKernel dual Φ c e tM tN (phaseActualNearTensorData T σ α v A B H k positive))
        T A B H f g k) (Icc (-θ*Real.log T) (θ*Real.log T)) := by
  obtain ⟨T0,kernels,hgraph,hseminorm⟩ :=
    a03_actual_ratio_tensor_bounded_schwartz_family dual hΦ hΦs hc hc1 he hκ hθ hR
  obtain ⟨C,hC,hCb⟩ := hseminorm 0 0
  filter_upwards [a03_actual_passive_tensor_parameters_valid hs T0 θ κ f g,
    rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/4)] with T hvalid hraw
  intro A B H hA hB hH k hactive σ α hσ hα hroot positive tM tN
  have hm : StronglyMeasurable (fun p : ℝ×A03SixTensorSpace =>
      a03RatioSourceFamilyKernel dual Φ c e tM tN (phaseActualNearTensorData T σ α p.1 A B H k positive) p.2) := by
    simpa only [phaseActualNearTensorData] using
      a03_actual_ratio_tensor_kernel_mellin_joint_stronglyMeasurable dual hc T e
        (H/(B*(rectangularAFESmoothScale (k 2)*rectangularAFESmoothScale (k 3))))
        (rectangularGapSign positive) tM tN σ α hα (hraw σ hσ) Φ hΦ.continuous
  have hb : ∀ v∈Icc (-θ*Real.log T) (θ*Real.log T),∀ y,
      ‖a03TensorLogCutoff y*a03RatioSourceFamilyKernel dual Φ c e tM tN
        (phaseActualNearTensorData T σ α v A B H k positive) y‖≤C := by
    intro v hv y
    have hvabs : |v|≤θ*Real.log T := abs_le.mpr (by simpa only [mem_Icc,neg_mul] using hv)
    let p : {p : A03RatioTensorData // A03RatioTensorValid T0 θ κ R p} :=
      ⟨⟨phaseActualNearTensorData T σ α v A B H k positive,tM,tN⟩,
        ⟨hvalid A B H hA hB hH k hactive σ α hα hroot v hvabs positive,hσ⟩⟩
    change ‖a03TensorLogCutoff y*a03ActualRatioTensorNormalizedKernel dual Φ c e p.val y‖≤C
    rw [←hgraph p y]
    exact (SchwartzMap.norm_le_seminorm ℂ (kernels p) y).trans (hCb p)
  exact ⟨a03EndpointPhysicalTensorSum_mellin_integrableOn_of_cutoff_bound _
      positive T A B H σ α f g k hm hC hb,
    a03SixTensorPhysicalZeroMode_mellin_integrableOn_of_cutoff_bound _ hm hC hb false false
      (phaseActualScales A B H k) hB (boundaryActual_scale_pos (k 1)) _ _
      (phaseActualAmplifierCoefficient_support T g hB)⟩

end
end Sechstmoment
