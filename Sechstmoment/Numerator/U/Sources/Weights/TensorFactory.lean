import Sechstmoment.Numerator.U.Separation.Tensor.DualSource
import Sechstmoment.Numerator.U.Separation.Tensor.Source
import Sechstmoment.Numerator.U.Sources.Weights.DualTensorParameters

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology FourierTransform
noncomputable section
set_option maxHeartbeats 2000000

def phaseActualSixFourierSourceClasses (ε K : ℝ) (bounds : ℕ → ℝ)
    (normalizer : A03SixTensorSpace → ℝ) (T A B H : ℝ) (f g : ℝ → ℝ)
    (k : Fin 4 → ℕ) : Prop :=
  ∀ ν : A03SixTensorSpace, ∀ component : Fin 5 → Bool,
    let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
    QuadraticAdmissible ε 1 K bounds (phaseNormalizedScales q)
      (phaseNormalizedAlpha q (boundaryActualAlpha T A f k) (a03SixActualBoundaryBeta T B g k ν))
      (phaseNormalizedBeta q (boundaryActualAlpha T A f k) (a03SixActualBoundaryBeta T B g k ν))
      (rectangularRealComponent (phaseNormalizedWeights q (a03SixTensorWeight normalizer ν)) component)

theorem phase_actual_main_tensor_source_factory
    {a b εsource εkernel c κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hεsource : 0<εsource)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc 1 2)
    (hc : 0<c) (hc1 : c≤1) (hεkernel : 4*c<εkernel)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ T0 : ℝ, ∃ kernels : {p : A03NearTensorData // A03NearTensorValid T0 θ κ p} →
        SchwartzMap A03SixTensorSpace ℂ,
      ∃ s u K C : ℝ, ∃ normalizer : A03SixTensorSpace → ℝ, ∃ bounds : ℕ → ℝ,
      (∀ p y, kernels p y=a03TensorLogCutoff y*a03ActualTensorNormalizedKernel Φ c εkernel p.val y) ∧
      0<s ∧ s<1/2 ∧ 0<u ∧ 1≤K ∧ 0≤C ∧ Measurable normalizer ∧
      (∀ ν, 0<normalizer ν) ∧ (∀ j, 0≤bounds j) ∧
      (∀ ν j, RectangularComplexWeight (a03SixTensorWeight normalizer ν j)) ∧
      (∀ j ν i x, ‖iteratedDeriv j (a03SixTensorWeight normalizer ν i) x‖≤bounds j) ∧
      (∀ p, Integrable (a03SixTensorCoefficient (kernels p) normalizer) ∧
        (∫ ν, ‖a03SixTensorCoefficient (kernels p) normalizer ν‖)≤C) ∧
      (∀ p (x : Fin 6 → ℝ), (∀ j, x j ∈ Icc (1 : ℝ) 2) →
        (∏ j : Fin 5, (rectangularSmoothBlockWeight (x j.succ):ℂ))*
          a03ActualTensorNormalizedKernel Φ c εkernel p.val (a03SixTensorLogPoint x)=
          ∫ ν, a03SixTensorCoefficient (kernels p) normalizer ν*
            ((x 0:ℂ)^a03SixTensorExponent ν 0*
              ∏ j, a03SixTensorWeight normalizer ν j (x j.succ))) ∧
      ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 2/3≤A → 2/3≤B → 2/3≤H →
        ∀ k : Fin 4 → ℕ, k∈rectangularAFEProductScaleGrid (T^(2+u)) →
        phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
        ∀ σ : MomentShifts, (∀ j, ‖σ j‖≤R) →
        (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
        ∀ v : ℝ, |v|≤θ*Real.log T → ∀ positive : Bool,
        A03NearTensorValid T0 θ κ
          (phaseActualNearTensorData T σ (rawMomentShifts T σ) v A B H k positive) ∧
          phaseActualSixFourierSourceClasses εsource K bounds normalizer T A B H f g k := by
  obtain ⟨T0,kernels,s,u,K,C,normalizer,bounds,hkeq,hs,hs2,hu,hK,hC,hm,hn,
    hbounds,hW,hd,hcoef,heq,hadm⟩ :=
    a03_actual_full_power_near_source_admissibility ha hab hlen hεsource f g hf hg hΦ hΦs
      hc hc1 hεkernel hκ hθ
  refine ⟨T0,kernels,s,u,K,C,normalizer,bounds,hkeq,hs,hs2,hu,hK,hC,hm,hn,
    hbounds,hW,hd,hcoef,heq,?_⟩
  have hs1 : s<1 := lt_trans hs2 (by norm_num)
  filter_upwards [hadm,phase_actual_near_main_tensor_parameters_valid hs1 hR T0 θ κ f g]
    with T hsource hvalid
  intro A B H hA hB hH k hk hactive σ hσ hroot v hv positive
  have hAp : 0<A := by linarith
  have hBp : 0<B := by linarith
  have hHp : 0<H := by linarith
  exact ⟨hvalid A B H hAp hBp hHp k hactive σ hσ hroot v hv positive,
    hsource A B H hA hB hH k hk hactive⟩

theorem phase_actual_dual_tensor_source_factory
    {a b εsource εkernel c κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hεsource : 0<εsource)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc 1 2)
    (hc : 0<c) (hc1 : c≤1) (hεkernel : 4*c<εkernel)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ T0 : ℝ, ∃ kernels : {p : A03NearTensorData // A03DualNearTensorValid T0 θ κ R p} →
        SchwartzMap A03SixTensorSpace ℂ,
      ∃ s u K C : ℝ, ∃ normalizer : A03SixTensorSpace → ℝ, ∃ bounds : ℕ → ℝ,
      (∀ p y, kernels p y=a03TensorLogCutoff y*a03ActualDualTensorNormalizedKernel Φ c εkernel p.val y) ∧
      0<s ∧ s<1/2 ∧ 0<u ∧ 1≤K ∧ 0≤C ∧ Measurable normalizer ∧
      (∀ ν, 0<normalizer ν) ∧ (∀ j, 0≤bounds j) ∧
      (∀ ν j, RectangularComplexWeight (a03SixTensorWeight normalizer ν j)) ∧
      (∀ j ν i x, ‖iteratedDeriv j (a03SixTensorWeight normalizer ν i) x‖≤bounds j) ∧
      (∀ p, Integrable (a03SixTensorCoefficient (kernels p) normalizer) ∧
        (∫ ν, ‖a03SixTensorCoefficient (kernels p) normalizer ν‖)≤C) ∧
      (∀ p (x : Fin 6 → ℝ), (∀ j, x j ∈ Icc (1 : ℝ) 2) →
        (∏ j : Fin 5, (rectangularSmoothBlockWeight (x j.succ):ℂ))*
          a03ActualDualTensorNormalizedKernel Φ c εkernel p.val (a03SixTensorLogPoint x)=
          ∫ ν, a03SixTensorCoefficient (kernels p) normalizer ν*
            ((x 0:ℂ)^a03SixTensorExponent ν 0*
              ∏ j, a03SixTensorWeight normalizer ν j (x j.succ))) ∧
      ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 2/3≤A → 2/3≤B → 2/3≤H →
        ∀ k : Fin 4 → ℕ, k∈rectangularAFEProductScaleGrid (T^(2+u)) →
        phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
        ∀ σ : MomentShifts, (∀ j, ‖σ j‖≤R) →
        (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
        ∀ v : ℝ, |v|≤θ*Real.log T → ∀ positive : Bool,
        A03DualNearTensorValid T0 θ κ R
          (phaseActualNearTensorData T σ (bblrSixShifts (rawMomentShifts T σ) 1) v A B H k positive) ∧
          phaseActualSixFourierSourceClasses εsource K bounds normalizer T A B H f g k := by
  obtain ⟨T0,kernels,s,u,K,C,normalizer,bounds,hkeq,hs,hs2,hu,hK,hC,hm,hn,
    hbounds,hW,hd,hcoef,heq,hadm⟩ :=
    a03_actual_dual_full_power_near_source_admissibility ha hab hlen hεsource f g hf hg hΦ hΦs
      hc hc1 hεkernel hκ hθ hR
  refine ⟨T0,kernels,s,u,K,C,normalizer,bounds,hkeq,hs,hs2,hu,hK,hC,hm,hn,
    hbounds,hW,hd,hcoef,heq,?_⟩
  have hs1 : s<1 := lt_trans hs2 (by norm_num)
  filter_upwards [hadm,phase_actual_near_dual_tensor_parameters_valid hs1 hR T0 θ κ f g]
    with T hsource hvalid
  intro A B H hA hB hH k hk hactive σ hσ hroot v hv positive
  have hAp : 0<A := by linarith
  have hBp : 0<B := by linarith
  have hHp : 0<H := by linarith
  exact ⟨hvalid A B H hAp hBp hHp k hactive σ hσ hroot v hv positive,
    hsource A B H hA hB hH k hk hactive⟩

end
end Sechstmoment
