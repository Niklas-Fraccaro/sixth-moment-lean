import SixthMoment.Numerator.U.Separation.SixTensorBoundaryTransport
import SixthMoment.Numerator.U.Separation.Tensor.FiniteSource
import SixthMoment.Numerator.U.Sources.Weights.TensorFactory

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology FourierTransform
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03EndpointNormalizedSum (positive : Bool) (T A B H : ℝ) (f g : ℝ → ℝ)
    (k : Fin 4 → ℕ) (normalizer : A03SixTensorSpace → ℝ) (ν : A03SixTensorSpace) : ℂ :=
  let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
  rectangularComplexQuadraticSum (phaseNormalizedSign q positive) (phaseNormalizedScales q)
    (phaseNormalizedAlpha q (boundaryActualAlpha T A f k) (a03SixActualBoundaryBeta T B g k ν))
    (phaseNormalizedBeta q (boundaryActualAlpha T A f k) (a03SixActualBoundaryBeta T B g k ν))
    (phaseNormalizedWeights q (a03SixTensorWeight normalizer ν))

def a03EndpointNormalizedZeroMode (T A B H : ℝ) (f g : ℝ → ℝ)
    (k : Fin 4 → ℕ) (normalizer : A03SixTensorSpace → ℝ) (ν : A03SixTensorSpace) : ℂ :=
  let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
  rectangularComplexZeroMode (phaseNormalizedScales q)
    (phaseNormalizedAlpha q (boundaryActualAlpha T A f k) (a03SixActualBoundaryBeta T B g k ν))
    (phaseNormalizedBeta q (boundaryActualAlpha T A f k) (a03SixActualBoundaryBeta T B g k ν))
    (phaseNormalizedWeights q (a03SixTensorWeight normalizer ν))

def a03EndpointNormalizedDiscrepancy (positive : Bool) (T A B H : ℝ) (f g : ℝ → ℝ)
    (k : Fin 4 → ℕ) (normalizer : A03SixTensorSpace → ℝ) (ν : A03SixTensorSpace) : ℂ :=
  let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
  rectangularComplexDiscrepancy (phaseNormalizedSign q positive) (phaseNormalizedScales q)
    (phaseNormalizedAlpha q (boundaryActualAlpha T A f k) (a03SixActualBoundaryBeta T B g k ν))
    (phaseNormalizedBeta q (boundaryActualAlpha T A f k) (a03SixActualBoundaryBeta T B g k ν))
    (phaseNormalizedWeights q (a03SixTensorWeight normalizer ν))

def a03EndpointPhysicalTensorSum (F : A03NearTensorData → A03SixTensorSpace → ℂ)
    (positive : Bool) (T A B H : ℝ) (σ α : MomentShifts) (v : ℝ) (f g : ℝ → ℝ)
    (k : Fin 4 → ℕ) : ℂ :=
  ∑ n ∈ quadraticIndexSet (phaseActualScales A B H k), if signedQuadraticRelation positive n then
    phaseActualAmplifierCoefficient T f A (n 0)*phaseActualAmplifierCoefficient T g B (n 1)*
      (∏ j : Fin 5, (rectangularSmoothBlockWeight
        (rectangularWeightArguments (phaseActualScales A B H k) n j) : ℂ))*
      F (phaseActualNearTensorData T σ α v A B H k positive)
        (a03SixTensorLogPoint (a03SixSourceArguments (phaseActualScales A B H k) n)) else 0

theorem a03_actual_source_class_superposition
    (hinput : SeparatedQuadraticInput) {ε K : ℝ} (hε : 0<ε) (hK : 1≤K)
    (bounds : ℕ → ℝ) (hbounds : ∀ j, 0≤bounds j)
    (normalizer : A03SixTensorSpace → ℝ) (hm : Measurable normalizer)
    (hW : ∀ ν j, RectangularComplexWeight (a03SixTensorWeight normalizer ν j)) :
    ∃ C : ℝ, 0≤C ∧ ∀ T A B H f g k
      (c : A03SixTensorSpace → ℂ), Integrable c →
      phaseActualSixFourierSourceClasses (DivisorProof.inputExponent ε 1) K bounds normalizer T A B H f g k → 0<B →
      ∀ positive : Bool,
      Integrable (fun ν => c ν*a03EndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν) ∧
      ‖∫ ν, c ν*a03EndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν‖ ≤
        (C*phaseSourceMajorant ε (phaseNormalizedScales
          (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k))))*
          (∫ ν, ‖c ν‖) := by
  obtain ⟨C,hC,hbound⟩ := phase_BBLRv1_integrable_component_source
    hinput hε (by norm_num : (0 : ℝ)<1) hK bounds hbounds
  refine ⟨C,hC,?_⟩
  intro T A B H f g k c hc hadm hB positive
  let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
  let α := fun _ : A03SixTensorSpace => boundaryActualAlpha T A f k
  let β := fun ν => a03SixActualBoundaryBeta T B g k ν
  have hα : ∀ n, Measurable (fun ν => α ν n) := fun _ => measurable_const
  have hβ : ∀ n, Measurable (fun ν => β ν n) :=
    a03SixActualBoundaryBeta_measurable T B g k hB
  exact hbound A03SixTensorSpace volume (phaseNormalizedScales q)
    (fun ν => phaseNormalizedAlpha q (α ν) (β ν))
    (fun ν => phaseNormalizedBeta q (α ν) (β ν))
    (fun ν => phaseNormalizedWeights q (a03SixTensorWeight normalizer ν)) c hc
    (phase_normalized_alpha_measurable q α β hα hβ)
    (phase_normalized_beta_measurable q α β hα hβ)
    (phase_normalized_weights_measurable q (a03SixTensorWeight normalizer)
      (a03SixTensorWeight_measurable normalizer hm))
    hadm (fun ν => phase_normalized_weights_complex q _ (hW ν)) (phaseNormalizedSign q positive)

private theorem a03_actual_source_integral_difference
    (kernel : SchwartzMap A03SixTensorSpace ℂ) (normalizer : A03SixTensorSpace → ℝ)
    (hm : Measurable normalizer) (hc : Integrable (a03SixTensorCoefficient kernel normalizer))
    {D : ℝ} (hD : 0≤D) (h0 : ∀ ν i x, ‖a03SixTensorWeight normalizer ν i x‖≤D)
    (hW : ∀ ν i, RectangularComplexWeight (a03SixTensorWeight normalizer ν i))
    (positive : Bool) (T A B H : ℝ) (f g : ℝ → ℝ) (k : Fin 4 → ℕ)
    (hA : 0<A) (hB : 0<B) (hH : 0<H)
    (hdisc : Integrable (fun ν => a03SixTensorCoefficient kernel normalizer ν*
      a03EndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν)) :
    Integrable (fun ν => a03SixTensorCoefficient kernel normalizer ν*
      a03EndpointNormalizedZeroMode T A B H f g k normalizer ν) ∧
    (∫ ν, a03SixTensorCoefficient kernel normalizer ν*
      a03EndpointNormalizedSum positive T A B H f g k normalizer ν)-
      (∫ ν, a03SixTensorCoefficient kernel normalizer ν*
        a03EndpointNormalizedZeroMode T A B H f g k normalizer ν)=
      ∫ ν, a03SixTensorCoefficient kernel normalizer ν*
        a03EndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν := by
  have hnative := a03SixTensor_source_integrable kernel normalizer hm hc hD h0
    positive (phaseActualScales A B H k) hB
    (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B)
  have hsum : Integrable (fun ν => a03SixTensorCoefficient kernel normalizer ν*
      a03EndpointNormalizedSum positive T A B H f g k normalizer ν) := by
    apply hnative.congr
    exact ae_of_all volume fun ν => congrArg (fun z : ℂ =>
      a03SixTensorCoefficient kernel normalizer ν*z)
      (a03Six_actual_normalized_source_sum positive T A B H f g k ν _ (hW ν) hA hB hH)
  have hz : Integrable (fun ν => a03SixTensorCoefficient kernel normalizer ν*
      a03EndpointNormalizedZeroMode T A B H f g k normalizer ν) := by
    apply (hsum.sub hdisc).congr
    apply ae_of_all volume
    intro ν
    simp only [Pi.sub_apply]
    unfold a03EndpointNormalizedSum a03EndpointNormalizedDiscrepancy
      a03EndpointNormalizedZeroMode rectangularComplexDiscrepancy
    dsimp only
    ring
  refine ⟨hz,?_⟩
  rw [←integral_sub hsum hz]
  apply integral_congr_ae
  apply ae_of_all volume
  intro ν
  unfold a03EndpointNormalizedSum a03EndpointNormalizedDiscrepancy
    a03EndpointNormalizedZeroMode rectangularComplexDiscrepancy
  dsimp only
  ring

theorem a03_actual_main_tensor_source_endpoint
    (hinput : SeparatedQuadraticInput) {a b εsource εkernel c κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hεsource : 0<εsource)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc 1 2)
    (hc : 0<c) (hc1 : c≤1) (hεkernel : 4*c<εkernel)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ T0 : ℝ, ∃ kernels : {p : A03NearTensorData // A03NearTensorValid T0 θ κ p} → SchwartzMap A03SixTensorSpace ℂ,
      ∃ s u K Ccoef Csource : ℝ, ∃ normalizer : A03SixTensorSpace → ℝ, ∃ bounds : ℕ → ℝ,
      (∀ p y, kernels p y = a03TensorLogCutoff y*a03ActualTensorNormalizedKernel Φ c εkernel p.val y) ∧
      0<s ∧ s<1/2 ∧ 0<u ∧ 1≤K ∧ 0≤Ccoef ∧ 0≤Csource ∧ Measurable normalizer ∧
      (∀ ν, 0<normalizer ν) ∧ (∀ j, 0≤bounds j) ∧
      (∀ ν j, RectangularComplexWeight (a03SixTensorWeight normalizer ν j)) ∧
      (∀ j ν i x, ‖iteratedDeriv j (a03SixTensorWeight normalizer ν i) x‖≤bounds j) ∧
      (∀ p, Integrable (a03SixTensorCoefficient (kernels p) normalizer) ∧
        (∫ ν, ‖a03SixTensorCoefficient (kernels p) normalizer ν‖)≤Ccoef) ∧
      ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 2/3≤A → 2/3≤B → 2/3≤H →
        ∀ k : Fin 4 → ℕ, k∈rectangularAFEProductScaleGrid (T^(2+u)) →
        phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
        ∀ σ : MomentShifts, (∀ j, ‖σ j‖≤R) →
        (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
        ∀ v : ℝ, |v|≤θ*Real.log T → ∀ positive : Bool,
        ∃ hvalid : A03NearTensorValid T0 θ κ
          (phaseActualNearTensorData T σ (rawMomentShifts T σ) v A B H k positive),
        let p := (⟨phaseActualNearTensorData T σ (rawMomentShifts T σ) v A B H k positive,hvalid⟩ :
          {p : A03NearTensorData // A03NearTensorValid T0 θ κ p})
        let coeff := a03SixTensorCoefficient (kernels p) normalizer
        let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
        (∫ ν, coeff ν*a03EndpointNormalizedSum positive T A B H f g k normalizer ν) =
          a03EndpointPhysicalTensorSum (a03ActualTensorNormalizedKernel Φ c εkernel)
            positive T A B H σ (rawMomentShifts T σ) v f g k ∧
        ‖∫ ν, coeff ν*a03EndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν‖ ≤
          (Csource*phaseSourceMajorant εsource (phaseNormalizedScales q))*(∫ ν, ‖coeff ν‖) ∧
        ‖∫ ν, coeff ν*a03EndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν‖ ≤
          Csource*Ccoef*phaseSourceMajorant εsource (phaseNormalizedScales q) ∧
        Integrable (fun ν => coeff ν*a03EndpointNormalizedZeroMode T A B H f g k normalizer ν) ∧
        (a03EndpointPhysicalTensorSum (a03ActualTensorNormalizedKernel Φ c εkernel)
            positive T A B H σ (rawMomentShifts T σ) v f g k -
          ∫ ν, coeff ν*a03EndpointNormalizedZeroMode T A B H f g k normalizer ν) =
          (∫ ν, coeff ν*a03EndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν) ∧
        ‖a03EndpointPhysicalTensorSum (a03ActualTensorNormalizedKernel Φ c εkernel)
            positive T A B H σ (rawMomentShifts T σ) v f g k -
          ∫ ν, coeff ν*a03EndpointNormalizedZeroMode T A B H f g k normalizer ν‖ ≤
          Csource*Ccoef*phaseSourceMajorant εsource (phaseNormalizedScales q) := by
  obtain ⟨T0,kernels,s,u,K,Ccoef,normalizer,bounds,hgraph,hs,hs2,hu,hK,hCcoef,hm,hn,
    hbounds,hW,hd,hcoef,_heq,hfuture⟩ :=
    phase_actual_main_tensor_source_factory ha hab hlen (DivisorProof.inputExponent_pos hεsource (by norm_num : (0:ℝ)<1)) f g hf hg hΦ hΦs hc hc1 hεkernel hκ hθ hR
  obtain ⟨Csource,hCsource,hsource⟩ :=
    a03_actual_source_class_superposition hinput hεsource hK bounds hbounds normalizer hm hW
  refine ⟨T0,kernels,s,u,K,Ccoef,Csource,normalizer,bounds,hgraph,hs,hs2,hu,hK,
    hCcoef,hCsource,hm,hn,hbounds,hW,hd,hcoef,?_⟩
  filter_upwards [hfuture] with T hactual
  intro A B H hA hB hH k hk hactive σ hσ hroot v hv positive
  obtain ⟨hvalid,hadm⟩ := hactual A B H hA hB hH k hk hactive σ hσ hroot v hv positive
  let p := (⟨phaseActualNearTensorData T σ (rawMomentShifts T σ) v A B H k positive,hvalid⟩ :
    {p : A03NearTensorData // A03NearTensorValid T0 θ κ p})
  let coeff := a03SixTensorCoefficient (kernels p) normalizer
  let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
  have hAp : 0<A := by linarith
  have hBp : 0<B := by linarith
  have hHp : 0<H := by linarith
  have h0 : ∀ ν i x, ‖a03SixTensorWeight normalizer ν i x‖≤bounds 0 := by
    intro ν i x
    simpa using hd 0 ν i x
  have hfinite := a03_actual_tensor_finite_signed_source_reconstruction T A B H c εkernel σ (rawMomentShifts T σ) v k positive f g Φ hBp
    (kernels p) (hgraph p) normalizer hm hn (hcoef p).1 (hbounds 0) h0
  have htransport := a03Six_actual_normalized_source_integral positive T A B H f g k
    normalizer hW coeff hAp hBp hHp
  obtain ⟨hdisc,hbound⟩ := hsource T A B H f g k coeff (hcoef p).1 hadm hBp positive
  have hq : ∀ j, 0≤(phaseNormalizedScales q).size j := by
    intro j
    exact zero_le_one.trans ((hadm 0 (fun _ => false)).1 j)
  have hmajor : 0≤phaseSourceMajorant εsource (phaseNormalizedScales q) :=
    phase_source_majorant_nonneg _ _ hq
  have hequality : (∫ ν, coeff ν*a03EndpointNormalizedSum positive T A B H f g k normalizer ν) =
      a03EndpointPhysicalTensorSum (a03ActualTensorNormalizedKernel Φ c εkernel)
            positive T A B H σ (rawMomentShifts T σ) v f g k := htransport.symm.trans hfinite
  have hbudget : ‖∫ ν, coeff ν*a03EndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν‖ ≤
      Csource*Ccoef*phaseSourceMajorant εsource (phaseNormalizedScales q) := by
    calc
      _ ≤ (Csource*phaseSourceMajorant εsource (phaseNormalizedScales q))*(∫ ν, ‖coeff ν‖) := hbound
      _ ≤ (Csource*phaseSourceMajorant εsource (phaseNormalizedScales q))*Ccoef :=
        mul_le_mul_of_nonneg_left (hcoef p).2 (mul_nonneg hCsource hmajor)
      _ = Csource*Ccoef*phaseSourceMajorant εsource (phaseNormalizedScales q) := by ring
  obtain ⟨hzero,hdifference⟩ := a03_actual_source_integral_difference (kernels p) normalizer
    hm (hcoef p).1 (hbounds 0) h0 hW positive T A B H f g k hAp hBp hHp hdisc
  change (∫ ν, coeff ν*a03EndpointNormalizedSum positive T A B H f g k normalizer ν)-
      (∫ ν, coeff ν*a03EndpointNormalizedZeroMode T A B H f g k normalizer ν)=
      ∫ ν, coeff ν*a03EndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν at hdifference
  rw [hequality] at hdifference
  exact ⟨hvalid,hequality,hbound,hbudget,hzero,hdifference,by rw [hdifference]; exact hbudget⟩

theorem a03_actual_dual_tensor_source_endpoint
    (hinput : SeparatedQuadraticInput) {a b εsource εkernel c κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hεsource : 0<εsource)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc 1 2)
    (hc : 0<c) (hc1 : c≤1) (hεkernel : 4*c<εkernel)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ T0 : ℝ, ∃ kernels : {p : A03NearTensorData // A03DualNearTensorValid T0 θ κ R p} → SchwartzMap A03SixTensorSpace ℂ,
      ∃ s u K Ccoef Csource : ℝ, ∃ normalizer : A03SixTensorSpace → ℝ, ∃ bounds : ℕ → ℝ,
      (∀ p y, kernels p y = a03TensorLogCutoff y*a03ActualDualTensorNormalizedKernel Φ c εkernel p.val y) ∧
      0<s ∧ s<1/2 ∧ 0<u ∧ 1≤K ∧ 0≤Ccoef ∧ 0≤Csource ∧ Measurable normalizer ∧
      (∀ ν, 0<normalizer ν) ∧ (∀ j, 0≤bounds j) ∧
      (∀ ν j, RectangularComplexWeight (a03SixTensorWeight normalizer ν j)) ∧
      (∀ j ν i x, ‖iteratedDeriv j (a03SixTensorWeight normalizer ν i) x‖≤bounds j) ∧
      (∀ p, Integrable (a03SixTensorCoefficient (kernels p) normalizer) ∧
        (∫ ν, ‖a03SixTensorCoefficient (kernels p) normalizer ν‖)≤Ccoef) ∧
      ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 2/3≤A → 2/3≤B → 2/3≤H →
        ∀ k : Fin 4 → ℕ, k∈rectangularAFEProductScaleGrid (T^(2+u)) →
        phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
        ∀ σ : MomentShifts, (∀ j, ‖σ j‖≤R) →
        (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
        ∀ v : ℝ, |v|≤θ*Real.log T → ∀ positive : Bool,
        ∃ hvalid : A03DualNearTensorValid T0 θ κ R
          (phaseActualNearTensorData T σ (bblrSixShifts (rawMomentShifts T σ) 1) v A B H k positive),
        let p := (⟨phaseActualNearTensorData T σ (bblrSixShifts (rawMomentShifts T σ) 1) v A B H k positive,hvalid⟩ :
          {p : A03NearTensorData // A03DualNearTensorValid T0 θ κ R p})
        let coeff := a03SixTensorCoefficient (kernels p) normalizer
        let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
        (∫ ν, coeff ν*a03EndpointNormalizedSum positive T A B H f g k normalizer ν) =
          a03EndpointPhysicalTensorSum (a03ActualDualTensorNormalizedKernel Φ c εkernel)
            positive T A B H σ (bblrSixShifts (rawMomentShifts T σ) 1) v f g k ∧
        ‖∫ ν, coeff ν*a03EndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν‖ ≤
          (Csource*phaseSourceMajorant εsource (phaseNormalizedScales q))*(∫ ν, ‖coeff ν‖) ∧
        ‖∫ ν, coeff ν*a03EndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν‖ ≤
          Csource*Ccoef*phaseSourceMajorant εsource (phaseNormalizedScales q) ∧
        Integrable (fun ν => coeff ν*a03EndpointNormalizedZeroMode T A B H f g k normalizer ν) ∧
        (a03EndpointPhysicalTensorSum (a03ActualDualTensorNormalizedKernel Φ c εkernel)
            positive T A B H σ (bblrSixShifts (rawMomentShifts T σ) 1) v f g k -
          ∫ ν, coeff ν*a03EndpointNormalizedZeroMode T A B H f g k normalizer ν) =
          (∫ ν, coeff ν*a03EndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν) ∧
        ‖a03EndpointPhysicalTensorSum (a03ActualDualTensorNormalizedKernel Φ c εkernel)
            positive T A B H σ (bblrSixShifts (rawMomentShifts T σ) 1) v f g k -
          ∫ ν, coeff ν*a03EndpointNormalizedZeroMode T A B H f g k normalizer ν‖ ≤
          Csource*Ccoef*phaseSourceMajorant εsource (phaseNormalizedScales q) := by
  obtain ⟨T0,kernels,s,u,K,Ccoef,normalizer,bounds,hgraph,hs,hs2,hu,hK,hCcoef,hm,hn,
    hbounds,hW,hd,hcoef,_heq,hfuture⟩ :=
    phase_actual_dual_tensor_source_factory ha hab hlen (DivisorProof.inputExponent_pos hεsource (by norm_num : (0:ℝ)<1)) f g hf hg hΦ hΦs hc hc1 hεkernel hκ hθ hR
  obtain ⟨Csource,hCsource,hsource⟩ :=
    a03_actual_source_class_superposition hinput hεsource hK bounds hbounds normalizer hm hW
  refine ⟨T0,kernels,s,u,K,Ccoef,Csource,normalizer,bounds,hgraph,hs,hs2,hu,hK,
    hCcoef,hCsource,hm,hn,hbounds,hW,hd,hcoef,?_⟩
  filter_upwards [hfuture] with T hactual
  intro A B H hA hB hH k hk hactive σ hσ hroot v hv positive
  obtain ⟨hvalid,hadm⟩ := hactual A B H hA hB hH k hk hactive σ hσ hroot v hv positive
  let p := (⟨phaseActualNearTensorData T σ (bblrSixShifts (rawMomentShifts T σ) 1) v A B H k positive,hvalid⟩ :
    {p : A03NearTensorData // A03DualNearTensorValid T0 θ κ R p})
  let coeff := a03SixTensorCoefficient (kernels p) normalizer
  let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
  have hAp : 0<A := by linarith
  have hBp : 0<B := by linarith
  have hHp : 0<H := by linarith
  have h0 : ∀ ν i x, ‖a03SixTensorWeight normalizer ν i x‖≤bounds 0 := by
    intro ν i x
    simpa using hd 0 ν i x
  have hfinite := a03_actual_dual_tensor_finite_signed_source_reconstruction T A B H c εkernel σ (bblrSixShifts (rawMomentShifts T σ) 1) v k positive f g Φ hBp
    (kernels p) (hgraph p) normalizer hm hn (hcoef p).1 (hbounds 0) h0
  have htransport := a03Six_actual_normalized_source_integral positive T A B H f g k
    normalizer hW coeff hAp hBp hHp
  obtain ⟨hdisc,hbound⟩ := hsource T A B H f g k coeff (hcoef p).1 hadm hBp positive
  have hq : ∀ j, 0≤(phaseNormalizedScales q).size j := by
    intro j
    exact zero_le_one.trans ((hadm 0 (fun _ => false)).1 j)
  have hmajor : 0≤phaseSourceMajorant εsource (phaseNormalizedScales q) :=
    phase_source_majorant_nonneg _ _ hq
  have hequality : (∫ ν, coeff ν*a03EndpointNormalizedSum positive T A B H f g k normalizer ν) =
      a03EndpointPhysicalTensorSum (a03ActualDualTensorNormalizedKernel Φ c εkernel)
            positive T A B H σ (bblrSixShifts (rawMomentShifts T σ) 1) v f g k := htransport.symm.trans hfinite
  have hbudget : ‖∫ ν, coeff ν*a03EndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν‖ ≤
      Csource*Ccoef*phaseSourceMajorant εsource (phaseNormalizedScales q) := by
    calc
      _ ≤ (Csource*phaseSourceMajorant εsource (phaseNormalizedScales q))*(∫ ν, ‖coeff ν‖) := hbound
      _ ≤ (Csource*phaseSourceMajorant εsource (phaseNormalizedScales q))*Ccoef :=
        mul_le_mul_of_nonneg_left (hcoef p).2 (mul_nonneg hCsource hmajor)
      _ = Csource*Ccoef*phaseSourceMajorant εsource (phaseNormalizedScales q) := by ring
  obtain ⟨hzero,hdifference⟩ := a03_actual_source_integral_difference (kernels p) normalizer
    hm (hcoef p).1 (hbounds 0) h0 hW positive T A B H f g k hAp hBp hHp hdisc
  change (∫ ν, coeff ν*a03EndpointNormalizedSum positive T A B H f g k normalizer ν)-
      (∫ ν, coeff ν*a03EndpointNormalizedZeroMode T A B H f g k normalizer ν)=
      ∫ ν, coeff ν*a03EndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν at hdifference
  rw [hequality] at hdifference
  exact ⟨hvalid,hequality,hbound,hbudget,hzero,hdifference,by rw [hdifference]; exact hbudget⟩

end
end SixthMoment
