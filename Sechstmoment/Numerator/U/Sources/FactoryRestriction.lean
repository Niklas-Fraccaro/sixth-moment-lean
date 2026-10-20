import Sechstmoment.Numerator.U.Sources.GlobalAmplifier
import Sechstmoment.Numerator.U.Sources.GlobalSupport

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology FourierTransform
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_actual_source_restricted_domain
    {T A B H s u s' u' : ℝ} (hT : 1≤T) (hs : s'≤s) (hu : u'≤u)
    (f g : ℝ → ℝ) (k : Fin 4 → ℕ)
    (hk : k∈rectangularAFEProductScaleGrid (T^(2+u')))
    (hactive : phaseActualActiveNearBlock T A B H (T^(s'-1)) f g k) :
    k∈rectangularAFEProductScaleGrid (T^(2+u)) ∧
      phaseActualActiveNearBlock T A B H (T^(s-1)) f g k := by
  have hTp : 0<T := zero_lt_one.trans_le hT
  refine ⟨rectangularAFEProductScaleGrid_mono (Real.rpow_pos_of_pos hTp _)
    (Real.rpow_pos_of_pos hTp _) (Real.rpow_le_rpow_of_exponent_le hT (by linarith)) hk,?_⟩
  exact phaseActualActiveNearBlock_mono f g k
    (Real.rpow_le_rpow_of_exponent_le hT (by linarith)) hactive

theorem a03_actual_source_slack_choices {a b : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) :
    0<rectangularSlack a b/128 ∧
      rectangularSlack a b/128≤1 ∧
      4*(rectangularSlack a b/128)<rectangularSlack a b/16 ∧
      4*(rectangularSlack a b/128)+rectangularSlack a b/16<rectangularSlack a b := by
  have hd := (rectangular_slack_bounds hab hlen).1
  refine ⟨by positivity,?_,by linarith,by linarith⟩
  unfold rectangularSlack
  linarith

theorem a03_actual_main_tensor_source_endpoint_sqrt_restricted
    (hinput : SeparatedQuadraticInput) {a b εsource εkernel c κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hεsource : 0<εsource)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc 1 2)
    (hc : 0<c) (hc1 : c≤1) (hεkernel : 4*c<εkernel)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R)
    (hloss : 4*εsource+εkernel<rectangularSlack a b) :
    ∃ T0 : ℝ, ∃ kernels : {p : A03NearTensorData // A03NearTensorValid T0 θ κ p} → SchwartzMap A03SixTensorSpace ℂ,
      ∃ s u Ccoef Csource : ℝ, ∃ normalizer : A03SixTensorSpace → ℝ,
      (∀ p y, kernels p y=a03TensorLogCutoff y*a03ActualTensorNormalizedKernel Φ c εkernel p.val y) ∧
      0<s ∧ s<1/2 ∧ s≤1/8 ∧ 0<u ∧ u≤1/8 ∧
      s/2+4*εsource+εkernel≤rectangularSlack a b ∧
      3*s/4+u/4+4*εsource+εkernel≤rectangularSlack a b ∧ 0≤Ccoef ∧ 0≤Csource ∧ Measurable normalizer ∧
      (∀ ν, 0<normalizer ν) ∧
      (∃ D : ℝ, 0≤D ∧ ∀ ν i x, ‖a03SixTensorWeight normalizer ν i x‖≤D) ∧
      (∀ ν j, RectangularComplexWeight (a03SixTensorWeight normalizer ν j)) ∧
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
        let physical := a03EndpointPhysicalTensorSum (a03ActualTensorNormalizedKernel Φ c εkernel)
          positive T A B H σ (rawMomentShifts T σ) v f g k
        let zero := a03EndpointZeroIntegral (kernels p) normalizer T A B H f g k
        (∫ ν, coeff ν*a03EndpointNormalizedSum positive T A B H f g k normalizer ν)=physical ∧
        Integrable (fun ν => coeff ν*a03EndpointNormalizedZeroMode T A B H f g k normalizer ν) ∧
        physical-zero=(∫ ν, coeff ν*a03EndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν) ∧
        ‖physical-zero‖≤(Csource*Ccoef/Real.sqrt (A*B))*phaseSourceMajorant εsource
          (phaseNormalizedScales (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k))) := by
  obtain ⟨T0,kernels,s,u,Ccoef,Csource,normalizer,hgraph,hs,hs2,hu,hCcoef,hCsource,hm,hn,
    hD,hW,hcoef,hfuture⟩ :=
    a03_actual_main_tensor_source_endpoint_sqrt hinput ha hab hlen hεsource f g hf hg
      hΦ hΦs hc hc1 hεkernel hκ hθ hR
  let d := rectangularSlack a b-4*εsource-εkernel
  have hd : 0<d := by dsimp [d]; linarith
  let s' := min s (min (1/8:ℝ) d)
  let u' := min u (min (1/8:ℝ) d)
  have hss : s'≤s := min_le_left _ _
  have huu : u'≤u := min_le_left _ _
  have hs' : 0<s' := lt_min hs (lt_min (by norm_num) hd)
  have hu' : 0<u' := lt_min hu (lt_min (by norm_num) hd)
  have hscap : s'≤1/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hucap : u'≤1/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hsd : s'≤d := (min_le_right _ _).trans (min_le_right _ _)
  have hud : u'≤d := (min_le_right _ _).trans (min_le_right _ _)
  have hloss1 : s'/2+4*εsource+εkernel≤rectangularSlack a b := by
    dsimp [d] at hd hsd
    linarith
  have hloss2 : 3*s'/4+u'/4+4*εsource+εkernel≤rectangularSlack a b := by
    dsimp [d] at hsd hud
    linarith
  refine ⟨T0,kernels,s',u',Ccoef,Csource,normalizer,hgraph,hs',hss.trans_lt hs2,hscap,
    hu',hucap,hloss1,hloss2,hCcoef,hCsource,hm,hn,hD,hW,hcoef,?_⟩
  filter_upwards [hfuture,eventually_ge_atTop (1:ℝ)] with T hactual hT
  intro A B H hA hB hH k hk hactive σ hσ hroot v hv positive
  obtain ⟨hk',hactive'⟩ := a03_actual_source_restricted_domain hT hss huu f g k hk hactive
  exact hactual A B H hA hB hH k hk' hactive' σ hσ hroot v hv positive

theorem a03_actual_dual_tensor_source_endpoint_sqrt_restricted
    (hinput : SeparatedQuadraticInput) {a b εsource εkernel c κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hεsource : 0<εsource)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc 1 2)
    (hc : 0<c) (hc1 : c≤1) (hεkernel : 4*c<εkernel)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R)
    (hloss : 4*εsource+εkernel<rectangularSlack a b) :
    ∃ T0 : ℝ, ∃ kernels : {p : A03NearTensorData // A03DualNearTensorValid T0 θ κ R p} → SchwartzMap A03SixTensorSpace ℂ,
      ∃ s u Ccoef Csource : ℝ, ∃ normalizer : A03SixTensorSpace → ℝ,
      (∀ p y, kernels p y=a03TensorLogCutoff y*a03ActualDualTensorNormalizedKernel Φ c εkernel p.val y) ∧
      0<s ∧ s<1/2 ∧ s≤1/8 ∧ 0<u ∧ u≤1/8 ∧
      s/2+4*εsource+εkernel≤rectangularSlack a b ∧
      3*s/4+u/4+4*εsource+εkernel≤rectangularSlack a b ∧ 0≤Ccoef ∧ 0≤Csource ∧ Measurable normalizer ∧
      (∀ ν, 0<normalizer ν) ∧
      (∃ D : ℝ, 0≤D ∧ ∀ ν i x, ‖a03SixTensorWeight normalizer ν i x‖≤D) ∧
      (∀ ν j, RectangularComplexWeight (a03SixTensorWeight normalizer ν j)) ∧
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
        let physical := a03EndpointPhysicalTensorSum (a03ActualDualTensorNormalizedKernel Φ c εkernel)
          positive T A B H σ (bblrSixShifts (rawMomentShifts T σ) 1) v f g k
        let zero := a03EndpointZeroIntegral (kernels p) normalizer T A B H f g k
        (∫ ν, coeff ν*a03EndpointNormalizedSum positive T A B H f g k normalizer ν)=physical ∧
        Integrable (fun ν => coeff ν*a03EndpointNormalizedZeroMode T A B H f g k normalizer ν) ∧
        physical-zero=(∫ ν, coeff ν*a03EndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν) ∧
        ‖physical-zero‖≤(Csource*Ccoef/Real.sqrt (A*B))*phaseSourceMajorant εsource
          (phaseNormalizedScales (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k))) := by
  obtain ⟨T0,kernels,s,u,Ccoef,Csource,normalizer,hgraph,hs,hs2,hu,hCcoef,hCsource,hm,hn,
    hD,hW,hcoef,hfuture⟩ :=
    a03_actual_dual_tensor_source_endpoint_sqrt hinput ha hab hlen hεsource f g hf hg
      hΦ hΦs hc hc1 hεkernel hκ hθ hR
  let d := rectangularSlack a b-4*εsource-εkernel
  have hd : 0<d := by dsimp [d]; linarith
  let s' := min s (min (1/8:ℝ) d)
  let u' := min u (min (1/8:ℝ) d)
  have hss : s'≤s := min_le_left _ _
  have huu : u'≤u := min_le_left _ _
  have hs' : 0<s' := lt_min hs (lt_min (by norm_num) hd)
  have hu' : 0<u' := lt_min hu (lt_min (by norm_num) hd)
  have hscap : s'≤1/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hucap : u'≤1/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hsd : s'≤d := (min_le_right _ _).trans (min_le_right _ _)
  have hud : u'≤d := (min_le_right _ _).trans (min_le_right _ _)
  have hloss1 : s'/2+4*εsource+εkernel≤rectangularSlack a b := by
    dsimp [d] at hd hsd
    linarith
  have hloss2 : 3*s'/4+u'/4+4*εsource+εkernel≤rectangularSlack a b := by
    dsimp [d] at hsd hud
    linarith
  refine ⟨T0,kernels,s',u',Ccoef,Csource,normalizer,hgraph,hs',hss.trans_lt hs2,hscap,
    hu',hucap,hloss1,hloss2,hCcoef,hCsource,hm,hn,hD,hW,hcoef,?_⟩
  filter_upwards [hfuture,eventually_ge_atTop (1:ℝ)] with T hactual hT
  intro A B H hA hB hH k hk hactive σ hσ hroot v hv positive
  obtain ⟨hk',hactive'⟩ := a03_actual_source_restricted_domain hT hss huu f g k hk hactive
  exact hactual A B H hA hB hH k hk' hactive' σ hσ hroot v hv positive

end
end Sechstmoment
