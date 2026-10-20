import Sechstmoment.Numerator.U.Sources.PassiveActualTensorParameters
import Sechstmoment.Numerator.U.Sources.PassiveSoftSourceFactory

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_actual_ratio_tensor_passive_soft_source_physical_bound
    (dual : Bool) (hinput : SeparatedQuadraticInput) {a b εsource εkernel c κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hεsource : 0<εsource)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    (hc : 0<c) (hc1 : c≤1) (hεkernel : 12*c<εkernel)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R)
    (hloss : 4*εsource+εkernel<rectangularSlack a b) :
    ∃ s u C : ℝ,0<s ∧ s<1/2 ∧ s≤1/8 ∧ 0<u ∧ u≤1/8 ∧
      s/2+4*εsource+εkernel≤rectangularSlack a b ∧
      3*s/4+u/4+4*εsource+εkernel≤rectangularSlack a b ∧ 0≤C ∧
      ∀ᶠ T : ℝ in atTop,∀ A B H : ℝ,2/3≤A → 2/3≤B → 2/3≤H →
        ∀ k : Fin 4→ℕ,k∈rectangularAFEProductScaleGrid (T^(2+u)) →
        A03ActualPassiveNearZeroBlock T A B H (T^(s-1)) f g k →
        let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
        q.M₁≤q.M₂*q.mass^(DivisorProof.inputExponent εsource 1) →
        q.N₁≤q.N₂*q.mass^(DivisorProof.inputExponent εsource 1) → k 1≠0 → k 3≠0 →
        ∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) → (∀ j,‖α j‖≤1/4) →
        (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
        ∀ v : ℝ,|v|≤θ*Real.log T → ∀ positive : Bool,∀ tM tN : ℝ,
        ‖a03EndpointPhysicalTensorSum (a03RatioSourceFamilyKernel dual Φ c εkernel tM tN)
            positive T A B H σ α v f g k-
          a03EndpointPhysicalUnsortedZeroMode
            (a03RatioSourceFamilyKernel dual Φ c εkernel tM tN
              (phaseActualNearTensorData T σ α v A B H k positive)) T A B H f g k‖≤
          (C/Real.sqrt (A*B))*phaseSourceMajorant εsource (a03SoftSourceOrientedScales q) := by
  obtain ⟨T0,kernels,hgraph,hseminorm⟩ :=
    a03_actual_ratio_tensor_bounded_schwartz_family dual hΦ hΦs hc hc1 hεkernel hκ hθ hR
  obtain ⟨s,u,K,Ccoef,normalizer,bounds,hs,hs2,hu,hK,hCcoef,hm,hn,hbounds,hW,hd,hcoef,_hexact,hfuture⟩ :=
    a03Six_actual_passive_power_near_soft_source_admissibility ha hab hlen
      (DivisorProof.inputExponent_pos hεsource (by norm_num : (0:ℝ)<1)) f g hf hg kernels hseminorm
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgb⟩ := rectangular_supported_profile_bounded g hg
  obtain ⟨Csource,hCsource,hsource⟩ := a03_actual_soft_source_sqrt_superposition
    hinput hεsource hK hF hG f g hfb hgb bounds hbounds normalizer hm hW
  let d := rectangularSlack a b-4*εsource-εkernel
  have hd0 : 0<d := by dsimp [d]; linarith
  let s' := min s (min (1/8:ℝ) d)
  let u' := min u (min (1/8:ℝ) d)
  have hss : s'≤s := min_le_left _ _
  have huu : u'≤u := min_le_left _ _
  have hs' : 0<s' := lt_min hs (lt_min (by norm_num) hd0)
  have hu' : 0<u' := lt_min hu (lt_min (by norm_num) hd0)
  have hs2' : s'<1/2 := hss.trans_lt hs2
  have hscap : s'≤1/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hucap : u'≤1/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hsd : s'≤d := (min_le_right _ _).trans (min_le_right _ _)
  have hud : u'≤d := (min_le_right _ _).trans (min_le_right _ _)
  have hloss1 : s'/2+4*εsource+εkernel≤rectangularSlack a b := by dsimp [d] at hsd; linarith
  have hloss2 : 3*s'/4+u'/4+4*εsource+εkernel≤rectangularSlack a b := by dsimp [d] at hsd hud; linarith
  refine ⟨s',u',Csource*Ccoef,hs',hs2',hscap,hu',hucap,hloss1,hloss2,mul_nonneg hCsource hCcoef,?_⟩
  filter_upwards [hfuture,a03_actual_passive_tensor_parameters_valid (by linarith : s'<1) T0 θ κ f g,
    eventually_ge_atTop (1:ℝ)] with T hactual hvalid hT
  intro A B H hA hB hH k hk hactive
  dsimp only
  intro hmsoft hnsoft hk1 hk3 σ α hσ hα hroot v hv positive tM tN
  have hAp : 0<A := by linarith
  have hBp : 0<B := by linarith
  have hHp : 0<H := by linarith
  obtain ⟨hk',hactive'⟩ := a03_actual_passive_source_restricted_domain hT hss huu f g k hk hactive
  have hadm : a03SoftSixFourierSourceClasses (DivisorProof.inputExponent εsource 1) K bounds normalizer T A B H f g k :=
    hactual A B H hA hB hH k hk' hactive' hmsoft hnsoft
  have hpvalid : A03RatioTensorValid T0 θ κ R
      ⟨phaseActualNearTensorData T σ α v A B H k positive,tM,tN⟩ :=
    ⟨hvalid A B H hAp hBp hHp k hactive σ α hα hroot v hv positive,hσ⟩
  let p : {p : A03RatioTensorData // A03RatioTensorValid T0 θ κ R p} :=
    ⟨⟨phaseActualNearTensorData T σ α v A B H k positive,tM,tN⟩,hpvalid⟩
  let coeff := a03SixTensorCoefficient (kernels p) normalizer
  let Fp := a03RatioSourceFamilyKernel dual Φ c εkernel tM tN
    (phaseActualNearTensorData T σ α v A B H k positive)
  have h0 : ∀ ν i x,‖a03SixTensorWeight normalizer ν i x‖≤bounds 0 := by
    intro ν i x
    simpa using hd 0 ν i x
  have hFpgraph : ∀ y,kernels p y=a03TensorLogCutoff y*Fp y := hgraph p
  have hβsmooth : ∀ b,phaseActualAmplifierCoefficient T g B b≠0 →
      rectangularSmoothBlockWeight ((b:ℝ)/B)≠0 := by
    intro b hb hz
    apply hb
    simp only [phaseActualAmplifierCoefficient,hz,Complex.ofReal_zero,zero_mul]
  have hfinite := a03_tensor_cutoff_finite_signed_source_reconstruction (kernels p) Fp hFpgraph
    normalizer hm hn (hcoef p).1 (hbounds 0) h0 positive (phaseActualScales A B H k) hBp
    (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B) hβsmooth
  have hsumint := a03SixTensor_source_integrable (kernels p) normalizer hm (hcoef p).1 (hbounds 0) h0
    positive (phaseActualScales A B H k) hBp
    (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B)
  have hsum : Integrable (fun ν => coeff ν*a03SoftEndpointNormalizedSum positive T A B H f g k normalizer ν) := by
    apply hsumint.congr
    exact ae_of_all _ fun ν => congrArg (fun z : ℂ => coeff ν*z)
      (a03_soft_source_sum_eq_native positive T A B H f g k ν normalizer (hW ν) hAp hBp hHp).symm
  have hphysical : (∫ ν,coeff ν*a03SoftEndpointNormalizedSum positive T A B H f g k normalizer ν)=
      a03EndpointPhysicalTensorSum (a03RatioSourceFamilyKernel dual Φ c εkernel tM tN)
        positive T A B H σ α v f g k := by
    simp_rw [a03_soft_source_sum_eq_native positive T A B H f g k _ normalizer (hW _) hAp hBp hHp]
    exact hfinite
  obtain ⟨hzero,hezero⟩ := a03_soft_endpoint_zero_integral_eq_uncut_unsorted_physical
    (kernels p) Fp hFpgraph normalizer hm hn (hcoef p).1 (hbounds 0) h0 T A B H f g k hAp hBp hHp hk1 hk3
  have hdiff : a03EndpointPhysicalTensorSum (a03RatioSourceFamilyKernel dual Φ c εkernel tM tN)
      positive T A B H σ α v f g k-a03EndpointPhysicalUnsortedZeroMode Fp T A B H f g k=
      ∫ ν,coeff ν*a03SoftEndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν := by
    rw [←hphysical,←hezero]
    unfold a03SoftEndpointZeroIntegral
    rw [←integral_sub hsum hzero]
    apply integral_congr_ae
    exact ae_of_all _ fun ν => by dsimp [a03SoftEndpointNormalizedDiscrepancy]; ring
  obtain ⟨_hdisc,hbound⟩ := hsource T A B H k coeff (hcoef p).1 hA hB hH hadm positive
  have hmajor : 0≤phaseSourceMajorant εsource (a03SoftSourceOrientedScales
      (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k))) :=
    phase_source_majorant_nonneg _ _ (fun j => zero_le_one.trans ((hadm 0 (fun _ => false)).1 j))
  rw [hdiff]
  calc
    _≤(Csource*phaseSourceMajorant εsource (a03SoftSourceOrientedScales
        (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k))))/Real.sqrt (A*B)*Ccoef :=
      hbound.trans (mul_le_mul_of_nonneg_left (hcoef p).2 (by positivity))
    _=_ := by ring

end
end Sechstmoment
