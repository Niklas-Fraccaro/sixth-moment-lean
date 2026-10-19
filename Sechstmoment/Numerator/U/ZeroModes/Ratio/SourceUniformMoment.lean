import Sechstmoment.Numerator.U.ZeroModes.Ratio.SourceMomentJoin
import Sechstmoment.Numerator.U.ZeroModes.Ratio.SourcePhysicalAggregate

/-! Positive witness restrictions permit one common hard/soft and
original/dual factory choice; the uniform native moment estimate is retained. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_actual_ratio_source_physical_error_aggregate_capped (dual : Bool)
    (hinput : SeparatedQuadraticInput) {a b εsource e c κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hεsource : 0<εsource)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    (hc : 0<c) (hc1 : c≤1) (he : 12*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R)
    (hloss : 4*εsource+e<rectangularSlack a b)
    (S U : ℝ) (hS : 0<S) (hU : 0<U) :
    ∃ s u C : ℝ,0<s ∧ s<1/2 ∧ s≤1/8 ∧ 0<u ∧ u≤1/8 ∧
      s/2+4*εsource+e≤rectangularSlack a b ∧
      3*s/4+u/4+4*εsource+e≤rectangularSlack a b ∧ 0≤C ∧ s≤S ∧ u≤U ∧
      (∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) →
        (∀ j,‖α j‖≤R/Real.log T) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
        ‖a03ActualRatioSourceErrorMoment dual Φ c e T a b s u εsource θ σ α f g‖≤
          C*T^e*a03ActualSoftSourceGlobalMajorant T a b s u εsource θ f g) ∧
      ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) →
        (∀ j,‖α j‖≤R/Real.log T) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
        ‖a03ActualRatioSourceErrorMoment dual Φ c e T a b s u εsource θ σ α f g‖≤δ*T := by
  obtain ⟨s0,u0,C,hs0,hs20,hscap0,hu0,hucap0,hloss10,hloss20,hC,hphysical⟩ :=
    a03_actual_ratio_tensor_soft_source_physical_bound dual hinput ha hab hlen hεsource
      f g hf hg hΦ hΦs hc hc1 he hκ hθ hR hloss
  let s := min s0 S
  let u := min u0 U
  have hss : s≤s0 := min_le_left _ _
  have huu : u≤u0 := min_le_left _ _
  have hs : 0<s := lt_min hs0 hS
  have hu : 0<u := lt_min hu0 hU
  have hs2 : s<1/2 := hss.trans_lt hs20
  have hscap : s≤1/8 := hss.trans hscap0
  have hucap : u≤1/8 := huu.trans hucap0
  have hloss1 : s/2+4*εsource+e≤rectangularSlack a b := by linarith
  have hloss2 : 3*s/4+u/4+4*εsource+e≤rectangularSlack a b := by linarith
  let D := C*a03SourceMellinBound R u
  have hD : 0≤D := by dsimp [D,a03SourceMellinBound]; positivity
  have hbound : ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) →
      (∀ j,‖α j‖≤R/Real.log T) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ‖a03ActualRatioSourceErrorMoment dual Φ c e T a b s u εsource θ σ α f g‖≤
        D*T^e*a03ActualSoftSourceGlobalMajorant T a b s u εsource θ f g := by
    filter_upwards [hphysical,eventually_ge_atTop (1:ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4*R))] with T hphysical hT hlog hlogR
    intro σ α hσ hα hroot
    have hL : 0<Real.log T := zero_lt_one.trans_le hlog
    have hαsmall : ∀ j,‖α j‖≤1/4 := fun j =>
      (hα j).trans ((div_le_iff₀ hL).mpr (by linarith))
    apply a03_actual_ratio_source_error_moment_bound hT hθ dual Φ c σ α f g
    intro v hv positive i hi
    have hk := (Finset.mem_product.mp hi).2
    apply a03_actual_ratio_source_restored_block_bound (zero_lt_one.trans_le hT) hlog hR hc.le hc1 hC
      dual positive Φ σ α hα v f g i hk
    intro hgood
    rcases hgood with ⟨hactive,hmsoft,hnsoft,hk1,hk3⟩
    obtain ⟨hk0,hactive0⟩ := a03_actual_source_restricted_domain hT hss huu f g i.2 hk hactive
    exact hphysical _ _ _ (boundaryActual_scale_ge_two_thirds (i.1 0))
      (boundaryActual_scale_ge_two_thirds (i.1 1)) (boundaryActual_scale_ge_two_thirds (i.1 2))
      i.2 hk0 hactive0 hmsoft hnsoft hk1 hk3 σ α hσ hαsmall hroot v hv positive _ _
  refine ⟨s,u,D,hs,hs2,hscap,hu,hucap,hloss1,hloss2,hD,min_le_right _ _,min_le_right _ _,hbound,?_⟩
  intro δ hδ
  have hsmall := (a03_actual_soft_source_restored_global_majorant_isLittleO
    ha hab hlen hs.le hscap hu hucap hεsource.le hθ hloss1 hloss2 f g hf hg).const_mul_left D
  filter_upwards [hbound,isLittleO_iff.mp hsmall hδ,eventually_ge_atTop (1:ℝ)] with T hb hδb hT
  intro σ α hσ hα hroot
  calc
    _≤D*T^e*a03ActualSoftSourceGlobalMajorant T a b s u εsource θ f g := hb σ α hσ hα hroot
    _≤‖D*(T^e*a03ActualSoftSourceGlobalMajorant T a b s u εsource θ f g)‖ := by
      rw [Real.norm_eq_abs]
      simpa only [mul_assoc] using le_abs_self (D*(T^e*a03ActualSoftSourceGlobalMajorant T a b s u εsource θ f g))
    _≤δ*T := by simpa only [Real.norm_of_nonneg (zero_le_one.trans hT)] using hδb

theorem a03_actual_ratio_source_native_moment_sub_Gamma_zero_uniform_capped (dual : Bool)
    (hinput : SeparatedQuadraticInput) {a b εsource e c κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hεsource : 0<εsource)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    (hc : 0<c) (hc1 : c≤1) (he : 12*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R)
    (hloss : 4*εsource+e<rectangularSlack a b)
    (S U : ℝ) (hS : 0<S) (hU : 0<U) :
    ∃ s u : ℝ,0<s ∧ s<1/2 ∧ s≤1/8 ∧ s≤S ∧ 0<u ∧ u≤1/8 ∧ u≤U ∧
      ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) →
        (∀ j,‖α j‖≤R/Real.log T) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
        IntegrableOn (fun v => a03ActualRatioSourceFiniteValue false dual Φ c T a b s u εsource v σ α f g)
          (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
        IntegrableOn (fun v => a03ActualRatioSourceFiniteValue true dual Φ c T a b s u εsource v σ α f g)
          (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
        ‖a03ActualRatioSourceValueMoment false dual Φ c T a b s u εsource θ σ α f g-
          a03ActualRatioSourceValueMoment true dual Φ c T a b s u εsource θ σ α f g‖≤δ*T := by
  obtain ⟨s,u,_C,hs,hs2,hscap,hu,hucap,_hloss1,_hloss2,_hC,hsS,huU,_hbound,hsmall⟩ :=
    a03_actual_ratio_source_physical_error_aggregate_capped dual hinput ha hab hlen hεsource
      f g hf hg hΦ hΦs hc hc1 he hκ hθ hR hloss S U hS hU
  refine ⟨s,u,hs,hs2,hscap,hsS,hu,hucap,huU,?_⟩
  intro δ hδ
  filter_upwards [hsmall δ hδ,
    a03_actual_ratio_source_finite_values_integrableOn dual hΦ hΦs hc hc1 he hκ hθ hR
      (hs2.trans (by norm_num)) a b u εsource f g,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4*R)),
    eventually_gt_atTop (0:ℝ)] with T hb hi hlog hlogR hT
  intro σ α hσ hα hroot
  have hL : 0<Real.log T := zero_lt_one.trans_le hlog
  have hαsmall : ∀ j,‖α j‖≤1/4 := fun j =>
    (hα j).trans ((div_le_iff₀ hL).mpr (by linarith))
  have hip := hi σ α hσ hαsmall hroot false
  have hiz := hi σ α hσ hαsmall hroot true
  refine ⟨hip,hiz,?_⟩
  rw [←a03ActualRatioSourceErrorMoment_eq_physical_sub_zero hT dual Φ c e a b s u εsource θ σ α f g hip hiz]
  exact hb σ α hσ hα hroot

/-- One genuine factory works at every smaller positive near and AFE
exponent. Thus hard/soft and original/dual witnesses may be restricted by
one literal minimum without changing the fixed contour or source losses. -/
theorem a03_actual_ratio_source_native_moment_sub_Gamma_zero_uniform_smaller (dual : Bool)
    (hinput : SeparatedQuadraticInput) {a b εsource e c κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hεsource : 0<εsource)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    (hc : 0<c) (hc1 : c≤1) (he : 12*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R)
    (hloss : 4*εsource+e<rectangularSlack a b) :
    ∃ S U : ℝ,0<S ∧ S<1/2 ∧ S≤1/8 ∧ 0<U ∧ U≤1/8 ∧
      ∀ s u : ℝ,0<s → s≤S → 0<u → u≤U →
      ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) →
        (∀ j,‖α j‖≤R/Real.log T) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
        IntegrableOn (fun v => a03ActualRatioSourceFiniteValue false dual Φ c T a b s u εsource v σ α f g)
          (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
        IntegrableOn (fun v => a03ActualRatioSourceFiniteValue true dual Φ c T a b s u εsource v σ α f g)
          (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
        ‖a03ActualRatioSourceValueMoment false dual Φ c T a b s u εsource θ σ α f g-
          a03ActualRatioSourceValueMoment true dual Φ c T a b s u εsource θ σ α f g‖≤δ*T := by
  obtain ⟨S,U,C,hS,hS2,hScap,hU,hUcap,hlossS,hlossU,hC,hphysical⟩ :=
    a03_actual_ratio_tensor_soft_source_physical_bound dual hinput ha hab hlen hεsource
      f g hf hg hΦ hΦs hc hc1 he hκ hθ hR hloss
  refine ⟨S,U,hS,hS2,hScap,hU,hUcap,?_⟩
  intro s u hs hss hu huu
  have hs2 : s<1/2 := hss.trans_lt hS2
  have hscap : s≤1/8 := hss.trans hScap
  have hucap : u≤1/8 := huu.trans hUcap
  have hloss1 : s/2+4*εsource+e≤rectangularSlack a b := by linarith
  have hloss2 : 3*s/4+u/4+4*εsource+e≤rectangularSlack a b := by linarith
  let D := C*a03SourceMellinBound R u
  have hD : 0≤D := by dsimp [D,a03SourceMellinBound]; positivity
  have hbound : ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) →
      (∀ j,‖α j‖≤R/Real.log T) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ‖a03ActualRatioSourceErrorMoment dual Φ c e T a b s u εsource θ σ α f g‖≤
        D*T^e*a03ActualSoftSourceGlobalMajorant T a b s u εsource θ f g := by
    filter_upwards [hphysical,eventually_ge_atTop (1:ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4*R))] with T hphysical hT hlog hlogR
    intro σ α hσ hα hroot
    have hL : 0<Real.log T := zero_lt_one.trans_le hlog
    have hαsmall : ∀ j,‖α j‖≤1/4 := fun j =>
      (hα j).trans ((div_le_iff₀ hL).mpr (by linarith))
    apply a03_actual_ratio_source_error_moment_bound hT hθ dual Φ c σ α f g
    intro v hv positive i hi
    have hk := (Finset.mem_product.mp hi).2
    apply a03_actual_ratio_source_restored_block_bound (zero_lt_one.trans_le hT) hlog hR hc.le hc1 hC
      dual positive Φ σ α hα v f g i hk
    intro hgood
    rcases hgood with ⟨hactive,hmsoft,hnsoft,hk1,hk3⟩
    obtain ⟨hk0,hactive0⟩ := a03_actual_source_restricted_domain hT hss huu f g i.2 hk hactive
    exact hphysical _ _ _ (boundaryActual_scale_ge_two_thirds (i.1 0))
      (boundaryActual_scale_ge_two_thirds (i.1 1)) (boundaryActual_scale_ge_two_thirds (i.1 2))
      i.2 hk0 hactive0 hmsoft hnsoft hk1 hk3 σ α hσ hαsmall hroot v hv positive _ _
  intro δ hδ
  have hsmall := (a03_actual_soft_source_restored_global_majorant_isLittleO
    ha hab hlen hs.le hscap hu hucap hεsource.le hθ hloss1 hloss2 f g hf hg).const_mul_left D
  filter_upwards [hbound,isLittleO_iff.mp hsmall hδ,
    a03_actual_ratio_source_finite_values_integrableOn dual hΦ hΦs hc hc1 he hκ hθ hR
      (hs2.trans (by norm_num)) a b u εsource f g,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4*R)),
    eventually_ge_atTop (1:ℝ)] with T hb hδb hi hlog hlogR hT
  intro σ α hσ hα hroot
  have hL : 0<Real.log T := zero_lt_one.trans_le hlog
  have hαsmall : ∀ j,‖α j‖≤1/4 := fun j =>
    (hα j).trans ((div_le_iff₀ hL).mpr (by linarith))
  have hip := hi σ α hσ hαsmall hroot false
  have hiz := hi σ α hσ hαsmall hroot true
  refine ⟨hip,hiz,?_⟩
  rw [←a03ActualRatioSourceErrorMoment_eq_physical_sub_zero (zero_lt_one.trans_le hT)
    dual Φ c e a b s u εsource θ σ α f g hip hiz]
  calc
    _≤D*T^e*a03ActualSoftSourceGlobalMajorant T a b s u εsource θ f g := hb σ α hσ hα hroot
    _≤‖D*(T^e*a03ActualSoftSourceGlobalMajorant T a b s u εsource θ f g)‖ := by
      rw [Real.norm_eq_abs]
      simpa only [mul_assoc] using le_abs_self (D*(T^e*a03ActualSoftSourceGlobalMajorant T a b s u εsource θ f g))
    _≤δ*T := by simpa only [Real.norm_of_nonneg (zero_le_one.trans hT)] using hδb

end
end Sechstmoment
