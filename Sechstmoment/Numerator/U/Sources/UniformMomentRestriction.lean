import Sechstmoment.Numerator.U.Sources.MomentIntegrability

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_actual_source_physical_moment_sub_Gamma_zero_uniform_smaller (dual : Bool)
    (hinput : SeparatedQuadraticInput) {a b εsource e c κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hεsource : 0<εsource)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    (hc : 0<c) (hc1 : c≤1) (he : 4*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R)
    (hloss : 4*εsource+e<rectangularSlack a b) :
    ∃ S U : ℝ,0<S ∧ S<1/2 ∧ S≤1/8 ∧ 0<U ∧ U≤1/8 ∧
      ∀ s u : ℝ,0<s → s≤S → 0<u → u≤U →
      ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,(∀ j,‖σ j‖≤R) →
        (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
        IntegrableOn (fun v => a03ActualSourceFiniteValue false dual Φ c T a b s u v σ f g)
          (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
        IntegrableOn (fun v => a03ActualSourceFiniteValue true dual Φ c T a b s u v σ f g)
          (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
        ‖a03ActualSourcePhysicalMoment dual Φ c T a b s u θ σ f g-
          a03ActualSourceGammaZeroMoment dual Φ c T a b s u θ σ f g‖≤δ*T := by
  obtain ⟨S,U,C,hS,hS2,hScap,hU,hUcap,hlossS,hlossU,hC,hphysical⟩ :=
    a03_actual_tensor_source_physical_bound dual hinput ha hab hlen hεsource
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
  have hbound : ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,(∀ j,‖σ j‖≤R) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ‖a03ActualSourceErrorMoment dual Φ c e T a b s u θ σ f g‖≤
        D*T^e*a03ActualSourceGlobalMajorant T a b s u εsource θ f g := by
    filter_upwards [hphysical,eventually_ge_atTop (1:ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hphysical hT hlog
    intro σ hσ hroot
    apply a03_actual_source_error_moment_bound hT hθ dual Φ c σ f g
    intro v hv positive i hi
    have hk := (Finset.mem_product.mp hi).2
    apply a03_actual_source_restored_block_bound (zero_lt_one.trans_le hT) hlog hR hc.le hc1 hC
      dual positive Φ σ hσ v f g i hk
    intro hactive
    obtain ⟨hk0,hactive0⟩ := a03_actual_source_restricted_domain hT hss huu f g i.2 hk hactive
    exact hphysical _ _ _ (boundaryActual_scale_ge_two_thirds (i.1 0))
      (boundaryActual_scale_ge_two_thirds (i.1 1)) (boundaryActual_scale_ge_two_thirds (i.1 2))
      i.2 hk0 hactive0 σ hσ hroot v hv positive
  intro δ hδ
  have hsmall := (a03_actual_source_restored_global_majorant_isLittleO
    ha hab hlen hs.le hscap hu hucap hεsource.le hθ hloss1 hloss2 f g hf hg).const_mul_left D
  filter_upwards [hbound,isLittleO_iff.mp hsmall hδ,
    a03_actual_source_finite_values_integrableOn dual hΦ hΦs hc hc1 he hκ hθ hR
      (hs2.trans (by norm_num)) a b u f g,eventually_ge_atTop (1:ℝ)] with T hb hδb hi hT
  intro σ hσ hroot
  have hip := hi σ hσ hroot false
  have hiz := hi σ hσ hroot true
  refine ⟨hip,hiz,?_⟩
  rw [←a03ActualSourceErrorMoment_eq_physical_sub_zero (zero_lt_one.trans_le hT)
    dual Φ c e a b s u θ σ f g hip hiz]
  calc
    _≤D*T^e*a03ActualSourceGlobalMajorant T a b s u εsource θ f g := hb σ hσ hroot
    _≤‖D*(T^e*a03ActualSourceGlobalMajorant T a b s u εsource θ f g)‖ := by
      rw [Real.norm_eq_abs]
      simpa only [mul_assoc] using le_abs_self (D*(T^e*a03ActualSourceGlobalMajorant T a b s u εsource θ f g))
    _≤δ*T := by simpa only [Real.norm_of_nonneg (zero_le_one.trans hT)] using hδb

end
end Sechstmoment
