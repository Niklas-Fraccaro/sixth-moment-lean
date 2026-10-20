import SixthMoment.Numerator.U.Sources.GlobalReindex
import SixthMoment.Numerator.U.Sources.MomentIntegrability

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def a03ActualFiniteOffdiagonalGammaMoment (dual : Bool) (c T a b u θ : ℝ)
    (σ : MomentShifts) (f g Φ : ℝ→ℝ) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫ v in Icc (-θ*Real.log T) (θ*Real.log T),
    ∑ positive : Bool,a03ActualFiniteOffdiagonalMellinGrid dual positive c T a b u v f g Φ σ
      (a03SourceShifts dual T σ)

def a03ActualFiniteGammaZeroMoment (dual : Bool) (c T a b s u θ : ℝ)
    (σ : MomentShifts) (f g Φ : ℝ→ℝ) : ℂ :=
  (1/(2*Real.pi):ℂ)*a03ActualSourceGammaZeroMoment dual (fun x => (Φ x:ℂ)) c T a b s u θ σ f g

theorem a03ActualFiniteOffdiagonalGammaMoment_eq_source_add_far {T a b : ℝ} (hT : 1<T)
    (dual : Bool) (c s u θ : ℝ) (σ : MomentShifts) (f g Φ : ℝ→ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hsource : IntegrableOn (fun v => a03ActualSourceFiniteValue false dual (fun x => (Φ x:ℂ))
      c T a b s u v σ f g) (Icc (-θ*Real.log T) (θ*Real.log T)))
    (hfar : ∀ positive : Bool,IntegrableOn (fun v => a03ActualSourceFarResidualMellinGrid
      dual positive c T a b s u v f g Φ σ (a03SourceShifts dual T σ))
      (Icc (-θ*Real.log T) (θ*Real.log T))) :
    a03ActualFiniteOffdiagonalGammaMoment dual c T a b u θ σ f g Φ=
      (1/(2*Real.pi):ℂ)*a03ActualSourcePhysicalMoment dual (fun x => (Φ x:ℂ)) c T a b s u θ σ f g+
      ∑ positive : Bool,a03ActualSourceFarResidualContour dual positive c T a b s u θ f g Φ σ
        (a03SourceShifts dual T σ) := by
  have he : (fun v : ℝ => ∑ positive : Bool,a03ActualFiniteOffdiagonalMellinGrid
      dual positive c T a b u v f g Φ σ (a03SourceShifts dual T σ))=
      fun v : ℝ => a03ActualSourceFiniteValue false dual (fun x => (Φ x:ℂ)) c T a b s u v σ f g+
        ∑ positive : Bool,a03ActualSourceFarResidualMellinGrid dual positive c T a b s u v f g Φ σ
          (a03SourceShifts dual T σ) := by
    funext v
    rw [a03ActualSourceFiniteValue_eq_near_finite_grid hT dual f g Φ hf hg σ c s u v,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro positive _
    unfold a03ActualSourceFarResidualMellinGrid
    ring
  have hR := integrable_finsetSum (Finset.univ : Finset Bool) (fun positive _ => hfar positive)
  unfold a03ActualFiniteOffdiagonalGammaMoment
  rw [he,integral_add hsource hR,mul_add,integral_finsetSum _ (fun positive _ => hfar positive),Finset.mul_sum]
  rfl

theorem a03_actual_finite_offdiagonal_Gamma_minus_zeros (dual : Bool)
    (hinput : SeparatedQuadraticInput) {a b εsource εkernel c κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hεsource : 0<εsource)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1) (hεkernel : 4*c<εkernel)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hloss : 4*εsource+εkernel<rectangularSlack a b) :
    ∃ s u : ℝ,0<s ∧ s<1/2 ∧ s≤1/8 ∧ 0<u ∧ u≤1/8 ∧
      ∀ σ : MomentShifts,(∀ j,‖σ j‖≤R) →
        (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
        (fun T : ℝ => a03ActualFiniteOffdiagonalGammaMoment dual c T a b u θ σ f g Φ-
          a03ActualFiniteGammaZeroMoment dual c T a b s u θ σ f g Φ)=o[atTop] (fun T : ℝ => T) := by
  have hΦc : ContDiff ℝ ∞ (fun x => (Φ x:ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ.1
  have hΦs : tsupport (fun x => (Φ x:ℂ))⊆Icc 1 2 := (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦ.2
  obtain ⟨s,u,hs,hs2,hscap,hu,hucap,hsourceSmall⟩ :=
    a03_actual_source_physical_moment_sub_Gamma_zero dual hinput ha hab hlen hεsource f g hf hg
      hΦc hΦs hc hc1 hεkernel hκ hθ hR hloss
  have hs1 : s≤1 := hs2.le.trans (by norm_num)
  obtain ⟨C,hC,hfar⟩ := a03_actual_source_far_residual_contour_uniform_rapid hf hg hΦ hc hc1 hu
    hκ hθ hR hs hs1 0
  have hraw := rawMomentShifts_uniform_eventually_small hR (show (0:ℝ)<1/4 by norm_num)
  have hα (T : ℝ) (σ : MomentShifts) (hraw : ∀ j,‖rawMomentShifts T σ j‖≤1/4) :
      ∀ j,‖a03SourceShifts dual T σ j‖≤1/4 := by
    cases dual
    · exact hraw
    · exact bblrSixShifts_norm_le _ hraw 1
  refine ⟨s,u,hs,hs2,hscap,hu,hucap,?_⟩
  intro σ hσ hroot
  have hRsmall : (fun T : ℝ => ∑ positive : Bool,a03ActualSourceFarResidualContour
      dual positive c T a b s u θ f g Φ σ (a03SourceShifts dual T σ))=o[atTop] (fun T : ℝ => T) := by
    apply (IsBigO.of_bound (2*C) ?_).trans_isLittleO (isLittleO_const_id_atTop (1:ℝ))
    filter_upwards [hfar,hraw] with T hfar hraw
    simp only [norm_one,mul_one]
    calc
      _≤∑ positive : Bool,‖a03ActualSourceFarResidualContour dual positive c T a b s u θ f g Φ σ
          (a03SourceShifts dual T σ)‖ := norm_sum_le _ _
      _≤∑ _positive : Bool,C := by
        apply Finset.sum_le_sum
        intro positive _
        simpa only [neg_zero,Real.rpow_zero,mul_one] using
          (hfar σ (a03SourceShifts dual T σ) hσ (hα T σ (hraw σ hσ)) hroot dual positive).2
      _=_ := by simp [two_mul]
  have hcombined := ((hsourceSmall σ hσ hroot).const_mul_left (1/(2*Real.pi):ℂ)).add hRsmall
  apply hcombined.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [hfar,hraw,a03_actual_source_finite_values_integrableOn dual hΦc hΦs hc hc1 hεkernel hκ hθ hR
    (hs2.trans (by norm_num)) a b u f g,eventually_gt_atTop (1:ℝ)] with T hfar hraw hsource hT
  have he := a03ActualFiniteOffdiagonalGammaMoment_eq_source_add_far hT dual c s u θ σ f g Φ hf hg
    (hsource σ hσ hroot false)
    (fun positive => (hfar σ (a03SourceShifts dual T σ) hσ (hα T σ (hraw σ hσ)) hroot dual positive).1)
  rw [he]
  unfold a03ActualFiniteGammaZeroMoment
  ring

theorem a03_actual_finite_offdiagonal_Gamma_minus_zeros_of_source (dual : Bool)
    (hinput : SeparatedQuadraticInput) {a b κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ c s u : ℝ,0<c ∧ c≤1 ∧ 0<s ∧ s<1/2 ∧ s≤1/8 ∧ 0<u ∧ u≤1/8 ∧
      ∀ σ : MomentShifts,(∀ j,‖σ j‖≤R) →
        (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
        (fun T : ℝ => a03ActualFiniteOffdiagonalGammaMoment dual c T a b u θ σ f g Φ-
          a03ActualFiniteGammaZeroMoment dual c T a b s u θ σ f g Φ)=o[atTop] (fun T : ℝ => T) := by
  obtain ⟨hc,hc1,hkernel,hloss⟩ := a03_actual_source_slack_choices ha hab hlen
  obtain ⟨s,u,hs,hs2,hscap,hu,hucap,hsmall⟩ := a03_actual_finite_offdiagonal_Gamma_minus_zeros
    dual hinput ha hab hlen hc f g Φ hf hg hΦ hc hc1 hkernel hκ hθ hR hloss
  exact ⟨rectangularSlack a b/128,s,u,hc,hc1,hs,hs2,hscap,hu,hucap,hsmall⟩

end
end SixthMoment
