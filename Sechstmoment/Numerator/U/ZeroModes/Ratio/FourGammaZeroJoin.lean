import Sechstmoment.Numerator.U.Sources.UniformMomentRestriction
import Sechstmoment.Numerator.U.ZeroModes.Ratio.BadSourceContourBudget
import Sechstmoment.Numerator.U.ZeroModes.Ratio.SourceTimePartition

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03ActualFourRatioGammaZeroMoment (dual : Bool) (Φ : ℝ→ℂ)
    (c T a b s u εsource θ : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∑ m : Bool,∑ n : Bool,a03ActualRatioSourceValueMoment true dual Φ c T a b s u εsource θ σ
    (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g

theorem a03SourceChamberShifts_norm_le_raw_scale {T R : ℝ} (hlog : 0<Real.log T)
    (dual : Bool) (σ : MomentShifts) (hσ : ∀ j,‖σ j‖≤R) (m n : Bool) :
    ∀ j,‖a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ) j‖≤R/Real.log T := by
  have hr : ∀ j,‖rawMomentShifts T σ j‖≤R/Real.log T := by
    intro j
    rw [rawMomentShifts,norm_div,Complex.norm_real,Real.norm_of_nonneg hlog.le]
    exact div_le_div_of_nonneg_right (hσ j) hlog.le
  have hs : ∀ j,‖a03SourceShifts dual T σ j‖≤R/Real.log T := by
    cases dual
    · exact hr
    · exact bblrSixShifts_norm_le _ hr 1
  exact fun j => hs (a03ZeroModePairPermutation m n j)

theorem a03SourceChamberShifts_norm_le_quarter {T : ℝ}
    (dual : Bool) (σ : MomentShifts) (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4) (m n : Bool) :
    ∀ j,‖a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ) j‖≤1/4 := by
  have hs : ∀ j,‖a03SourceShifts dual T σ j‖≤1/4 := by
    cases dual
    · exact hσ
    · exact bblrSixShifts_norm_le _ hσ 1
  exact fun j => hs (a03ZeroModePairPermutation m n j)

theorem a03_actual_source_physical_moment_sub_four_ratio_Gamma_zeros_uniform_smaller (dual : Bool)
    (hinput : SeparatedQuadraticInput) {a b εsource e c κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hεsource : 0<εsource)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1) (he : 12*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hloss : 4*εsource+e<rectangularSlack a b) :
    ∃ S U : ℝ,0<S ∧ S<1/2 ∧ S≤1/8 ∧ 0<U ∧ U≤1/8 ∧
      ∀ s u : ℝ,0<s → s≤S → 0<u → u≤U →
      ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,(∀ j,‖σ j‖≤R) →
        (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
        ‖a03ActualSourcePhysicalMoment dual (fun x => (Φ x:ℂ)) c T a b s u θ σ f g-
          a03ActualFourRatioGammaZeroMoment dual (fun x => (Φ x:ℂ)) c T a b s u εsource θ σ f g‖≤δ*T := by
  have hΦc : ContDiff ℝ ∞ (fun x => (Φ x:ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ.1
  have hΦs : tsupport (fun x => (Φ x:ℂ))⊆Icc 1 2 := (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦ.2
  obtain ⟨S,U,hS,hS2,hScap,hU,hUcap,hgood⟩ :=
    a03_actual_ratio_source_native_moment_sub_Gamma_zero_uniform_smaller dual hinput ha hab hlen hεsource
      f g hf hg hΦc hΦs hc hc1 he hκ hθ hR hloss
  refine ⟨S,U,hS,hS2,hScap,hU,hUcap,?_⟩
  intro s u hs hsS hu huU δ hδ
  have hs2 : s<1/2 := hsS.trans_lt hS2
  obtain ⟨C,_hC,hbad⟩ := a03_actual_ratio_bad_source_moment_uniform_rapid ha hab hlen hs.le hs2.le hu hεsource
    hf hg hΦ hc hc1 hκ hθ hR 0
  filter_upwards [hgood s u hs hsS hu huU (δ/8) (by positivity),hbad,
    rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/4),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    eventually_gt_atTop (1:ℝ),eventually_ge_atTop (8*C/δ)] with T hgoodT hb hraw hlog hT hlarge
  intro σ hσ hroot
  have hrawσ := hraw σ hσ
  have hCsmall : C≤(δ/8)*T := by
    have hx := (div_le_iff₀ hδ).mp hlarge
    nlinarith
  have hsingle (m n : Bool) :
      ‖a03ActualRatioTimeMoment false false dual (a03ZeroModeRatioWeight (rawMomentShifts T σ))
        c T a b s u θ σ (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g Φ-
        a03ActualRatioSourceValueMoment true dual (fun x => (Φ x:ℂ)) c T a b s u εsource θ σ
          (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g‖≤(δ/4)*T := by
    let α := a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)
    have hα := a03SourceChamberShifts_norm_le_quarter dual σ hrawσ m n
    have hαscale := a03SourceChamberShifts_norm_le_raw_scale (zero_lt_one.trans_le hlog) dual σ hσ m n
    have hgoodα := hgoodT σ α hσ hαscale hroot
    have hbadα := hb σ α hσ hα hroot dual
    have he := (a03ActualRatioTimeMoment_eq_source_add_bad hc hT dual f g Φ hf hg hΦ σ α hα hrawσ s u εsource θ).2.2
    rw [he]
    have halg (X Y Z : ℂ) : X+Y-Z=(X-Z)+Y := by ring
    rw [halg]
    apply (norm_add_le _ _).trans
    apply (add_le_add hgoodα.2.2 hbadα.2).trans
    simp only [neg_zero,Real.rpow_zero,mul_one]
    nlinarith
  rw [a03_actual_source_moment_four_chambers hc hT dual f g Φ hf hg hΦ σ hrawσ s u θ]
  unfold a03ActualFourRatioGammaZeroMoment
  rw [←Finset.sum_sub_distrib]
  simp_rw [←Finset.sum_sub_distrib]
  calc
    _≤∑ m : Bool,‖∑ n : Bool,
      (a03ActualRatioTimeMoment false false dual (a03ZeroModeRatioWeight (rawMomentShifts T σ))
        c T a b s u θ σ (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g Φ-
        a03ActualRatioSourceValueMoment true dual (fun x => (Φ x:ℂ)) c T a b s u εsource θ σ
          (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g)‖ := norm_sum_le _ _
    _≤∑ _m : Bool,∑ _n : Bool,(δ/4)*T := by
      apply Finset.sum_le_sum
      intro m _
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n _ => hsingle m n))
    _=δ*T := by simp only [Fintype.sum_bool]; ring

end
end Sechstmoment
