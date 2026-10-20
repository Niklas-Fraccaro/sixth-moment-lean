import Sechstmoment.Numerator.U.Sources.OffdiagonalMoment
import Sechstmoment.Numerator.U.ZeroModes.Ratio.FourGammaZeroJoin

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03ActualFiniteFourRatioGammaZeroMoment (dual : Bool) (c T a b s u εsource θ : ℝ)
    (σ : MomentShifts) (f g Φ : ℝ→ℝ) : ℂ :=
  (1/(2*Real.pi):ℂ)*a03ActualFourRatioGammaZeroMoment dual (fun x => (Φ x:ℂ))
    c T a b s u εsource θ σ f g

theorem a03_actual_finite_offdiagonal_Gamma_sub_four_ratio_Gamma_zeros_uniform_smaller (dual : Bool)
    (hinput : SeparatedQuadraticInput) {a b εsource e c κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hεsource : 0<εsource)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1) (he : 12*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hloss : 4*εsource+e<rectangularSlack a b) :
    ∃ S U : ℝ,0<S ∧ S<1/2 ∧ S≤1/8 ∧ 0<U ∧ U≤1/8 ∧
      ∀ s u : ℝ,0<s → s≤S → 0<u → u≤U →
      ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,(∀ j,‖σ j‖≤R) →
        (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
        ‖a03ActualFiniteOffdiagonalGammaMoment dual c T a b u θ σ f g Φ-
          a03ActualFiniteFourRatioGammaZeroMoment dual c T a b s u εsource θ σ f g Φ‖≤δ*T := by
  obtain ⟨S,U,hS,hS2,hScap,hU,hUcap,hsource⟩ :=
    a03_actual_source_physical_moment_sub_four_ratio_Gamma_zeros_uniform_smaller dual hinput ha hab hlen hεsource
      f g Φ hf hg hΦ hc hc1 he hκ hθ hR hloss
  refine ⟨S,U,hS,hS2,hScap,hU,hUcap,?_⟩
  intro s u hs hsS hu huU δ hδ
  have hs2 : s<1/2 := hsS.trans_lt hS2
  have hs1 : s≤1 := hs2.le.trans (by norm_num)
  have hΦc : ContDiff ℝ ∞ (fun x => (Φ x:ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ.1
  have hΦs : tsupport (fun x => (Φ x:ℂ))⊆Icc 1 2 := (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦ.2
  have he4 : 4*c<e := by linarith
  obtain ⟨C,_hC,hfar⟩ := a03_actual_source_far_residual_contour_uniform_rapid hf hg hΦ hc hc1 hu
    hκ hθ hR hs hs1 0
  filter_upwards [hsource s u hs hsS hu huU (δ/2) (by positivity),hfar,
    a03_actual_source_finite_values_integrableOn dual hΦc hΦs hc hc1 he4 hκ hθ hR
      (hs2.trans (by norm_num)) a b u f g,
    rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/4),
    eventually_gt_atTop (1:ℝ),eventually_ge_atTop (4*C/δ)] with T hb hf0 hi hraw hT hlarge
  intro σ hσ hroot
  have hα : ∀ j,‖a03SourceShifts dual T σ j‖≤1/4 := by
    cases dual
    · exact hraw σ hσ
    · exact bblrSixShifts_norm_le _ (hraw σ hσ) 1
  have hfarT (positive : Bool) := hf0 σ (a03SourceShifts dual T σ) hσ hα hroot dual positive
  have heq := a03ActualFiniteOffdiagonalGammaMoment_eq_source_add_far hT dual c s u θ σ f g Φ hf hg
    (hi σ hσ hroot false) (fun positive => (hfarT positive).1)
  have hfarbound : ‖∑ positive : Bool,a03ActualSourceFarResidualContour dual positive c T a b s u θ f g Φ σ
      (a03SourceShifts dual T σ)‖≤(δ/2)*T := by
    apply (norm_sum_le _ _).trans
    calc
      _≤∑ _positive : Bool,C := Finset.sum_le_sum (fun positive _ => by
        simpa only [neg_zero,Real.rpow_zero,mul_one] using (hfarT positive).2)
      _=2*C := by simp only [Fintype.sum_bool]; ring
      _≤(δ/2)*T := by have hx := (div_le_iff₀ hδ).mp hlarge; nlinarith
  have hconst : ‖(1/(2*Real.pi):ℂ)‖≤1 := by
    rw [norm_div,norm_one,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    exact (div_le_one (by positivity : (0:ℝ)<2*Real.pi)).mpr (by linarith [Real.pi_gt_three])
  rw [heq]
  unfold a03ActualFiniteFourRatioGammaZeroMoment
  have halg (z X Y R : ℂ) : z*X+R-z*Y=z*(X-Y)+R := by ring
  rw [halg]
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  exact (add_le_add ((mul_le_mul hconst (hb σ hσ hroot) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
    hfarbound).trans_eq (by ring)

end
end Sechstmoment
