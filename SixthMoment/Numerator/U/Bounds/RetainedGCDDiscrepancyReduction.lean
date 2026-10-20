import SixthMoment.Numerator.U.Bounds.FourRatioGammaDiscrepancyReduction
import SixthMoment.Numerator.U.ZeroModes.Ratio.SevenGridSpectralTail

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 300000

def a03RetainedGCDCrossedDiscrepancy (T a b s u : ℝ)
    (σ : MomentShifts) (f g Φ : ℝ→ℝ) : ℂ :=
  (∑ dual : Bool,a03ActualFourRetainedRatioGCDVStarFinite dual (fun x => (Φ x:ℂ))
    T a b s u (rectangularSlack a b/128) σ f g)-
      ∑j : Fin 4,bblrIndexedMainTerm ⟨j.val+2,by omega⟩ T a b
        (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ

theorem a03FinalDiscrepancy_minus_retainedGCDCrossed_uniform_oT
    (hAFE : BBLRv1FixedApproximateFEInput) (hSource : SeparatedQuadraticInput) {a b θ : ℝ}
    (ha : 0≤a) (hab : a≤b) (hrect : 3*a+5*b<2) (hθ : 0<θ)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (hroot : ∀σ∈K,∀j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∃ S U : ℝ,0<S ∧ S<1/2 ∧ S≤1/8 ∧ 0<U ∧ U≤1/8 ∧
      ∀s u : ℝ,0<s → s≤S → 0<u → u≤U →
        ∀δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀σ∈K,
          ‖bblrMomentDiscrepancy T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ-
            a03RetainedGCDCrossedDiscrepancy T a b s u σ f g Φ‖≤δ*T := by
  obtain ⟨S,U,hS,hS2,hScap,hU,hUcap,hsource⟩ :=
    a03FinalDiscrepancy_minus_fourRatioGammaCrossed_uniform_oT hAFE hSource ha hab hrect hθ
      K hK hκ hroot f g Φ hf hg hΦ
  obtain ⟨B,hB⟩ := hK.isBounded.exists_norm_le
  let R := max B 0
  have hR : 0≤R := le_max_right _ _
  have hc : 0<rectangularSlack a b/512 := by
    have hd := (rectangular_slack_bounds hab hrect).1
    positivity
  refine ⟨S,U,hS,hS2,hScap,hU,hUcap,?_⟩
  intro s u hs hsS hu huU δ hδ
  filter_upwards [hsource s u hs hsS hu huU (δ/3) (by positivity),
    a03_actual_four_ratio_Gamma_zero_sub_linear_uniform_slack ha hab hrect hs.le (hsS.trans hScap)
      hu (huU.trans hUcap) f g Φ hf hg hΦ hκ hθ.le hR (δ/3) (by positivity),
    a03_actual_four_ratio_linear_zero_sub_retained_GCD_compact_uniform_oT K hK hκ hroot
      ha (ha.trans hab) hs.le hu f g Φ hf hg hΦ hc hθ (rectangularSlack a b/128) (δ/3) (by positivity)]
    with T hsource hGamma hVStar
  intro σ hσ
  have hσR (j : Fin 4) : ‖σ j‖≤R := ((norm_le_pi_norm σ j).trans (hB σ hσ)).trans (le_max_left _ _)
  have he : bblrMomentDiscrepancy T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ-
      a03RetainedGCDCrossedDiscrepancy T a b s u σ f g Φ=
      (bblrMomentDiscrepancy T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ-
        a03FourRatioGammaCrossedDiscrepancy T a b s u θ σ f g Φ)+
      ((∑ dual : Bool,a03ActualFiniteFourRatioGammaZeroMoment dual (rectangularSlack a b/512)
          T a b s u (rectangularSlack a b/128) θ σ f g Φ)-
        ∑ dual : Bool,a03ActualFiniteFourRatioLinearZeroMoment dual (rectangularSlack a b/512)
          T a b s u (rectangularSlack a b/128) θ σ f g Φ)+
      ((∑ dual : Bool,a03ActualFiniteFourRatioLinearZeroMoment dual (rectangularSlack a b/512)
          T a b s u (rectangularSlack a b/128) θ σ f g Φ)-
        ∑ dual : Bool,a03ActualFourRetainedRatioGCDVStarFinite dual (fun x => (Φ x:ℂ))
          T a b s u (rectangularSlack a b/128) σ f g) := by
    unfold a03RetainedGCDCrossedDiscrepancy a03FourRatioGammaCrossedDiscrepancy
    simp only [Fintype.sum_bool]
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  calc
    _≤((δ/3)*T+(δ/3)*T)+(δ/3)*T :=
      add_le_add ((norm_add_le _ _).trans (add_le_add (hsource σ hσ)
        (hGamma σ hσR (hroot σ hσ)))) (hVStar σ hσ)
    _=δ*T := by ring

end
end SixthMoment
