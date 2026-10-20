import SixthMoment.Numerator.U.Sources.FiniteGammaDiscrepancyReduction
import SixthMoment.Numerator.U.ZeroModes.Ratio.OffdiagonalGammaMoment

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 1000000

def a03FourRatioGammaCrossedDiscrepancy (T a b s u θ : ℝ)
    (σ : MomentShifts) (f g Φ : ℝ→ℝ) : ℂ :=
  a03ActualFiniteFourRatioGammaZeroMoment false (rectangularSlack a b/512) T a b s u
      (rectangularSlack a b/128) θ σ f g Φ+
    a03ActualFiniteFourRatioGammaZeroMoment true (rectangularSlack a b/512) T a b s u
      (rectangularSlack a b/128) θ σ f g Φ-
        ∑ j : Fin 4,bblrIndexedMainTerm ⟨j.val+2,by omega⟩ T a b
          (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ

theorem a03FinalDiscrepancy_minus_fourRatioGammaCrossed_uniform_oT
    (hAFE : BBLRv1FixedApproximateFEInput) (hSource : SeparatedQuadraticInput) {a b θ : ℝ}
    (ha : 0≤a) (hab : a≤b) (hrect : 3*a+5*b<2) (hθ : 0<θ)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (hroot : ∀ σ∈K,∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∃ S U : ℝ,0<S ∧ S<1/2 ∧ S≤1/8 ∧ 0<U ∧ U≤1/8 ∧
      ∀ s u : ℝ,0<s → s≤S → 0<u → u≤U →
        ∀ ε : ℝ,0<ε → ∀ᶠ T : ℝ in atTop,∀ σ∈K,
          ‖bblrMomentDiscrepancy T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ-
            a03FourRatioGammaCrossedDiscrepancy T a b s u θ σ f g Φ‖≤ε*T := by
  have hd := (rectangular_slack_bounds hab hrect).1
  have hc : 0<rectangularSlack a b/512 := by positivity
  have hc1 : rectangularSlack a b/512≤1 := by dsimp [rectangularSlack]; linarith
  have he : 12*(rectangularSlack a b/512)<rectangularSlack a b/16 := by linarith
  have hεs : 0<rectangularSlack a b/128 := by positivity
  have hloss : 4*(rectangularSlack a b/128)+rectangularSlack a b/16<rectangularSlack a b := by linarith
  obtain ⟨B,hB⟩ := hK.isBounded.exists_norm_le
  let R := max B 0
  have hR : 0≤R := le_max_right _ _
  have hσR (σ : MomentShifts) (hσ : σ∈K) (j : Fin 4) : ‖σ j‖≤R :=
    ((norm_le_pi_norm σ j).trans (hB σ hσ)).trans (le_max_left _ _)
  obtain ⟨S₀,U₀,hS₀,hS₀2,hS₀cap,hU₀,hU₀cap,h₀⟩ :=
    a03_actual_finite_offdiagonal_Gamma_sub_four_ratio_Gamma_zeros_uniform_smaller false hSource
      ha hab hrect hεs f g Φ hf hg hΦ hc hc1 he hκ hθ.le hR hloss
  obtain ⟨S₁,U₁,hS₁,_hS₁2,_hS₁cap,hU₁,_hU₁cap,h₁⟩ :=
    a03_actual_finite_offdiagonal_Gamma_sub_four_ratio_Gamma_zeros_uniform_smaller true hSource
      ha hab hrect hεs f g Φ hf hg hΦ hc hc1 he hκ hθ.le hR hloss
  refine ⟨min S₀ S₁,min U₀ U₁,lt_min hS₀ hS₁,(min_le_left _ _).trans_lt hS₀2,
    (min_le_left _ _).trans hS₀cap,lt_min hU₀ hU₁,(min_le_left _ _).trans hU₀cap,?_⟩
  intro s u hs hsS hu huU ε hε
  filter_upwards [a03FinalDiscrepancy_minus_finiteGammaCrossed_uniform_oT_of_source hAFE
    ha hab hrect hu hθ K hK hκ hroot f g Φ hf hg hΦ (ε/3) (by positivity),
    h₀ s u hs (hsS.trans (min_le_left _ _)) hu (huU.trans (min_le_left _ _)) (ε/3) (by positivity),
    h₁ s u hs (hsS.trans (min_le_right _ _)) hu (huU.trans (min_le_right _ _)) (ε/3) (by positivity)]
      with T hknown hfalse htrue
  intro σ hσ
  have heq : bblrMomentDiscrepancy T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ-
      a03FourRatioGammaCrossedDiscrepancy T a b s u θ σ f g Φ=
    (bblrMomentDiscrepancy T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ-
      a03FiniteGammaCrossedDiscrepancy (rectangularSlack a b/512) T a b u θ σ f g Φ)+
      (a03ActualFiniteOffdiagonalGammaMoment false (rectangularSlack a b/512) T a b u θ σ f g Φ-
        a03ActualFiniteFourRatioGammaZeroMoment false (rectangularSlack a b/512) T a b s u
          (rectangularSlack a b/128) θ σ f g Φ)+
      (a03ActualFiniteOffdiagonalGammaMoment true (rectangularSlack a b/512) T a b u θ σ f g Φ-
        a03ActualFiniteFourRatioGammaZeroMoment true (rectangularSlack a b/512) T a b s u
          (rectangularSlack a b/128) θ σ f g Φ) := by
    unfold a03FourRatioGammaCrossedDiscrepancy a03FiniteGammaCrossedDiscrepancy
    ring
  rw [heq]
  apply (norm_add_le _ _).trans
  calc
    _≤((ε/3)*T+(ε/3)*T)+(ε/3)*T :=
      add_le_add ((norm_add_le _ _).trans (add_le_add (hknown σ hσ)
        (hfalse σ (hσR σ hσ) (hroot σ hσ)))) (htrue σ (hσR σ hσ) (hroot σ hσ))
    _=ε*T := by ring

end
end SixthMoment
