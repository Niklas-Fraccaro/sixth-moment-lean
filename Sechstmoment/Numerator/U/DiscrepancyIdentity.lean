import Sechstmoment.Numerator.U.Replacement.ErrorBound
import Sechstmoment.Numerator.U.Replacement.VStar.DiagonalMoment

namespace Sechstmoment
open Complex Source MeasureTheory Filter Set
open scoped BigOperators Topology
noncomputable section

def a03LiteralCrossedDiscrepancy (T a b : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ → ℝ) : ℂ :=
  rectangularVStarSelectedMoment false T a b σ f g Φ -
    ∑ j : Fin 4, bblrIndexedMainTerm ⟨j.val+2,by omega⟩ T a b
      (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ

theorem a03SixMainTerms_split (T a b : ℝ) (α : MomentShifts) (G : ℂ → ℂ)
    (f g Φ : ℝ → ℝ) :
    bblrSixMainTerms T a b α G f g Φ =
      bblrIndexedMainTerm 0 T a b α G f g Φ +
      bblrIndexedMainTerm 1 T a b α G f g Φ +
      ∑ j : Fin 4, bblrIndexedMainTerm ⟨j.val+2,by omega⟩ T a b α G f g Φ := by
  rw [bblrSixMainTerms_eq_indexed]
  simp only [Fin.sum_univ_succ]
  norm_num
  ring

theorem a03FinalDiscrepancy_eventual_identity
    {a b : ℝ} (ha : 0<a) (hab : a≤b) (hrect : 3*a+5*b<2)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) :
    ∀ᶠ T : ℝ in atTop, ∀ σ∈K,
      bblrMomentDiscrepancy T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ =
        rectangularAFEIntegratedError T (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ +
        rectangularOriginalWeightReplacementError T σ f g Φ +
        rectangularDualWeightReplacementError T σ f g Φ +
        rectangularDualPhaseReplacementError T σ f g Φ +
        a03LiteralCrossedDiscrepancy T a b σ f g Φ := by
  obtain ⟨C,hC,hparts⟩ := rectangularReplacementErrorParts_uniform_power_bound
    ha hab hrect K hK δ hδ hroot f g Φ hf hg hΦ
  obtain ⟨D,hD,hfull⟩ := rectangularCompleteReplacementError_uniform_power_bound
    ha hab hrect K hK δ hδ hroot f g Φ hf hg hΦ
  have hdiag := rectangularVStarAFEMoment_eventually_eq_diagonal_and_offdiagonal
    K hK δ hδ hroot a b f g Φ hf hg hΦ
  filter_upwards [hparts,hfull,hdiag,
    compactNormalizedShifts_eventually_norm_small K hK (1/8) (by norm_num),
    eventually_gt_atTop (1:ℝ)] with T hp hu hd hs hT
  intro σ hσ
  have hafe := rectangularFullAFEMoment_actual_identity hT σ (fun j => (hs σ hσ j).trans_lt (by norm_num))
    a b f g Φ hf hg hΦ
  have h₀ := (hp σ hσ 0).1
  have h₁ := (hp σ hσ 1).1
  have h₂ := (hp σ hσ 2).1
  simp only [rectangularReplacementErrorPartIntegrand, ite_eq_left, ite_false,
    show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide] at h₀ h₁ h₂
  have he := rectangularReplacementErrors_sum_eq_full_difference T σ f g Φ
    (hu σ hσ).1 (hu σ hσ).2.1 h₀ h₁ h₂
  have hz := (hd σ hσ).2.2
  rw [hafe.2,hz] at he
  unfold bblrMomentDiscrepancy a03LiteralCrossedDiscrepancy
  rw [a03SixMainTerms_split]
  linear_combination -he

theorem a03FinalDiscrepancy_minus_crossed_uniform_oT
    (hsource : BBLRv1FixedApproximateFEInput)
    {a b : ℝ} (ha : 0<a) (hab : a≤b) (hrect : 3*a+5*b<2)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ T : ℝ in atTop, ∀ σ∈K,
      ‖bblrMomentDiscrepancy T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ -
        a03LiteralCrossedDiscrepancy T a b σ f g Φ‖≤ε*T := by
  have hi := a03FinalDiscrepancy_eventual_identity ha hab hrect K hK δ hδ hroot
    f g Φ hf hg hΦ
  have hae := rectangular_concrete_AFE_integrated_uniform_negligible hsource
    K hK δ hδ hroot a b f g Φ hf hg hΦ
  have hw := rectangularFullWeightAndDualPhaseErrors_uniform_oT
    ha hab hrect K hK δ hδ hroot f g Φ hf hg hΦ
  intro ε hε
  filter_upwards [hi,hae (ε/2) (by positivity),hw (ε/2) (by positivity)] with T hi ha hw
  intro σ hσ
  rw [hi σ hσ]
  have he : rectangularAFEIntegratedError T (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ +
      rectangularOriginalWeightReplacementError T σ f g Φ +
      rectangularDualWeightReplacementError T σ f g Φ +
      rectangularDualPhaseReplacementError T σ f g Φ +
      a03LiteralCrossedDiscrepancy T a b σ f g Φ - a03LiteralCrossedDiscrepancy T a b σ f g Φ =
      rectangularAFEIntegratedError T (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ +
      rectangularOriginalWeightReplacementError T σ f g Φ +
      rectangularDualWeightReplacementError T σ f g Φ +
      rectangularDualPhaseReplacementError T σ f g Φ := by ring
  rw [he]
  have hn := (norm_add_le
    (rectangularAFEIntegratedError T (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ +
      rectangularOriginalWeightReplacementError T σ f g Φ +
      rectangularDualWeightReplacementError T σ f g Φ)
    (rectangularDualPhaseReplacementError T σ f g Φ))
  have hn₁ := norm_add_le
    (rectangularAFEIntegratedError T (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ +
      rectangularOriginalWeightReplacementError T σ f g Φ)
    (rectangularDualWeightReplacementError T σ f g Φ)
  have hn₀ := norm_add_le
    (rectangularAFEIntegratedError T (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ)
    (rectangularOriginalWeightReplacementError T σ f g Φ)
  linarith [ha σ hσ,hw σ hσ]

theorem a03Final_uniform_oT_iff_crossed
    (hsource : BBLRv1FixedApproximateFEInput)
    {a b : ℝ} (ha : 0<a) (hab : a≤b) (hrect : 3*a+5*b<2)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) :
    (∀ ε : ℝ, 0<ε → ∀ᶠ T : ℝ in atTop, ∀ σ∈K,
      ‖bblrMomentDiscrepancy T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ‖≤ε*T) ↔
    (∀ ε : ℝ, 0<ε → ∀ᶠ T : ℝ in atTop, ∀ σ∈K,
      ‖a03LiteralCrossedDiscrepancy T a b σ f g Φ‖≤ε*T) := by
  have he := a03FinalDiscrepancy_minus_crossed_uniform_oT hsource ha hab hrect
    K hK δ hδ hroot f g Φ hf hg hΦ
  constructor
  · intro hm ε hε
    filter_upwards [he (ε/2) (by positivity),hm (ε/2) (by positivity)] with T he hm
    intro σ hσ
    have hn := norm_sub_le
      (bblrMomentDiscrepancy T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ)
      (bblrMomentDiscrepancy T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ -
        a03LiteralCrossedDiscrepancy T a b σ f g Φ)
    simp only [sub_sub_cancel] at hn
    linarith [he σ hσ,hm σ hσ]
  · intro hm ε hε
    filter_upwards [he (ε/2) (by positivity),hm (ε/2) (by positivity)] with T he hm
    intro σ hσ
    have hn := norm_add_le
      (bblrMomentDiscrepancy T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ -
        a03LiteralCrossedDiscrepancy T a b σ f g Φ)
      (a03LiteralCrossedDiscrepancy T a b σ f g Φ)
    simp only [sub_add_cancel] at hn
    linarith [he σ hσ,hm σ hσ]

end
end Sechstmoment
