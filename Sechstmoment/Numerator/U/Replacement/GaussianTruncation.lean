import Sechstmoment.Numerator.U.Replacement.GaussianAFETail

/-! Exact truncation of the actual Gaussian-weighted BBLR V integrals and
both fourfold AFE series, with the proved power-decaying tail retained. -/

namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section

def bblrGaussianVCore (T : ℝ) (σ α : MomentShifts) (x t R : ℝ) : ℂ :=
  (1/(2*Real.pi) : ℂ)*
    ∫ v in {v : ℝ | R < |v|}ᶜ, bblrVerticalIntegrand (polarPoleKiller T σ) α x t v

def bblrGaussianAFECoreSummand (T : ℝ) (σ α : MomentShifts) (t R : ℝ)
    (n : Fin 4 → ℕ) : ℂ :=
  ((((n 0+1)*(n 1+1) : ℕ) : ℂ)/(((n 2+1)*(n 3+1) : ℕ) : ℂ))^(-(t : ℂ)*I)*
    bblrGaussianVCore T σ α (positiveQuadProduct n) t R /
      ∏ j : Fin 4, (n j+1 : ℂ)^(1/2+α j)

def bblrGaussianAFECore (T : ℝ) (σ α : MomentShifts) (t R : ℝ) : ℂ :=
  ∑' n : Fin 4 → ℕ, bblrGaussianAFECoreSummand T σ α t R n

private theorem small_norm_real_lower (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    ∀ j, -1/2 < (α j).re := by
  intro j
  have h := (abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))).1
  linarith

theorem bblrGaussianV_core_add_tail (T : ℝ) (σ α : MomentShifts) (x t R : ℝ)
    (hx : 0 < x) (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    bblrV (polarPoleKiller T σ) α x t =
      bblrGaussianVCore T σ α x t R+bblrGaussianVTail T σ α x t R := by
  have hi := bblrVerticalIntegrand_integrable (polarPoleKiller T σ)
    (polarPoleKiller_differentiable T σ).continuous
    (polarPoleKiller_vertical_integrable T σ 1).norm α x t hx
    (small_norm_real_lower α hα)
  have hs : MeasurableSet {v : ℝ | R < |v|} :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  have he := integral_add_compl hs hi
  change (1/(2*Real.pi) : ℂ)*(∫ v : ℝ, bblrVerticalIntegrand (polarPoleKiller T σ) α x t v) = _
  unfold bblrGaussianVCore bblrGaussianVTail
  rw [← he]
  ring

theorem bblrGaussianAFESummand_core_add_tail (T : ℝ) (σ α : MomentShifts) (t R : ℝ)
    (hα : ∀ j, ‖α j‖ ≤ 1/4) (n : Fin 4 → ℕ) :
    bblrAFESummand (polarPoleKiller T σ) α t n =
      bblrGaussianAFECoreSummand T σ α t R n+bblrGaussianAFETailSummand T σ α t R n := by
  have hx : 0 < (positiveQuadProduct n : ℝ) := by unfold positiveQuadProduct; positivity
  unfold bblrAFESummand bblrGaussianAFECoreSummand bblrGaussianAFETailSummand
  rw [bblrGaussianV_core_add_tail T σ α _ t R hx hα]
  ring

theorem bblrGaussianAFECoreSummand_summable (T : ℝ) (σ α : MomentShifts) (t R : ℝ)
    (ht : 0 ≤ t) (hR : 0 ≤ R) (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    Summable (bblrGaussianAFECoreSummand T σ α t R) := by
  have hs := bblrAFESummand_summable (polarPoleKiller T σ)
    (polarPoleKiller_differentiable T σ).continuous
    (polarPoleKiller_vertical_integrable T σ 1).norm α t (small_norm_real_lower α hα)
  have ht' := bblrGaussianAFETailSummand_summable T σ α t R ht hR hα
  have he : bblrGaussianAFECoreSummand T σ α t R =
      fun n => bblrAFESummand (polarPoleKiller T σ) α t n-
        bblrGaussianAFETailSummand T σ α t R n := by
    funext n
    rw [bblrGaussianAFESummand_core_add_tail T σ α t R hα n]
    ring
  rw [he]
  exact hs.sub ht'

theorem bblrGaussianAFE_core_add_tail (T : ℝ) (σ α : MomentShifts) (t R : ℝ)
    (ht : 0 ≤ t) (hR : 0 ≤ R) (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    bblrAFESum (polarPoleKiller T σ) α t =
      bblrGaussianAFECore T σ α t R+bblrGaussianAFETail T σ α t R := by
  unfold bblrAFESum bblrGaussianAFECore bblrGaussianAFETail
  simp_rw [bblrGaussianAFESummand_core_add_tail T σ α t R hα]
  exact (bblrGaussianAFECoreSummand_summable T σ α t R ht hR hα).tsum_add
    (bblrGaussianAFETailSummand_summable T σ α t R ht hR hα)

theorem bblrGaussianAFE_truncation_uniform_raw_error (K : Set MomentShifts)
    (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ σ ∈ K, ∀ k : PurePolarIndex, δ ≤ ‖normalizedPurePolarRoot σ k‖)
    {ε : ℝ} (hε : 0 < ε) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ t ∈ Icc T (2*T),
      ‖bblrAFESum (polarPoleKiller T σ) (rawMomentShifts T σ) t-
        bblrGaussianAFECore T σ (rawMomentShifts T σ) t (T^ε)‖ ≤ C*T^(-(A : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := bblrGaussianAFETail_uniform_raw_power_bound K hK δ hδ hρ hε A
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,compactNormalizedShifts_eventually_norm_small K hK (1/4)
    (by norm_num),eventually_gt_atTop (0 : ℝ)] with T hb hs hT
  intro σ hσ t ht
  rw [bblrGaussianAFE_core_add_tail T σ _ t (T^ε) (by linarith [ht.1])
    (Real.rpow_pos_of_pos hT ε).le (hs σ hσ),add_sub_cancel_left]
  exact hb σ hσ t ht

theorem bblrGaussianAFE_truncation_uniform_six_shifts_error (K : Set MomentShifts)
    (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ σ ∈ K, ∀ k : PurePolarIndex, δ ≤ ‖normalizedPurePolarRoot σ k‖)
    {ε : ℝ} (hε : 0 < ε) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ k : Fin 6,
      ∀ t ∈ Icc T (2*T),
      ‖bblrAFESum (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) k) t-
        bblrGaussianAFECore T σ (bblrSixShifts (rawMomentShifts T σ) k) t (T^ε)‖ ≤
          C*T^(-(A : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := bblrGaussianAFETail_uniform_six_shifts_power_bound K hK δ hδ hρ hε A
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,compactNormalizedShifts_eventually_norm_small K hK (1/4)
    (by norm_num),eventually_gt_atTop (0 : ℝ)] with T hb hs hT
  intro σ hσ k t ht
  have hα : ∀ j, ‖bblrSixShifts (rawMomentShifts T σ) k j‖ ≤ 1/4 := by
    intro j
    have h := hs σ hσ
    fin_cases k <;> fin_cases j <;> simp [bblrSixShifts] <;>
      first | simpa using h 0 | simpa using h 1 | simpa using h 2 | simpa using h 3
  rw [bblrGaussianAFE_core_add_tail T σ _ t (T^ε) (by linarith [ht.1])
    (Real.rpow_pos_of_pos hT ε).le hα,add_sub_cancel_left]
  exact hb σ hσ k t ht

end
end Sechstmoment.Source
