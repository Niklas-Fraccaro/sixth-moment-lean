import Mathlib.Analysis.Normed.Group.Bounded
import Sechstmoment.Analysis.Asymptotics.PowerLog
import Sechstmoment.Numerator.U.Reconstruction.RectangularAFEGrouping
import Sechstmoment.Numerator.U.Replacement.GaussianAdmissible
import Sechstmoment.Numerator.U.Replacement.GaussianCoefficientGrowth

/-! Instantiation of the fixed-G source input for the actual pole killer.
All finite-basis, convergence and coefficient-growth steps are own proofs. -/

namespace Sechstmoment.Source
open Complex MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section

theorem compactNormalizedShifts_eventually_real_small (K : Set MomentShifts)
    (hK : IsCompact K) :
    ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ j, |(rawMomentShifts T σ j).re| < 1/2 := by
  obtain ⟨B, hB⟩ := hK.isBounded.exists_norm_le
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_gt_atTop (2*max B 0+1))] with T hT
  intro σ hσ j
  have hL : 0 < Real.log T := by linarith [le_max_right B 0]
  have hj : |(σ j).re| ≤ max B 0 :=
    ((Complex.abs_re_le_norm _).trans ((norm_le_pi_norm σ j).trans (hB σ hσ))).trans
      (le_max_left B 0)
  simp only [rawMomentShifts, Complex.div_ofReal_re, abs_div, abs_of_pos hL]
  apply (div_lt_iff₀ hL).mpr
  linarith

theorem fixedGaussianBasis_analytic_receipt (K : Set MomentShifts) (hK : IsCompact K) :
    BBLRFiniteBasisAnalyticReceipt fixedGaussianBasis polarPoleBasisWeights K := by
  filter_upwards [compactNormalizedShifts_eventually_real_small K hK] with T hsmall
  intro σ hσ t ht
  let α := rawMomentShifts T σ
  have hα : ∀ j, -1/2 < (α j).re := by
    intro j
    have h := (abs_lt.mp (hsmall σ hσ j)).1
    dsimp [α]
    linarith
  have hαd : ∀ j, -1/2 < (bblrSixShifts α 1 j).re := by
    intro j
    have hu (k : Fin 4) : (α k).re < 1/2 := (abs_lt.mp (hsmall σ hσ k)).2
    fin_cases j <;> simp [bblrSixShifts] <;> linarith [hu 0, hu 1, hu 2, hu 3]
  have hGI (i : Fin 25) : Integrable (fun v : ℝ => ‖fixedGaussianBasis i (1+(v : ℂ)*I)‖) :=
    rectangular_BBLR_weight_vertical_integrable (fixedGaussianBasis i) (fun _ => 0)
      (fixedGaussianBasis_admissible i)
  have hc (i : Fin 25) : Continuous (fixedGaussianBasis i) :=
    (fixedGaussianBasis_differentiable i).continuous
  have hx (n : Fin 4 → ℕ) : 0 < (positiveQuadProduct n : ℝ) := by
    unfold positiveQuadProduct
    positivity
  refine ⟨polarPoleBasisWeights_sum T σ, ?_, ?_, ?_, ?_⟩
  · exact fun i n => bblrVerticalIntegrand_integrable _ (hc i) (hGI i) α _ t (hx n) hα
  · exact fun i n => bblrVerticalIntegrand_integrable _ (hc i) (hGI i) _ _ t (hx n) hαd
  · exact fun i => bblrAFESummand_summable _ (hc i) (hGI i) α t hα
  · exact fun i => bblrAFESummand_summable _ (hc i) (hGI i) _ t hαd

/-- Every requested power-decaying AFE remainder for the concrete G_T
follows from only the literal fixed-G source boundary. The normalized pure
root gap is stated explicitly, so uniformity near collisions is not assumed. -/
theorem polarPoleKiller_AFE_uniform_remainder (hsource : BBLRv1FixedApproximateFEInput)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ σ ∈ K, ∀ k : PurePolarIndex, δ ≤ ‖normalizedPurePolarRoot σ k‖)
    (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ t ∈ Icc T (2*T),
      ‖bblrAFEDiscrepancy (polarPoleKiller T σ) (rawMomentShifts T σ) t‖ ≤
        C*T^(-(A : ℝ)) := by
  let D : ℝ := 1+48*(1+1/δ^2)^24
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hlog : ∀ᶠ T : ℝ in atTop, (Real.log T)^48 ≤ T := by
    have h := (log_pow_isLittleO_rpow 48 (δ := 1) zero_lt_one).bound zero_lt_one
    filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with T hT hpos
    simpa only [Real.rpow_one, Real.norm_eq_abs,
      abs_of_pos (zero_lt_one.trans hpos), abs_of_nonneg (by positivity : 0 ≤ (Real.log T)^48),
      one_mul] using hT
  have hw : ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∑ i, ‖polarPoleBasisWeights T σ i‖ ≤ D*T^1 := by
    filter_upwards [hlog, eventually_gt_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with T hlog hT hL
    intro σ hσ
    calc
      _ ≤ D*(Real.log T)^48 := polarPoleBasisWeights_log_growth hT hL hδ σ (hρ σ hσ)
      _ ≤ D*T^1 := by simpa using mul_le_mul_of_nonneg_left hlog hD
  obtain ⟨C, hC, hb⟩ := bblrAFE_fixed_basis_uniform_remainder hsource fixedGaussianBasis
    fixedGaussianBasis_admissible K hK polarPoleBasisWeights
    (fixedGaussianBasis_analytic_receipt K hK) 1 D hD hw A
  refine ⟨C, hC, hb.mono ?_⟩
  intro T hT σ hσ t ht
  rw [polarPoleKiller_fixed_basis]
  exact hT σ hσ t ht

end
end Sechstmoment.Source
