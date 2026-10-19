import Sechstmoment.Numerator.U.Reconstruction.RectangularActualMoment

/-! Exact diagonal and signed off-diagonal grouping of the actual integrated
AFE. All series convergence and Bochner interchange follow from the genuine
auxiliary class, rather than being assumed as block expansion receipts. -/

namespace Sechstmoment
open Complex Source MeasureTheory Set
open scoped BigOperators Topology
open Classical
noncomputable section

def rectangularAFESelected (G : ℂ → ℂ) (α : MomentShifts)
    (P : (Fin 4 → ℕ) → Prop) (t : ℝ) : ℂ :=
  ∑' n, if P n then bblrAFESummand G α t n else 0

private theorem filtered_summable (f : (Fin 4 → ℕ) → ℂ) (hf : Summable f)
    (P : (Fin 4 → ℕ) → Prop) : Summable (fun n => if P n then f n else 0) := by
  apply hf.norm.of_norm_bounded
  intro n
  by_cases hn : P n <;> simp [hn]

/-- A genuine selection of actual AFE terms can be interchanged with the
actual compact time integral, retaining the same fourfold majorant. -/
theorem rectangular_actual_AFE_selected_weighted_hasSum
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, -1/2 < (α j).re) (P : (Fin 4 → ℕ) → Prop)
    (w : ℝ → ℂ) (hw : Continuous w) (hws : HasCompactSupport w) :
    HasSum (fun n : Fin 4 → ℕ => ∫ t : ℝ,
      w t*(if P n then bblrAFESummand G α t n else 0))
      (∫ t : ℝ, w t*rectangularAFESelected G α P t) := by
  let B : ℝ → ℝ := fun t => ‖w t‖*(bblrGammaLineMajorant α t*rectangularAFEMellinMass G)
  have hBc : Continuous B :=
    hw.norm.mul ((rectangular_Gamma_line_majorant_continuous α hα).mul_const _)
  have hBs : HasCompactSupport B :=
    (hws.comp_left (show ‖(0:ℂ)‖ = (0:ℝ) by simp)).mul_right
  have hBi : Integrable B := hBc.integrable_of_hasCompactSupport hBs
  have hP := rectangular_AFE_index_majorant_summable α hα
  have hbound (n : Fin 4 → ℕ) (t : ℝ) :
      ‖w t*(if P n then bblrAFESummand G α t n else 0)‖ ≤
        B t*rectangularAFEIndexMajorant α n := by
    have hmaj := bblrAFESummand_norm_majorant G α t
      (bblrGammaLineMajorant α t*rectangularAFEMellinMass G)
      (fun x hx => rectangular_actual_V_height_majorant G α hG t x hx hα) n
    by_cases hn : P n
    · simp only [ite_eq_left hn, norm_mul]
      calc
        _ ≤ ‖w t‖*((bblrGammaLineMajorant α t*rectangularAFEMellinMass G)*
            rectangularAFEIndexMajorant α n) :=
          mul_le_mul_of_nonneg_left hmaj (norm_nonneg _)
        _ = _ := by dsimp [B]; ring
    · simp only [ite_eq_right hn, mul_zero, norm_zero]
      have hnon : 0 ≤ B t := by
        dsimp [B]
        exact mul_nonneg (norm_nonneg _) (mul_nonneg
          (bblrGammaLineMajorant_nonneg α t hα) (rectangular_AFE_Mellin_mass_nonneg G))
      exact mul_nonneg hnon (by dsimp [rectangularAFEIndexMajorant]; positivity)
  apply hasSum_integral_of_dominated_convergence
    (fun n t => B t*rectangularAFEIndexMajorant α n)
  · intro n
    by_cases hn : P n
    · simp only [ite_eq_left hn]
      exact (hw.stronglyMeasurable.mul
        (rectangular_actual_AFE_summand_stronglyMeasurable G
          (continuousOn_univ.mp hG.1.continuousOn) α hα n)).aestronglyMeasurable
    · simp only [ite_eq_right hn, mul_zero]
      exact aestronglyMeasurable_const
  · intro n
    exact Filter.Eventually.of_forall (hbound n)
  · exact Filter.Eventually.of_forall (fun t => hP.mul_left (B t))
  · simp_rw [tsum_mul_left]
    exact hBi.mul_const _
  · filter_upwards [] with t
    exact (filtered_summable _ (rectangular_actual_AFE_summable G α hG t hα) P).hasSum.mul_left (w t)

/-- The selected time integral is the sum of finite actual dyadic boxes. -/
theorem rectangular_actual_AFE_selected_dyadic_integral
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, -1/2 < (α j).re) (P : (Fin 4 → ℕ) → Prop)
    (w : ℝ → ℂ) (hw : Continuous w) (hws : HasCompactSupport w) :
    (∫ t : ℝ, w t*rectangularAFESelected G α P t) =
      ∑' k : Fin 4 → ℕ, ∑ n ∈ rectangularAFEDyadicBox k,
        ∫ t : ℝ, w t*(if P n then bblrAFESummand G α t n else 0) := by
  have hs := rectangular_actual_AFE_selected_weighted_hasSum G α hG hα P w hw hws
  rw [← hs.tsum_eq]
  exact rectangular_AFE_dyadic_grouping _ hs.summable

def rectangularAFESelectedBlocks (G : ℂ → ℂ) (α : MomentShifts)
    (w : ℝ → ℂ) (P : (Fin 4 → ℕ) → Prop) : ℂ :=
  ∑' k : Fin 4 → ℕ, ∑ n ∈ rectangularAFEDyadicBox k,
    if P n then ∫ t : ℝ, w t*bblrAFESummand G α t n else 0

/-- The selected block representation is tied to the actual AFE function. -/
theorem rectangular_actual_selected_integral_eq_blocks
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, -1/2 < (α j).re) (P : (Fin 4 → ℕ) → Prop)
    (w : ℝ → ℂ) (hw : Continuous w) (hws : HasCompactSupport w) :
    (∫ t : ℝ, w t*rectangularAFESelected G α P t) =
      rectangularAFESelectedBlocks G α w P := by
  rw [rectangular_actual_AFE_selected_dyadic_integral G α hG hα P w hw hws]
  apply tsum_congr
  intro k
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : P n <;> simp [hp]

/-- Actual diagonal and both signed errors, after the actual time integral,
exhaust the fourfold AFE series. -/
theorem rectangular_actual_AFE_integrated_diagonal_offDiagonal
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, -1/2 < (α j).re) (a b : ℕ)
    (w : ℝ → ℂ) (hw : Continuous w) (hws : HasCompactSupport w) :
    (∫ t : ℝ, w t*bblrAFESum G α t) =
      rectangularAFESelectedBlocks G α w (diagonalQuadRelation a b)+
      rectangularAFESelectedBlocks G α w (rectangularPositiveQuadGap a b)+
      rectangularAFESelectedBlocks G α w (rectangularNegativeQuadGap a b) := by
  let F : (Fin 4 → ℕ) → ℂ := fun n => ∫ t : ℝ, w t*bblrAFESummand G α t n
  have hs : Summable F := (rectangular_actual_AFE_weighted_hasSum G α hG hα w hw hws).summable
  have hd := filtered_summable F hs (diagonalQuadRelation a b)
  have hp := filtered_summable F hs (rectangularPositiveQuadGap a b)
  have hn := filtered_summable F hs (rectangularNegativeQuadGap a b)
  rw [rectangular_actual_AFE_weighted_integral G α hG hα w hw hws]
  change (∑' n, F n) = rectangularAFESelectedBlocks G α w (diagonalQuadRelation a b)+
    rectangularAFESelectedBlocks G α w (rectangularPositiveQuadGap a b)+
    rectangularAFESelectedBlocks G α w (rectangularNegativeQuadGap a b)
  unfold rectangularAFESelectedBlocks
  rw [← rectangular_AFE_dyadic_grouping _ hd, ← rectangular_AFE_dyadic_grouping _ hp,
    ← rectangular_AFE_dyadic_grouping _ hn, ← hd.tsum_add hp, ← (hd.add hp).tsum_add hn]
  apply tsum_congr
  intro n
  rcases lt_trichotomy (a*(n 0+1)*(n 1+1)) (b*(n 2+1)*(n 3+1)) with h | h | h
  · simp [diagonalQuadRelation, rectangularPositiveQuadGap, rectangularNegativeQuadGap,
      h, h.ne, not_lt_of_gt h]
  · simp [diagonalQuadRelation, rectangularPositiveQuadGap, rectangularNegativeQuadGap, h]
  · simp [diagonalQuadRelation, rectangularPositiveQuadGap, rectangularNegativeQuadGap,
      h, h.ne', not_lt_of_gt h]

/-- The actual original AFE block integral splits according to the exact
amplifier-dependent diagonal relation. -/
theorem rectangular_original_AFE_blocks_signed {T : ℝ} (hT : 1 < T)
    (f g Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (u v : ℕ)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, -1/2 < (α j).re) :
    rectangularOriginalAFEBlocks T α G f g Φ u v =
      rectangularAFESelectedBlocks G α (rectangularMomentPairWeight T f g Φ u v)
        (diagonalQuadRelation (u+1) (v+1))+
      rectangularAFESelectedBlocks G α (rectangularMomentPairWeight T f g Φ u v)
        (rectangularPositiveQuadGap (u+1) (v+1))+
      rectangularAFESelectedBlocks G α (rectangularMomentPairWeight T f g Φ u v)
        (rectangularNegativeQuadGap (u+1) (v+1)) := by
  have hw := rectangular_moment_pair_weight_continuous T f g Φ hΦ u v
  have hs := rectangular_moment_pair_weight_compact
    (ne_of_gt (lt_trans zero_lt_one hT)) f g Φ hΦ u v
  change (∑' k : Fin 4 → ℕ, ∑ n ∈ rectangularAFEDyadicBox k,
      ∫ t : ℝ, rectangularMomentPairWeight T f g Φ u v t*bblrAFESummand G α t n) = _
  rw [← rectangular_actual_AFE_dyadic_integral G α hG hα _ hw hs]
  exact rectangular_actual_AFE_integrated_diagonal_offDiagonal G α hG hα (u+1) (v+1) _ hw hs

/-- The literal dual multiplier remains inside each of the three dual
integrals; no Gamma or large-height phase approximation is assumed. -/
theorem rectangular_dual_AFE_blocks_signed {T : ℝ} (hT : 1 < T)
    (f g Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (u v : ℕ)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, |(α j).re| < 1/2) :
    rectangularDualAFEBlocks T α G f g Φ u v =
      rectangularAFESelectedBlocks G (bblrSixShifts α 1)
        (fun t => rectangularMomentPairWeight T f g Φ u v t*bblrDualMultiplier t α)
        (diagonalQuadRelation (u+1) (v+1))+
      rectangularAFESelectedBlocks G (bblrSixShifts α 1)
        (fun t => rectangularMomentPairWeight T f g Φ u v t*bblrDualMultiplier t α)
        (rectangularPositiveQuadGap (u+1) (v+1))+
      rectangularAFESelectedBlocks G (bblrSixShifts α 1)
        (fun t => rectangularMomentPairWeight T f g Φ u v t*bblrDualMultiplier t α)
        (rectangularNegativeQuadGap (u+1) (v+1)) := by
  have hw : Continuous (fun t : ℝ =>
      rectangularMomentPairWeight T f g Φ u v t*bblrDualMultiplier t α) :=
    (rectangular_moment_pair_weight_continuous T f g Φ hΦ u v).mul
      (rectangular_dual_multiplier_continuous α hα)
  have hs : HasCompactSupport (fun t : ℝ =>
      rectangularMomentPairWeight T f g Φ u v t*bblrDualMultiplier t α) :=
    (rectangular_moment_pair_weight_compact
      (ne_of_gt (lt_trans zero_lt_one hT)) f g Φ hΦ u v).mul_right
  have hd := rectangular_dual_shifts_strip α hα
  change (∑' k : Fin 4 → ℕ, ∑ n ∈ rectangularAFEDyadicBox k,
      ∫ t : ℝ, (rectangularMomentPairWeight T f g Φ u v t*bblrDualMultiplier t α)*
        bblrAFESummand G (bblrSixShifts α 1) t n) = _
  rw [← rectangular_actual_AFE_dyadic_integral G (bblrSixShifts α 1) hG hd _ hw hs]
  exact rectangular_actual_AFE_integrated_diagonal_offDiagonal G (bblrSixShifts α 1)
    hG hd (u+1) (v+1) _ hw hs

def rectangularActualSignedAFEBlocks (T a b : ℝ) (α : MomentShifts) (G : ℂ → ℂ)
    (f g Φ : ℝ → ℝ) : ℂ :=
  ∑ u ∈ Finset.range ⌊T^a⌋₊, ∑ v ∈ Finset.range ⌊T^b⌋₊,
    ((rectangularAFESelectedBlocks G α (rectangularMomentPairWeight T f g Φ u v)
        (diagonalQuadRelation (u+1) (v+1))+
      rectangularAFESelectedBlocks G α (rectangularMomentPairWeight T f g Φ u v)
        (rectangularPositiveQuadGap (u+1) (v+1))+
      rectangularAFESelectedBlocks G α (rectangularMomentPairWeight T f g Φ u v)
        (rectangularNegativeQuadGap (u+1) (v+1)))+
    (rectangularAFESelectedBlocks G (bblrSixShifts α 1)
        (fun t => rectangularMomentPairWeight T f g Φ u v t*bblrDualMultiplier t α)
        (diagonalQuadRelation (u+1) (v+1))+
      rectangularAFESelectedBlocks G (bblrSixShifts α 1)
        (fun t => rectangularMomentPairWeight T f g Φ u v t*bblrDualMultiplier t α)
        (rectangularPositiveQuadGap (u+1) (v+1))+
      rectangularAFESelectedBlocks G (bblrSixShifts α 1)
        (fun t => rectangularMomentPairWeight T f g Φ u v t*bblrDualMultiplier t α)
        (rectangularNegativeQuadGap (u+1) (v+1))))

/-- Both finite amplifiers are retained in the literal six-piece block sum. -/
theorem rectangular_actual_AFE_blocks_signed {T : ℝ} (hT : 1 < T) (a b : ℝ)
    (f g Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (hα : ∀ j, |(α j).re| < 1/2) :
    rectangularActualAFEBlocks T a b α G f g Φ =
      rectangularActualSignedAFEBlocks T a b α G f g Φ := by
  have ha : ∀ j, -1/2 < (α j).re := by
    intro j
    have := (abs_lt.mp (hα j)).1
    linarith
  unfold rectangularActualAFEBlocks rectangularActualSignedAFEBlocks
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  rw [rectangular_original_AFE_blocks_signed hT f g Φ hΦ u v G α hG ha,
    rectangular_dual_AFE_blocks_signed hT f g Φ hΦ u v G α hG hα]

/-- The actual moment discrepancy now contains six literal integrated
diagonal/signed AFE pieces and the actual primitive AFE remainder. -/
theorem rectangular_actual_moment_discrepancy_signed_AFE {T : ℝ} (hT : 1 < T)
    (a b : ℝ) (f g Φ : ℝ → ℝ) (hf : ∀ x, a < x → f x = 0)
    (hg : ∀ x, b < x → g x = 0) (hΦ : SmoothDyadicWeight Φ)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, ‖α j‖ < 1/4) :
    bblrMomentDiscrepancy T a b α G f g Φ =
      (rectangularActualSignedAFEBlocks T a b α G f g Φ-bblrSixMainTerms T a b α G f g Φ)+
        rectangularAFEIntegratedError T α G f g Φ := by
  have ha : ∀ j, |(α j).re| < 1/2 := fun j =>
    lt_trans ((Complex.abs_re_le_norm _).trans_lt (hα j)) (by norm_num)
  rw [rectangular_actual_moment_discrepancy_AFE hT a b f g Φ hf hg hΦ α G hG hα,
    rectangular_actual_AFE_blocks_signed hT a b f g Φ hΦ G α hG ha]

end
end Sechstmoment
