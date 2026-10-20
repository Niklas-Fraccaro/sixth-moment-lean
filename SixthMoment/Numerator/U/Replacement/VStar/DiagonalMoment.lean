import SixthMoment.Numerator.U.Replacement.VStar.DiagonalExtraction

namespace SixthMoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def bblrIndexedMainIntegrand (j : Fin 6) (T a b : ℝ) (α : MomentShifts) (G : ℂ→ℂ)
    (f g Φ : ℝ→ℝ) (t : ℝ) : ℂ :=
  ∑ m∈Finset.Icc 1 ⌊T^a⌋₊, ∑ n∈Finset.Icc 1 ⌊T^b⌋₊,
    (f (Real.log m/Real.log T):ℂ)*(g (Real.log n/Real.log T):ℂ)*
      ((Φ (t/T):ℂ)*(t/(2*Real.pi):ℂ)^(bblrSixPhaseExponents α j)*
        bblrDiagonalTerm G (bblrSixShifts α j) m n t)

private theorem shifts_re_lower (α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) :
    ∀ j, -1/2<(α j).re := by
  intro j
  have h := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hα j))).1
  linarith

theorem bblrIndexedMainIntegrand_integrable {T : ℝ} (hT : 0<T) (a b : ℝ)
    (α : MomentShifts) (G : ℂ→ℂ) (hG : BBLREntireWeight G α)
    (hα : ∀ j, ‖α j‖≤1/4) (j : Fin 6) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Integrable (bblrIndexedMainIntegrand j T a b α G f g Φ) := by
  unfold bblrIndexedMainIntegrand
  apply integrable_finsetSum
  intro m _
  apply integrable_finsetSum
  intro n _
  exact (actualDyadicDiagonal_integrable hT G (bblrSixShifts α j) hG
    (shifts_re_lower _ (bblrSixShifts_norm_le _ hα j)) Φ hΦ
      (bblrSixPhaseExponents α j) m n).const_mul _

theorem integral_bblrIndexedMainIntegrand {T : ℝ} (hT : 0<T) (a b : ℝ)
    (α : MomentShifts) (G : ℂ→ℂ) (hG : BBLREntireWeight G α)
    (hα : ∀ j, ‖α j‖≤1/4) (j : Fin 6) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    (∫ t : ℝ, bblrIndexedMainIntegrand j T a b α G f g Φ t)=
      bblrIndexedMainTerm j T a b α G f g Φ := by
  have hi (m n : ℕ) : Integrable (fun t : ℝ =>
      (f (Real.log m/Real.log T):ℂ)*(g (Real.log n/Real.log T):ℂ)*
        ((Φ (t/T):ℂ)*(t/(2*Real.pi):ℂ)^(bblrSixPhaseExponents α j)*
          bblrDiagonalTerm G (bblrSixShifts α j) m n t)) :=
    (actualDyadicDiagonal_integrable hT G (bblrSixShifts α j) hG
      (shifts_re_lower _ (bblrSixShifts_norm_le _ hα j)) Φ hΦ
        (bblrSixPhaseExponents α j) m n).const_mul _
  unfold bblrIndexedMainIntegrand bblrIndexedMainTerm
  rw [integral_finsetSum _ (fun m _ => integrable_finsetSum _ (fun n _ => hi m n))]
  apply Finset.sum_congr rfl
  intro m _
  rw [integral_finsetSum _ (fun n _ => hi m n)]
  apply Finset.sum_congr rfl
  intro n _
  rw [integral_const_mul]

theorem rectangularVStarSelectedCombined_diagonal_eq_main_integrands {T : ℝ}
    (hT : T≠0) (a b : ℝ) (σ : MomentShifts) (f g Φ : ℝ→ℝ) (t : ℝ) :
    rectangularVStarSelectedCombinedIntegrand true T a b σ f g Φ t=
      bblrIndexedMainIntegrand 0 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ t+
        bblrIndexedMainIntegrand 1 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ t := by
  unfold rectangularVStarSelectedCombinedIntegrand
  rw [rectangularVStarSelectedIntegrand_diagonal_eq_source,
    rectangularVStarSelectedIntegrand_diagonal_eq_source]
  unfold bblrIndexedMainIntegrand
  have hdual : bblrDualLeadingMultiplier T σ (t/T)=
      (t/(2*Real.pi):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) 1) := by
    unfold bblrDualLeadingMultiplier
    rw [Complex.ofReal_div,mul_div_cancel₀ (t:ℂ) (Complex.ofReal_ne_zero.mpr hT)]
    congr 1
    simp [bblrSixPhaseExponents,Fin.sum_univ_succ]
    ring
  rw [hdual]
  simp only [bblrSixPhaseExponents,bblrSixShifts,Matrix.cons_val_zero,Complex.cpow_zero,mul_one,
    Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro n _
    ring
  · apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro n _
    ring

theorem rectangularVStarSelectedCombined_diagonal_integrable {T : ℝ} (hT : 0<T)
    (a b : ℝ) (σ : MomentShifts) (hα : ∀ j, ‖rawMomentShifts T σ j‖≤1/4)
    (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Integrable (rectangularVStarSelectedCombinedIntegrand true T a b σ f g Φ) := by
  have he : rectangularVStarSelectedCombinedIntegrand true T a b σ f g Φ=
      (fun t : ℝ => bblrIndexedMainIntegrand 0 T a b (rawMomentShifts T σ)
        (polarPoleKiller T σ) f g Φ t)+
      (fun t : ℝ => bblrIndexedMainIntegrand 1 T a b (rawMomentShifts T σ)
        (polarPoleKiller T σ) f g Φ t) := by
    funext t
    exact rectangularVStarSelectedCombined_diagonal_eq_main_integrands hT.ne' a b σ f g Φ t
  rw [he]
  have hG := polarPoleKiller_BBLREntireWeight T σ (rawMomentShifts T σ)
  exact (bblrIndexedMainIntegrand_integrable hT a b _ _ hG hα 0 f g Φ hΦ).add
    (bblrIndexedMainIntegrand_integrable hT a b _ _ hG hα 1 f g Φ hΦ)

theorem rectangularVStarSelectedMoment_diagonal_eq_main_terms {T : ℝ} (hT : 0<T)
    (a b : ℝ) (σ : MomentShifts) (hα : ∀ j, ‖rawMomentShifts T σ j‖≤1/4)
    (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    rectangularVStarSelectedMoment true T a b σ f g Φ=
      bblrIndexedMainTerm 0 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ+
        bblrIndexedMainTerm 1 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ := by
  unfold rectangularVStarSelectedMoment
  simp only [rectangularVStarSelectedCombined_diagonal_eq_main_integrands hT.ne']
  have hG := polarPoleKiller_BBLREntireWeight T σ (rawMomentShifts T σ)
  rw [integral_add (bblrIndexedMainIntegrand_integrable hT a b _ _ hG hα 0 f g Φ hΦ)
      (bblrIndexedMainIntegrand_integrable hT a b _ _ hG hα 1 f g Φ hΦ),
    integral_bblrIndexedMainIntegrand hT a b _ _ hG hα 0 f g Φ hΦ,
    integral_bblrIndexedMainIntegrand hT a b _ _ hG hα 1 f g Φ hΦ]

theorem rectangularVStarAFEMoment_eventually_eq_diagonal_and_offdiagonal
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖)
    (a b : ℝ) (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) :
    ∀ᶠ T : ℝ in atTop, ∀ σ∈K,
      Integrable (rectangularVStarSelectedCombinedIntegrand true T a b σ f g Φ) ∧
      Integrable (rectangularVStarSelectedCombinedIntegrand false T a b σ f g Φ) ∧
      rectangularVStarAFEMoment T σ f g Φ=
        bblrIndexedMainTerm 0 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ+
          bblrIndexedMainTerm 1 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ+
            rectangularVStarSelectedMoment false T a b σ f g Φ := by
  have hfull := rectangularVStarAFEIntegrand_eventually_integrable K hK δ hδ hroot a b f g Φ hf hg hΦ
  filter_upwards [hfull,compactNormalizedShifts_eventually_norm_small K hK (1/4)
    (by norm_num),eventually_gt_atTop (1:ℝ)] with T hfull hsmall hT
  intro σ hσ
  have hα := hsmall σ hσ
  have hd := rectangularVStarSelectedCombined_diagonal_integrable
    (zero_lt_one.trans hT) a b σ hα f g Φ hΦ
  have he : rectangularVStarAFEIntegrand T σ f g Φ=
      (fun t : ℝ => rectangularVStarSelectedCombinedIntegrand true T a b σ f g Φ t)+
      (fun t : ℝ => rectangularVStarSelectedCombinedIntegrand false T a b σ f g Φ t) := by
    funext t
    exact rectangularVStarAFEIntegrand_eq_selected hT a b σ hα f g Φ hf hg t
  have ho : Integrable (rectangularVStarSelectedCombinedIntegrand false T a b σ f g Φ) := by
    have hsub := (hfull σ hσ).sub hd
    convert hsub using 1
    funext t
    have := congrFun he t
    simp only [Pi.add_apply,Pi.sub_apply] at this ⊢
    linear_combination -this
  refine ⟨hd,ho,?_⟩
  unfold rectangularVStarAFEMoment
  rw [he]
  simp only [Pi.add_apply]
  rw [integral_add hd ho]
  change rectangularVStarSelectedMoment true T a b σ f g Φ+
    rectangularVStarSelectedMoment false T a b σ f g Φ=_
  rw [rectangularVStarSelectedMoment_diagonal_eq_main_terms (zero_lt_one.trans hT) a b σ hα f g Φ hΦ]

end
end SixthMoment
