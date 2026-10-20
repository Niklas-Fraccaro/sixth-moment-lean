import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Sechstmoment.Numerator.U.Diagonal.ActualDiagonalGrouping
import Sechstmoment.Numerator.U.Reconstruction.RectangularAFEError


namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 0

def actualDiagonalQuadLineSeries (α : MomentShifts) (a b : ℕ) (v : ℝ) : ℂ :=
  ∑' n : Fin 4 → ℕ, if diagonalQuadRelation a b n then
    actualDiagonalQuadDirichletTerm α n (1+(v:ℂ)*I) else 0

private theorem actualDiagonalQuadLineTerm_continuous (α : MomentShifts) (n : Fin 4 → ℕ) :
    Continuous (fun v : ℝ => actualDiagonalQuadDirichletTerm α n (1+(v:ℂ)*I)) := by
  unfold actualDiagonalQuadDirichletTerm
  apply Continuous.div continuous_const
  · apply continuous_finsetProd
    intro j _
    apply Continuous.const_cpow (by fun_prop)
    exact Or.inl (by exact_mod_cast Nat.succ_ne_zero (n j))
  · intro v
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact Complex.natCast_add_one_cpow_ne_zero (n j) _

private theorem actualDiagonalQuadLineTerm_norm_le (α : MomentShifts) (a b : ℕ)
    (n : Fin 4 → ℕ) (v : ℝ) :
    ‖if diagonalQuadRelation a b n then actualDiagonalQuadDirichletTerm α n (1+(v:ℂ)*I)
      else 0‖ ≤ rectangularAFEIndexMajorant α n := by
  by_cases hn : diagonalQuadRelation a b n
  · simp only [hn,ite_true]
    exact (actualDiagonalQuadDirichletTerm_line_norm α n v).le
  · simp only [hn,ite_false,norm_zero]
    exact Finset.prod_nonneg (fun _ _ => by positivity)

theorem actualDiagonalQuadLineSeries_continuous (α : MomentShifts)
    (hα : ∀ j, -1/2 < (α j).re) (a b : ℕ) :
    Continuous (actualDiagonalQuadLineSeries α a b) := by
  apply continuous_tsum (u := rectangularAFEIndexMajorant α)
  · intro n
    by_cases hn : diagonalQuadRelation a b n
    · simpa only [hn,ite_true] using actualDiagonalQuadLineTerm_continuous α n
    · simp only [hn,ite_false]
      exact continuous_const
  · exact rectangular_AFE_index_majorant_summable α hα
  · exact actualDiagonalQuadLineTerm_norm_le α a b

theorem actualDiagonalQuadLineSeries_norm_le (α : MomentShifts)
    (hα : ∀ j, -1/2 < (α j).re) (a b : ℕ) (v : ℝ) :
    ‖actualDiagonalQuadLineSeries α a b v‖ ≤ ∑' n : Fin 4 → ℕ, rectangularAFEIndexMajorant α n := by
  have hm := rectangular_AFE_index_majorant_summable α hα
  have hn : Summable (fun n : Fin 4 → ℕ =>
      ‖if diagonalQuadRelation a b n then actualDiagonalQuadDirichletTerm α n (1+(v:ℂ)*I)
        else 0‖) := hm.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n =>
          actualDiagonalQuadLineTerm_norm_le α a b n v)
  exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum
    (fun n => actualDiagonalQuadLineTerm_norm_le α a b n v) hm)

theorem actualDiagonalMellinFactor_time_continuous (G : ℂ → ℂ) (a b : ℕ) (v : ℝ) :
    Continuous (fun t : ℝ => actualDiagonalMellinFactor G a b t (1+(v:ℂ)*I)) := by
  unfold actualDiagonalMellinFactor
  apply Continuous.div_const
  apply Continuous.const_mul
  exact (Complex.continuous_ofReal_cpow_const (by simp : 0 < (1+(v:ℂ)*I).re)).comp
    (by fun_prop : Continuous (fun t : ℝ => t^2))

theorem bblrDiagonalTerm_continuousAt_pos {t : ℝ} (ht : 0 < t)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, -1/2 < (α j).re) (a b : ℕ) :
    ContinuousAt (fun s : ℝ => bblrDiagonalTerm G α a b s) t := by
  let K : ℝ → ℝ → ℂ := fun s v => actualDiagonalMellinFactor G a b s (1+(v:ℂ)*I)*
    actualDiagonalQuadLineSeries α a b v
  let M : ℝ := actualDiagonalMellinMajorant a b (t+1)*
    (∑' n : Fin 4 → ℕ, rectangularAFEIndexMajorant α n)
  have hm : 0 ≤ ∑' n : Fin 4 → ℕ, rectangularAFEIndexMajorant α n :=
    tsum_nonneg (fun _ => Finset.prod_nonneg (fun _ _ => by positivity))
  have hnear : ∀ᶠ s in 𝓝 t, 0 < s ∧ s < t+1 :=
    IsOpen.mem_nhds isOpen_Ioo (show t ∈ Ioo 0 (t+1) by constructor <;> linarith)
  have hkernel : ContinuousAt (fun s : ℝ => ∫ v : ℝ, K s v) t := by
    apply continuousAt_of_dominated
      (bound := fun v : ℝ => M*‖G (1+(v:ℂ)*I)‖)
    · filter_upwards [hnear] with s hs
      have hc : Continuous (fun v : ℝ => K s v) := by
        apply Continuous.mul
        · have h0 := actualDiagonalMellinKernel_line_continuous hs.1.ne' G
            (continuousOn_univ.mp hG.1.continuousOn) α a b (fun _ => 0)
          simpa [actualDiagonalMellinKernel,actualDiagonalQuadDirichletTerm] using h0
        · exact actualDiagonalQuadLineSeries_continuous α hα a b
      exact hc.aestronglyMeasurable
    · filter_upwards [hnear] with s hs
      filter_upwards [] with v
      have hmaj : actualDiagonalMellinMajorant a b s ≤ actualDiagonalMellinMajorant a b (t+1) := by
        unfold actualDiagonalMellinMajorant
        gcongr <;> linarith [hs.1,hs.2]
      calc
        ‖K s v‖ = ‖actualDiagonalMellinFactor G a b s (1+(v:ℂ)*I)‖*
            ‖actualDiagonalQuadLineSeries α a b v‖ := norm_mul _ _
        _ ≤ (actualDiagonalMellinMajorant a b s*‖G (1+(v:ℂ)*I)‖)*
            (∑' n : Fin 4 → ℕ, rectangularAFEIndexMajorant α n) :=
          mul_le_mul (actualDiagonalMellinFactor_norm_le hs.1.ne' G a b v)
            (actualDiagonalQuadLineSeries_norm_le α hα a b v) (norm_nonneg _)
            (mul_nonneg (actualDiagonalMellinMajorant_nonneg a b s) (norm_nonneg _))
        _ ≤ M*‖G (1+(v:ℂ)*I)‖ := by
          have h := mul_le_mul_of_nonneg_right hmaj
            (mul_nonneg (norm_nonneg (G (1+(v:ℂ)*I))) hm)
          simpa only [M,mul_assoc,mul_comm,mul_left_comm] using h
    · exact (rectangular_BBLR_weight_vertical_integrable G α hG).const_mul M
    · exact Eventually.of_forall (fun v =>
        (actualDiagonalMellinFactor_time_continuous G a b v).continuousAt.mul_const _)
  have hident : (fun s : ℝ => bblrDiagonalTerm G α a b s) =ᶠ[𝓝 t]
      (fun s : ℝ => (1/(2*π):ℂ)*∫ v : ℝ, K s v) := by
    filter_upwards [hnear] with s hs
    simpa [verticalIntegral,actualDiagonalQuadLineSeries,K] using
      bblrDiagonalTerm_eq_actualMellin hs.1.ne' G α hG hα a b
  exact (hkernel.const_mul _).congr hident.symm


theorem actualDyadicDiagonal_integrable {T : ℝ} (hT : 0 < T)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, -1/2 < (α j).re) (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ)
    (ρ : ℂ) (a b : ℕ) : Integrable (fun t : ℝ =>
      (Φ (t/T):ℂ)*(t/(2*π):ℂ)^ρ*bblrDiagonalTerm G α a b t) := by
  have hzero (s : ℝ) (hs : s < T) : Φ (s/T)=0 := by
    by_contra hn
    have hsupp : s/T ∈ tsupport Φ := subset_tsupport Φ hn
    have hlow := (hΦ.2 hsupp).1
    have hbound : T ≤ s := by simpa only [one_mul] using (le_div_iff₀ hT).mp hlow
    linarith
  have hc : Continuous (fun t : ℝ =>
      (Φ (t/T):ℂ)*(t/(2*π):ℂ)^ρ*bblrDiagonalTerm G α a b t) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    by_cases ht : 0 < t
    · apply ContinuousAt.mul
      · apply ContinuousAt.mul
        · exact Complex.continuous_ofReal.continuousAt.comp
            (hΦ.1.continuous.continuousAt.comp (by fun_prop))
        · have hp : ContinuousAt (fun s : ℝ => ((s/(2*π):ℝ):ℂ)^ρ) t :=
            (Complex.continuousAt_ofReal_cpow_const (t/(2*π)) ρ
              (Or.inr (div_pos ht (by positivity)).ne')).comp_of_eq
                (by fun_prop : ContinuousAt (fun s : ℝ => s/(2*π)) t) rfl
          simpa only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat] using hp
      · exact bblrDiagonalTerm_continuousAt_pos ht G α hG hα a b
    · have hlt : t < T := lt_of_le_of_lt (le_of_not_gt ht) hT
      have heq : (fun _ : ℝ => (0:ℂ)) =ᶠ[𝓝 t] (fun s : ℝ =>
          (Φ (s/T):ℂ)*(s/(2*π):ℂ)^ρ*bblrDiagonalTerm G α a b s) := by
        filter_upwards [Iio_mem_nhds hlt] with s hs
        rw [hzero s hs]
        simp
      exact continuousAt_const.congr heq
  have hcompact : HasCompactSupport Φ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hΦ.2
  have hscaled : HasCompactSupport (fun t : ℝ => (Φ (t/T):ℂ)) := by
    have h := hcompact.comp_smul (inv_ne_zero hT.ne')
    have hs : HasCompactSupport (fun t : ℝ => Φ (t/T)) := by
      convert h using 1
      funext t
      simp only [smul_eq_mul,div_eq_mul_inv]
      congr 1
      ring
    exact hs.comp_left (show Complex.ofReal 0=0 from rfl)
  exact hc.integrable_of_hasCompactSupport
    ((hscaled.mul_right (f' := fun t : ℝ => (t/(2*π):ℂ)^ρ)).mul_right
      (f' := fun t : ℝ => bblrDiagonalTerm G α a b t))

end
end Sechstmoment
