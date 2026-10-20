import Sechstmoment.Analysis.Mellin.ProfileInversion
import Sechstmoment.Numerator.U.Diagonal.DiagonalEulerSixIndices
import Sechstmoment.Numerator.U.Reconstruction.RectangularAFEInterchange


namespace Sechstmoment
open Complex Source MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 0

def actualDiagonalQuadDirichletTerm (α : MomentShifts) (n : Fin 4 → ℕ) (z : ℂ) : ℂ :=
  1/(∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j+z))

def actualDiagonalMellinFactor (G : ℂ → ℂ) (a b : ℕ) (t : ℝ) (z : ℂ) : ℂ :=
  G z/z*(2*Real.pi:ℂ)^(-2*z)*((t^2:ℝ):ℂ)^z/((a*b:ℕ):ℂ)^(1/2:ℂ)

def actualDiagonalMellinKernel (G : ℂ → ℂ) (α : MomentShifts)
    (a b : ℕ) (t : ℝ) (n : Fin 4 → ℕ) (z : ℂ) : ℂ :=
  actualDiagonalMellinFactor G a b t z*actualDiagonalQuadDirichletTerm α n z

theorem actualDiagonal_quad_power_factorization (t : ℝ)
    (n : Fin 4 → ℕ) (z : ℂ) :
    ((positiveQuadProduct n/t^2:ℝ):ℂ)^(-z) =
      ((t^2:ℝ):ℂ)^z*(positiveQuadProduct n:ℂ)^(-z) := by
  have hq : (0:ℝ) ≤ positiveQuadProduct n := by positivity
  have ht2 : (0:ℝ) ≤ t^2 := sq_nonneg t
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hq ht2]
  simp only [Complex.cpow_neg, div_eq_mul_inv, inv_inv]
  simpa only [Complex.ofReal_natCast] using
    mul_comm ((positiveQuadProduct n:ℂ)^z)⁻¹ (((t^2:ℝ):ℂ)^z)

theorem actualDiagonalMellinKernel_eq_source_line (t : ℝ)
    (G : ℂ → ℂ) (α : MomentShifts) (a b : ℕ) (n : Fin 4 → ℕ) (v : ℝ) :
    actualDiagonalMellinKernel G α a b t n (1+(v:ℂ)*I) =
      G (1+(v:ℂ)*I)/(1+(v:ℂ)*I)*(2*Real.pi:ℂ)^(-2*(1+(v:ℂ)*I))*
        (((positiveQuadProduct n/t^2:ℝ):ℂ)^(-(1+(v:ℂ)*I)))/
          ((a*b:ℕ):ℂ)^(1/2:ℂ)/(∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j)) := by
  rw [actualDiagonal_quad_power_factorization t,
    actualDiagonalMellinKernel, actualDiagonalMellinFactor, actualDiagonalQuadDirichletTerm]
  have h := rectangular_AFE_Mellin_powers α n (1+(v:ℂ)*I)
  rw [div_eq_mul_inv] at h
  simp only [one_div] at h
  simp only [div_eq_mul_inv, one_mul]
  rw [← h]
  ring

theorem bblrDiagonalSummand_eq_actualMellin (t : ℝ)
    (G : ℂ → ℂ) (α : MomentShifts) (a b : ℕ) (n : Fin 4 → ℕ) :
    bblrDiagonalSummand G α a b t n =
      verticalIntegral 1 (actualDiagonalMellinKernel G α a b t n) := by
  unfold bblrDiagonalSummand bblrVStar verticalIntegral
  dsimp only
  simp only [Complex.ofReal_one]
  simp_rw [actualDiagonalMellinKernel_eq_source_line t]
  simp_rw [integral_div]
  ring

theorem actualDiagonalQuadDirichletTerm_line_norm (α : MomentShifts)
    (n : Fin 4 → ℕ) (v : ℝ) :
    ‖actualDiagonalQuadDirichletTerm α n (1+(v:ℂ)*I)‖ =
      ∏ j : Fin 4, 1/(n j+1:ℝ)^(3/2+(α j).re) := by
  unfold actualDiagonalQuadDirichletTerm
  rw [norm_div, norm_one, norm_prod]
  have hn (j : Fin 4) : 0 < (n j+1:ℝ) := by positivity
  have hp (j : Fin 4) : ‖(n j+1:ℂ)^(1/2+α j+(1+(v:ℂ)*I))‖ =
      (n j+1:ℝ)^(3/2+(α j).re) := by
    rw [show (n j+1:ℂ) = ((n j+1:ℝ):ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (hn j)]
    congr 1
    simp
    ring
  simp_rw [hp]
  rw [Finset.prod_div_distrib, Finset.prod_const_one]

def actualDiagonalMellinMajorant (a b : ℕ) (t : ℝ) : ℝ :=
  (2*Real.pi)^(-2:ℝ)*t^2/‖((a*b:ℕ):ℂ)^(1/2:ℂ)‖

theorem actualDiagonalMellinFactor_norm_le {t : ℝ} (ht : t ≠ 0)
    (G : ℂ → ℂ) (a b : ℕ) (v : ℝ) :
    ‖actualDiagonalMellinFactor G a b t (1+(v:ℂ)*I)‖ ≤
      actualDiagonalMellinMajorant a b t*‖G (1+(v:ℂ)*I)‖ := by
  have hz : 1 ≤ ‖(1:ℂ)+(v:ℂ)*I‖ := by
    simpa using Complex.abs_re_le_norm ((1:ℂ)+(v:ℂ)*I)
  have hg : ‖G (1+(v:ℂ)*I)/(1+(v:ℂ)*I)‖ ≤ ‖G (1+(v:ℂ)*I)‖ := by
    rw [norm_div]
    exact div_le_self (norm_nonneg _) hz
  have hp : ‖(2*Real.pi:ℂ)^(-2*(1+(v:ℂ)*I))‖ = (2*Real.pi)^(-2:ℝ) := by
    rw [show (2*Real.pi:ℂ) = ((2*Real.pi:ℝ):ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < 2*Real.pi)]
    congr 1
    simp
  have ht2 : ‖((t^2:ℝ):ℂ)^((1:ℂ)+(v:ℂ)*I)‖ = t^2 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (sq_pos_of_ne_zero ht)]
    simp
  unfold actualDiagonalMellinFactor actualDiagonalMellinMajorant
  rw [norm_div, norm_mul, norm_mul, hp, ht2]
  calc
    _ ≤ ‖G (1+(v:ℂ)*I)‖*(2*Real.pi)^(-2:ℝ)*t^2/
        ‖((a*b:ℕ):ℂ)^(1/2:ℂ)‖ := by
      gcongr
    _ = _ := by ring

theorem actualDiagonalMellinMajorant_nonneg (a b : ℕ) (t : ℝ) :
    0 ≤ actualDiagonalMellinMajorant a b t := by
  unfold actualDiagonalMellinMajorant
  exact div_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg t))
    (norm_nonneg _)

theorem actualDiagonalMellinKernel_line_norm_le {t : ℝ} (ht : t ≠ 0)
    (G : ℂ → ℂ) (α : MomentShifts) (a b : ℕ) (n : Fin 4 → ℕ) (v : ℝ) :
    ‖actualDiagonalMellinKernel G α a b t n (1+(v:ℂ)*I)‖ ≤
      actualDiagonalMellinMajorant a b t*‖G (1+(v:ℂ)*I)‖*rectangularAFEIndexMajorant α n := by
  rw [actualDiagonalMellinKernel, norm_mul, actualDiagonalQuadDirichletTerm_line_norm]
  exact mul_le_mul_of_nonneg_right (actualDiagonalMellinFactor_norm_le ht G a b v)
    (Finset.prod_nonneg (fun _ _ => by positivity))

theorem actualDiagonalMellinKernel_line_continuous {t : ℝ} (ht : t ≠ 0)
    (G : ℂ → ℂ) (hG : Continuous G) (α : MomentShifts) (a b : ℕ) (n : Fin 4 → ℕ) :
    Continuous (fun v : ℝ => actualDiagonalMellinKernel G α a b t n (1+(v:ℂ)*I)) := by
  unfold actualDiagonalMellinKernel actualDiagonalMellinFactor actualDiagonalQuadDirichletTerm
  apply Continuous.mul
  · apply Continuous.div_const
    apply Continuous.mul
    · apply Continuous.mul
      · apply Continuous.div
        · exact hG.comp (by fun_prop)
        · fun_prop
        · intro v hv
          have he := congrArg Complex.re hv
          simp at he
      · apply Continuous.const_cpow (by fun_prop)
        exact Or.inl (mul_ne_zero (by norm_num)
          (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    · apply Continuous.const_cpow (by fun_prop)
      exact Or.inl (Complex.ofReal_ne_zero.mpr (sq_pos_of_ne_zero ht).ne')
  · apply Continuous.div continuous_const
    · apply continuous_finsetProd
      intro j _
      apply Continuous.const_cpow (by fun_prop)
      exact Or.inl (by exact_mod_cast Nat.succ_ne_zero (n j))
    · intro v
      apply Finset.prod_ne_zero_iff.mpr
      intro j _
      exact Complex.natCast_add_one_cpow_ne_zero (n j) _

theorem actualDiagonalMellinKernel_selected_norm_summable {t : ℝ} (ht : t ≠ 0)
    (G : ℂ → ℂ) (α : MomentShifts) (hα : ∀ j, -1/2 < (α j).re)
    (a b : ℕ) (v : ℝ) :
    Summable (fun n : Fin 4 → ℕ =>
      ‖if diagonalQuadRelation a b n then actualDiagonalMellinKernel G α a b t n (1+(v:ℂ)*I)
        else 0‖) := by
  apply ((rectangular_AFE_index_majorant_summable α hα).mul_left
    (actualDiagonalMellinMajorant a b t*‖G (1+(v:ℂ)*I)‖)).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro n
  by_cases hn : diagonalQuadRelation a b n
  · simpa only [hn, ite_true] using actualDiagonalMellinKernel_line_norm_le ht G α a b n v
  · simp only [hn, ite_false, norm_zero]
    exact mul_nonneg (mul_nonneg (actualDiagonalMellinMajorant_nonneg a b t) (norm_nonneg _))
      (Finset.prod_nonneg (fun _ _ => by positivity))

theorem bblrDiagonalTerm_eq_actualMellin {t : ℝ} (ht : t ≠ 0)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, -1/2 < (α j).re) (a b : ℕ) :
    bblrDiagonalTerm G α a b t = verticalIntegral 1 (fun z =>
      actualDiagonalMellinFactor G a b t z*
        ∑' n : Fin 4 → ℕ, if diagonalQuadRelation a b n then actualDiagonalQuadDirichletTerm α n z
          else 0) := by
  let F : (Fin 4 → ℕ) → ℝ → ℂ := fun n v =>
    if diagonalQuadRelation a b n then actualDiagonalMellinKernel G α a b t n (1+(v:ℂ)*I) else 0
  have hg : Integrable (fun v : ℝ => ‖G (1+(v:ℂ)*I)‖) :=
    rectangular_BBLR_weight_vertical_integrable G α hG
  have hmaj := rectangular_AFE_index_majorant_summable α hα
  have hs : HasSum (fun n : Fin 4 → ℕ => ∫ v : ℝ, F n v)
      (∫ v : ℝ, ∑' n : Fin 4 → ℕ, F n v) := by
    apply hasSum_integral_of_dominated_convergence (fun n (v : ℝ) =>
      actualDiagonalMellinMajorant a b t*‖G (1+(v:ℂ)*I)‖*rectangularAFEIndexMajorant α n)
    · intro n
      by_cases hn : diagonalQuadRelation a b n
      · simpa only [F, hn, ite_true] using
          (actualDiagonalMellinKernel_line_continuous ht G
            (continuousOn_univ.mp hG.1.continuousOn) α a b n).aestronglyMeasurable
      · simp only [F, hn, ite_false]
        exact aestronglyMeasurable_const
    · intro n
      filter_upwards [] with v
      by_cases hn : diagonalQuadRelation a b n
      · simpa only [F, hn, ite_true] using actualDiagonalMellinKernel_line_norm_le ht G α a b n v
      · simp only [F, hn, ite_false, norm_zero]
        exact mul_nonneg (mul_nonneg (actualDiagonalMellinMajorant_nonneg a b t) (norm_nonneg _))
          (Finset.prod_nonneg (fun _ _ => by positivity))
    · exact Eventually.of_forall (fun v => hmaj.mul_left _)
    · simp_rw [tsum_mul_left]
      exact (hg.const_mul _).mul_const _
    · exact Eventually.of_forall (fun v =>
        (actualDiagonalMellinKernel_selected_norm_summable ht G α hα a b v).of_norm.hasSum)
  have hs' := hs.mul_left (1/(2*Real.pi):ℂ)
  calc
    bblrDiagonalTerm G α a b t =
        ∑' n : Fin 4 → ℕ, (1/(2*Real.pi):ℂ)*∫ v : ℝ, F n v := by
      unfold bblrDiagonalTerm
      apply tsum_congr
      intro n
      by_cases hn : diagonalQuadRelation a b n
      · simp only [F, hn, ite_true]
        exact bblrDiagonalSummand_eq_actualMellin t G α a b n
      · simp [F, hn]
    _ = (1/(2*Real.pi):ℂ)*∫ v : ℝ, ∑' n : Fin 4 → ℕ, F n v := hs'.tsum_eq
    _ = _ := by
      unfold verticalIntegral
      dsimp only
      simp only [Complex.ofReal_one]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with v
      dsimp [F]
      simp_rw [actualDiagonalMellinKernel]
      simp_rw [show ∀ n : Fin 4 → ℕ,
        (if diagonalQuadRelation a b n then
          actualDiagonalMellinFactor G a b t (1+(v:ℂ)*I)*
            actualDiagonalQuadDirichletTerm α n (1+(v:ℂ)*I) else 0) =
        actualDiagonalMellinFactor G a b t (1+(v:ℂ)*I)*
          (if diagonalQuadRelation a b n then actualDiagonalQuadDirichletTerm α n (1+(v:ℂ)*I)
            else 0) from fun n => by split_ifs <;> simp]
      rw [tsum_mul_left]

end
end Sechstmoment
