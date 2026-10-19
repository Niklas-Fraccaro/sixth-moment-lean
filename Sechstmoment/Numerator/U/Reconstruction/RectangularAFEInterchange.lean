import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
import Sechstmoment.Numerator.U.Reconstruction.RectangularAFEMellin

/-!
The fourfold actual AFE series is interchanged with a compactly supported
time integral. The dominating function retains the actual height-dependent
Gamma quotient; no large-height Gamma asymptotic is needed for this exact step.
-/

namespace Sechstmoment

set_option maxHeartbeats 2000000

open Complex Source MeasureTheory Set
open scoped BigOperators Topology
open Classical

noncomputable section

theorem rectangular_source_point_continuous (j : Fin 4) :
    Continuous (fun t : ℝ => sourceZetaPoints t j) := by
  fin_cases j <;> fun_prop [sourceZetaPoints, criticalLinePoint]

theorem rectangular_Gamma_line_majorant_continuous (α : MomentShifts)
    (hα : ∀ j, -1/2 < (α j).re) : Continuous (bblrGammaLineMajorant α) := by
  unfold bblrGammaLineMajorant
  apply continuous_finsetProd
  intro j hj
  apply Continuous.div continuous_const
  · apply Continuous.norm
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (Complex.continuousAt_Gamma _ ?_).comp
    · exact (((rectangular_source_point_continuous j).add continuous_const).div_const 2).continuousAt
    · intro n hn
      have hr := congrArg Complex.re hn
      have ha := hα j
      have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
      simp at hr
      linarith
  · intro t
    apply norm_ne_zero_iff.mpr
    apply Complex.Gamma_ne_zero
    intro n hn
    have hr := congrArg Complex.re hn
    have ha := hα j
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    simp at hr
    linarith

theorem rectangular_Gamma_quotient_joint_continuous (α : MomentShifts)
    (hα : ∀ j, -1/2 < (α j).re) :
    Continuous (fun p : ℝ×ℝ => bblrGammaQuotient p.1 α (1+(p.2 : ℂ)*I)) := by
  unfold bblrGammaQuotient
  apply continuous_finsetProd
  intro j hj
  apply Continuous.div
  · apply continuous_iff_continuousAt.mpr
    intro p
    apply (Complex.continuousAt_Gamma _ ?_).comp
    · apply Continuous.continuousAt
      exact ((((rectangular_source_point_continuous j).comp continuous_fst).add continuous_const).add
        (by fun_prop)).div_const 2
    · intro n hn
      have hr := congrArg Complex.re hn
      have ha := hα j
      have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
      simp at hr
      linarith
  · apply continuous_iff_continuousAt.mpr
    intro p
    apply (Complex.continuousAt_Gamma _ ?_).comp
    · exact ((((rectangular_source_point_continuous j).comp continuous_fst).add continuous_const).div_const 2).continuousAt
    · intro n hn
      have hr := congrArg Complex.re hn
      have ha := hα j
      have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
      simp at hr
      linarith
  · intro p
    apply Complex.Gamma_ne_zero
    intro n hn
    have hr := congrArg Complex.re hn
    have ha := hα j
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    simp at hr
    linarith

theorem rectangular_vertical_joint_continuous (G : ℂ → ℂ) (hG : Continuous G)
    (α : MomentShifts) (hα : ∀ j, -1/2 < (α j).re) (x : ℝ) (hx : 0 < x) :
    Continuous (fun p : ℝ×ℝ => bblrVerticalIntegrand G α x p.1 p.2) := by
  unfold bblrVerticalIntegrand
  dsimp only
  apply Continuous.mul
  · apply Continuous.mul
    · apply Continuous.mul
      · apply Continuous.div
        · exact hG.comp (by fun_prop)
        · fun_prop
        · intro p hp
          have hr := congrArg Complex.re hp
          simp at hr
      · exact rectangular_Gamma_quotient_joint_continuous α hα
    · apply Continuous.const_cpow
      · fun_prop
      · exact Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  · apply Continuous.const_cpow
    · fun_prop
    · exact Or.inl (Complex.ofReal_ne_zero.mpr hx.ne')

/-- Measurability of the actual parameter integral follows from its genuine
joint integrand, rather than from an assumed continuity of V. -/
theorem rectangular_actual_V_stronglyMeasurable (G : ℂ → ℂ) (hG : Continuous G)
    (α : MomentShifts) (hα : ∀ j, -1/2 < (α j).re) (x : ℝ) (hx : 0 < x) :
    StronglyMeasurable (fun t : ℝ => bblrV G α x t) := by
  have hm := (rectangular_vertical_joint_continuous G hG α hα x hx).stronglyMeasurable
  have hi := hm.integral_prod_right' (ν := volume)
  exact hi.const_mul (1/(2*Real.pi) : ℂ)

theorem rectangular_actual_AFE_summand_stronglyMeasurable (G : ℂ → ℂ) (hG : Continuous G)
    (α : MomentShifts) (hα : ∀ j, -1/2 < (α j).re) (n : Fin 4 → ℕ) :
    StronglyMeasurable (fun t : ℝ => bblrAFESummand G α t n) := by
  have hc : Continuous (fun t : ℝ => rectangularAFEOscillation t n) := by
    unfold rectangularAFEOscillation
    apply Continuous.const_cpow
    · fun_prop
    · apply Or.inl
      have h₁ : (((n 0+1)*(n 1+1) : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.mul_ne_zero (Nat.succ_ne_zero (n 0)) (Nat.succ_ne_zero (n 1))
      have h₂ : (((n 2+1)*(n 3+1) : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.mul_ne_zero (Nat.succ_ne_zero (n 2)) (Nat.succ_ne_zero (n 3))
      exact div_ne_zero h₁ h₂
  have hm := rectangular_actual_V_stronglyMeasurable G hG α hα (positiveQuadProduct n)
    (by simp [positiveQuadProduct]; positivity)
  simpa only [bblrAFESummand, rectangularAFEOscillation, div_eq_mul_inv, Pi.mul_apply] using
    (hc.stronglyMeasurable.mul hm).mul_const (∏ j : Fin 4, (n j+1 : ℂ)^(1/2+α j))⁻¹

def rectangularAFEMellinMass (G : ℂ → ℂ) : ℝ :=
  Real.pi^(-2:ℝ)*(∫ v : ℝ, ‖G (1+(v : ℂ)*I)‖)/(2*Real.pi)

theorem rectangular_AFE_Mellin_mass_nonneg (G : ℂ → ℂ) :
    0 ≤ rectangularAFEMellinMass G := by
  unfold rectangularAFEMellinMass
  have hi : (0:ℝ) ≤ ∫ v : ℝ, ‖G (1+(v : ℂ)*I)‖ :=
    integral_nonneg (fun v : ℝ => norm_nonneg (G (1+(v : ℂ)*I)))
  positivity

/-- This retains the explicit genuine Gamma majorant at the actual height. -/
theorem rectangular_actual_V_height_majorant (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (t x : ℝ) (hx : 0 < x)
    (hα : ∀ j, -1/2 < (α j).re) :
    ‖bblrV G α x t‖ ≤ bblrGammaLineMajorant α t*rectangularAFEMellinMass G/x := by
  have hGI := rectangular_BBLR_weight_vertical_integrable G α hG
  have hb := norm_integral_le_of_norm_le
    (hGI.const_mul (bblrGammaLineMajorant α t*Real.pi^(-2:ℝ)/x))
    (Filter.Eventually.of_forall (fun v => bblrVerticalIntegrand_norm_le G α x t v hx hα))
  change ‖(1/(2*Real.pi) : ℂ)*(∫ v : ℝ, bblrVerticalIntegrand G α x t v)‖ ≤ _
  rw [norm_mul]
  have hn : ‖(1/(2*Real.pi) : ℂ)‖ = 1/(2*Real.pi) := by
    simp [Complex.norm_real, abs_of_pos Real.pi_pos]
  rw [hn]
  calc
    _ ≤ (1/(2*Real.pi))*(∫ v : ℝ,
        (bblrGammaLineMajorant α t*Real.pi^(-2:ℝ)/x)*‖G (1+(v : ℂ)*I)‖) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [integral_const_mul]; unfold rectangularAFEMellinMass; ring

/-- The complete genuine fourfold AFE is interchanged with an actual compact
time weight. Both summability and dominating integrability are proved here. -/
theorem rectangular_actual_AFE_weighted_hasSum (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (hα : ∀ j, -1/2 < (α j).re)
    (w : ℝ → ℂ) (hw : Continuous w) (hws : HasCompactSupport w) :
    HasSum (fun n : Fin 4 → ℕ => ∫ t : ℝ, w t*bblrAFESummand G α t n)
      (∫ t : ℝ, w t*bblrAFESum G α t) := by
  let P : (Fin 4 → ℕ) → ℝ := fun n => ∏ j : Fin 4,
    1/(n j+1 : ℝ)^(3/2+(α j).re)
  have hs : ∀ j : Fin 4, Summable (fun n : ℕ => 1/(n+1 : ℝ)^(3/2+(α j).re)) := by
    intro j
    have hp := (Real.summable_one_div_nat_add_rpow 1 (3/2+(α j).re)).mpr
      (by have := hα j; linarith)
    have ha (n : ℕ) : |(n : ℝ)+1| = (n : ℝ)+1 := abs_of_pos (by positivity)
    simpa only [ha] using hp
  have hP : Summable P := summable_finitePi_prod_nonneg 4
    (fun j n => 1/(n+1 : ℝ)^(3/2+(α j).re)) (fun j n => by positivity) hs
  let B : ℝ → ℝ := fun t => ‖w t‖*(bblrGammaLineMajorant α t*rectangularAFEMellinMass G)
  have hBc : Continuous B :=
    hw.norm.mul ((rectangular_Gamma_line_majorant_continuous α hα).mul_const _)
  have hBs : HasCompactSupport B := by
    exact (hws.comp_left (show ‖(0:ℂ)‖ = (0:ℝ) by simp)).mul_right
  have hBi : Integrable B := hBc.integrable_of_hasCompactSupport hBs
  have hbound (n : Fin 4 → ℕ) (t : ℝ) :
      ‖w t*bblrAFESummand G α t n‖ ≤ B t*P n := by
    have hmaj := bblrAFESummand_norm_majorant G α t
      (bblrGammaLineMajorant α t*rectangularAFEMellinMass G)
      (fun x hx => rectangular_actual_V_height_majorant G α hG t x hx hα) n
    rw [norm_mul]
    calc
      _ ≤ ‖w t‖*((bblrGammaLineMajorant α t*rectangularAFEMellinMass G)*P n) :=
        mul_le_mul_of_nonneg_left hmaj (norm_nonneg _)
      _ = _ := by dsimp [B]; ring
  have hsum : HasSum
      (fun n : Fin 4 → ℕ => ∫ t : ℝ, w t*bblrAFESummand G α t n)
      (∫ t : ℝ, w t*bblrAFESum G α t) := by
    apply hasSum_integral_of_dominated_convergence (fun n t => B t*P n)
    · intro n
      exact (hw.stronglyMeasurable.mul
        (rectangular_actual_AFE_summand_stronglyMeasurable G
          (continuousOn_univ.mp hG.1.continuousOn) α hα n)).aestronglyMeasurable
    · intro n
      exact Filter.Eventually.of_forall (hbound n)
    · exact Filter.Eventually.of_forall (fun t => hP.mul_left (B t))
    · simp_rw [tsum_mul_left]
      exact hBi.mul_const _
    · filter_upwards [] with t
      exact (rectangular_actual_AFE_summable G α hG t hα).hasSum.mul_left (w t)
  exact hsum

theorem rectangular_actual_AFE_weighted_integral (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (hα : ∀ j, -1/2 < (α j).re)
    (w : ℝ → ℂ) (hw : Continuous w) (hws : HasCompactSupport w) :
    (∫ t : ℝ, w t*bblrAFESum G α t) =
      ∑' n : Fin 4 → ℕ, ∫ t : ℝ, w t*bblrAFESummand G α t n :=
  (rectangular_actual_AFE_weighted_hasSum G α hG hα w hw hws).tsum_eq.symm

/-- After the exact Bochner interchange, the actual time integral becomes
the sum of finite genuine dyadic blocks. No block reconstruction is assumed. -/
theorem rectangular_actual_AFE_dyadic_integral (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (hα : ∀ j, -1/2 < (α j).re)
    (w : ℝ → ℂ) (hw : Continuous w) (hws : HasCompactSupport w) :
    (∫ t : ℝ, w t*bblrAFESum G α t) =
      ∑' k : Fin 4 → ℕ, ∑ n ∈ rectangularAFEDyadicBox k,
        ∫ t : ℝ, w t*bblrAFESummand G α t n := by
  rw [rectangular_actual_AFE_weighted_integral G α hG hα w hw hws]
  exact rectangular_AFE_dyadic_grouping _
    (rectangular_actual_AFE_weighted_hasSum G α hG hα w hw hws).summable

def rectangularAFEIndexMajorant (α : MomentShifts) (n : Fin 4 → ℕ) : ℝ :=
  ∏ j : Fin 4, 1/(n j+1 : ℝ)^(3/2+(α j).re)

theorem rectangular_AFE_index_majorant_summable (α : MomentShifts)
    (hα : ∀ j, -1/2 < (α j).re) : Summable (rectangularAFEIndexMajorant α) := by
  have hs : ∀ j : Fin 4, Summable (fun n : ℕ => 1/(n+1 : ℝ)^(3/2+(α j).re)) := by
    intro j
    have hp := (Real.summable_one_div_nat_add_rpow 1 (3/2+(α j).re)).mpr
      (by have := hα j; linarith)
    have ha (n : ℕ) : |(n : ℝ)+1| = (n : ℝ)+1 := abs_of_pos (by positivity)
    simpa only [ha] using hp
  exact summable_finitePi_prod_nonneg 4
    (fun j n => 1/(n+1 : ℝ)^(3/2+(α j).re)) (fun j n => by positivity) hs

theorem rectangular_actual_AFE_height_majorant (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (t : ℝ) (hα : ∀ j, -1/2 < (α j).re) :
    ‖bblrAFESum G α t‖ ≤
      (bblrGammaLineMajorant α t*rectangularAFEMellinMass G)*
        ∑' n, rectangularAFEIndexMajorant α n := by
  exact tsum_of_norm_bounded
    ((rectangular_AFE_index_majorant_summable α hα).hasSum.mul_left
      (bblrGammaLineMajorant α t*rectangularAFEMellinMass G))
    (fun n => bblrAFESummand_norm_majorant G α t
      (bblrGammaLineMajorant α t*rectangularAFEMellinMass G)
      (fun x hx => rectangular_actual_V_height_majorant G α hG t x hx hα) n)

/-- The complete weighted AFE is genuinely Bochner-integrable. -/
theorem rectangular_actual_AFE_weighted_integrable (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (hα : ∀ j, -1/2 < (α j).re)
    (w : ℝ → ℂ) (hw : Continuous w) (hws : HasCompactSupport w) :
    Integrable (fun t : ℝ => w t*bblrAFESum G α t) := by
  let B : ℝ → ℝ := fun t => ‖w t‖*(bblrGammaLineMajorant α t*rectangularAFEMellinMass G)
  have hBc : Continuous B :=
    hw.norm.mul ((rectangular_Gamma_line_majorant_continuous α hα).mul_const _)
  have hBs : HasCompactSupport B :=
    (hws.comp_left (show ‖(0:ℂ)‖ = (0:ℝ) by simp)).mul_right
  have hm : StronglyMeasurable (fun t : ℝ => bblrAFESum G α t) :=
    StronglyMeasurable.tsum (fun n => rectangular_actual_AFE_summand_stronglyMeasurable G
      (continuousOn_univ.mp hG.1.continuousOn) α hα n)
  apply ((hBc.integrable_of_hasCompactSupport hBs).mul_const
    (∑' n, rectangularAFEIndexMajorant α n)).mono'
    (hw.stronglyMeasurable.mul hm).aestronglyMeasurable
  filter_upwards [] with t
  rw [Pi.mul_apply, norm_mul]
  calc
    _ ≤ ‖w t‖*((bblrGammaLineMajorant α t*rectangularAFEMellinMass G)*
        ∑' n, rectangularAFEIndexMajorant α n) :=
      mul_le_mul_of_nonneg_left (rectangular_actual_AFE_height_majorant G α hG t hα) (norm_nonneg _)
    _ = _ := by dsimp [B]; ring

end
end Sechstmoment
