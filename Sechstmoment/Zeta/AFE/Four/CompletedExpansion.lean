import Sechstmoment.Zeta.AFE.Four.Geometry
import Sechstmoment.Zeta.AFE.Four.HorizontalDecay

/-!
# Exact expansion of the completed kernel on the finite contour

The shifted Gamma factors must be nonzero.  Excluding only the two poles
of completed zeta would be insufficient at the totalized Gamma poles.
The geometric hypotheses below exclude those points by their nonzero
imaginary parts.
-/

namespace Sechstmoment.Source
open Complex
open scoped BigOperators
noncomputable section

theorem fixedAFECompletedKernel_eq_gamma_zeta_of_ne_poles
    (G : ℂ → ℂ) (α : MomentShifts) (t : ℝ) (z : ℂ)
    (hs0 : ∀ j, fixedAFEShiftedPoint t α j + z ≠ 0)
    (hs1 : ∀ j, fixedAFEShiftedPoint t α j + z ≠ 1)
    (hΓ : ∀ j, Gammaℝ (fixedAFEShiftedPoint t α j + z) ≠ 0) :
    fixedAFECompletedKernel G α t z =
      G z * bblrGammaQuotient t α z * (Real.pi : ℂ) ^ (-2 * z) *
        ∏ j : Fin 4, riemannZeta (sourceZetaPoints t j + α j + z) := by
  have hterm (j : Fin 4) :
      fixedAFELambda (fixedAFEShiftedPoint t α j + z) /
          Gammaℝ (fixedAFEShiftedPoint t α j) =
        (Gammaℝ (fixedAFEShiftedPoint t α j + z) /
          Gammaℝ (fixedAFEShiftedPoint t α j)) *
          riemannZeta (fixedAFEShiftedPoint t α j + z) := by
    rw [fixedAFELambda_eq_completed (hs0 j) (hs1 j),
      riemannZeta_def_of_ne_zero (hs0 j)]
    symm
    calc
      _ = (completedRiemannZeta (fixedAFEShiftedPoint t α j + z) /
          Gammaℝ (fixedAFEShiftedPoint t α j)) *
          (Gammaℝ (fixedAFEShiftedPoint t α j + z) /
            Gammaℝ (fixedAFEShiftedPoint t α j + z)) := by ring
      _ = _ := by rw [div_self (hΓ j), mul_one]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpow : ((Real.pi : ℂ) ^ (-z / 2)) ^ 4 =
      (Real.pi : ℂ) ^ (-2 * z) := by
    symm
    rw [show -2 * z = (-z / 2 + -z / 2) + (-z / 2 + -z / 2) by ring]
    simp only [Complex.cpow_add _ _ hπ]
    ring
  unfold fixedAFECompletedKernel
  simp_rw [hterm]
  rw [Finset.prod_mul_distrib]
  simp_rw [gammaReal_shift_ratio]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hpow]
  unfold bblrGammaQuotient fixedAFEShiftedPoint
  ring

theorem fixedAFECompletedKernel_div_eq_explicit
    (G : ℂ → ℂ) (α : MomentShifts) (t : ℝ) (z : ℂ)
    (hs0 : ∀ j, fixedAFEShiftedPoint t α j + z ≠ 0)
    (hs1 : ∀ j, fixedAFEShiftedPoint t α j + z ≠ 1)
    (hΓ : ∀ j, Gammaℝ (fixedAFEShiftedPoint t α j + z) ≠ 0) :
    fixedAFECompletedKernel G α t z / z = bblrExplicitAFEIntegrand G α t z := by
  rw [fixedAFECompletedKernel_eq_gamma_zeta_of_ne_poles G α t z hs0 hs1 hΓ]
  unfold bblrExplicitAFEIntegrand
  ring

/-- Exact identity on the open finite-contour neighborhood, including both
horizontal edges of the rectangle. -/
theorem fixedAFECompletedKernel_div_eq_explicit_on_neighborhood
    (G : ℂ → ℂ) (t : ℝ) (ht : 16 ≤ t) (α : MomentShifts)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ))
    {z : ℂ} (hz : z ∈ fixedAFERectangleNeighborhood t) :
    fixedAFECompletedKernel G α t z / z = bblrExplicitAFEIntegrand G α t z := by
  exact fixedAFECompletedKernel_div_eq_explicit G α t z
    (fun j => fixedAFEArgument_ne_zero t ht α hα j hz)
    (fun j => fixedAFEArgument_ne_one t ht α hα j hz)
    (fun j => fixedAFEArgument_Gammaℝ_ne_zero t ht α hα j hz)

theorem fixedAFECompletedKernel_div_eq_explicit_on_rectangle
    (G : ℂ → ℂ) (t : ℝ) (ht : 16 ≤ t) (α : MomentShifts)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ))
    {z : ℂ} (hz : z ∈ fixedAFERectangle t) :
    fixedAFECompletedKernel G α t z / z = bblrExplicitAFEIntegrand G α t z := by
  exact fixedAFECompletedKernel_div_eq_explicit_on_neighborhood G t ht α hα
    (fixedAFERectangle_subset_neighborhood t hz)

/-- The same exact identity on the whole original AFE line, including its
two infinite tails.  No lower bound on the height is needed here. -/
theorem fixedAFECompletedKernel_div_eq_explicit_rightLine
    (G : ℂ → ℂ) (t : ℝ) (α : MomentShifts)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ)) (v : ℝ) :
    fixedAFECompletedKernel G α t (1 + (v : ℂ) * I) / (1 + (v : ℂ) * I) =
      bblrExplicitAFEIntegrand G α t (1 + (v : ℂ) * I) := by
  rw [fixedAFECompletedKernel_div_eq_gamma_zeta G α t (1 + (v : ℂ) * I)
    (fixedAFEArgument_rightLine_re_gt_one t α hα v)]
  unfold bblrExplicitAFEIntegrand
  ring

end
end Sechstmoment.Source
