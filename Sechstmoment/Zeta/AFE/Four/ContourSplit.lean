import Sechstmoment.Zeta.AFE.Four.FiniteRectangle
import Sechstmoment.Zeta.AFE.Four.FourDirichlet
import Sechstmoment.Zeta.AFE.Four.Geometry


namespace Sechstmoment.Source
open Complex MeasureTheory Set
open scoped BigOperators Topology
noncomputable section

def fixedAFEMellinIntegrand (G : ℂ → ℂ) (α : MomentShifts) (t : ℝ) (z : ℂ) : ℂ :=
  fixedAFECompletedKernel G α t z / z

def fixedAFEHorizontalError (G : ℂ → ℂ) (α : MomentShifts) (t : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * (-I) *
    ((∫ c in (-1 : ℝ)..1,
      fixedAFEMellinIntegrand G α t ((c : ℂ) + ((-t / 2 : ℝ) : ℂ) * I)) -
     (∫ c in (-1 : ℝ)..1,
      fixedAFEMellinIntegrand G α t ((c : ℂ) + (t / 2 : ℂ) * I)))

def fixedAFEVerticalTail (G : ℂ → ℂ) (α : MomentShifts) (t : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ((∫ v : ℝ, fixedAFEMellinIntegrand G α t (1 + (v : ℂ) * I)) -
     (∫ v in (-t / 2 : ℝ)..(t / 2),
      fixedAFEMellinIntegrand G α t (1 + (v : ℂ) * I)))

theorem fixedAFEMellinIntegrand_reflection (G : ℂ → ℂ) (α : MomentShifts)
    (t : ℝ) (z : ℂ) (hG : ∀ z, G (-z) = G z)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ)) :
    fixedAFEMellinIntegrand G α t (-z) =
      -bblrDualMultiplier t α * fixedAFEMellinIntegrand G (bblrSixShifts α 1) t z := by
  unfold fixedAFEMellinIntegrand
  rw [fixedAFECompletedKernel_reflection G α t z (hG z)
    (fixedAFEShiftedPoint_dual_Gammaℝ_ne_zero t α hα)]
  ring

theorem fixedAFE_truncated_left_eq_dual (G : ℂ → ℂ) (α : MomentShifts)
    (t h : ℝ) (hG : ∀ z, G (-z) = G z)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ)) :
    (∫ v in (-h)..h, fixedAFEMellinIntegrand G α t (-1 + (v : ℂ) * I)) =
      -bblrDualMultiplier t α *
        (∫ v in (-h)..h,
          fixedAFEMellinIntegrand G (bblrSixShifts α 1) t (1 + (v : ℂ) * I)) := by
  have hp (v : ℝ) :
      fixedAFEMellinIntegrand G α t (-1 + (v : ℂ) * I) =
        -bblrDualMultiplier t α *
          fixedAFEMellinIntegrand G (bblrSixShifts α 1) t
            (1 + ((-v : ℝ) : ℂ) * I) := by
    rw [show (-1 : ℂ) + (v : ℂ) * I =
      -(1 + ((-v : ℝ) : ℂ) * I) by push_cast; ring]
    exact fixedAFEMellinIntegrand_reflection G α t _ hG hα
  simp_rw [hp]
  rw [intervalIntegral.integral_const_mul]
  have hneg := intervalIntegral.integral_comp_neg
    (fun v : ℝ => fixedAFEMellinIntegrand G (bblrSixShifts α 1) t
      (1 + (v : ℂ) * I)) (a := -h) (b := h)
  change (∫ v in (-h)..h, fixedAFEMellinIntegrand G (bblrSixShifts α 1) t
    (1 + ((-v : ℝ) : ℂ) * I)) = _ at hneg
  rw [hneg]
  simp only [neg_neg]

theorem fixedAFE_discrepancy_eq_three_errors
    (G : ℂ → ℂ) (hG : BBLREntireWeight G (fun _ => 0))
    (t : ℝ) (ht : 16 ≤ t) (α : MomentShifts)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ)) :
    bblrAFEDiscrepancy G α t =
      fixedAFEHorizontalError G α t - fixedAFEVerticalTail G α t -
        bblrDualMultiplier t α * fixedAFEVerticalTail G (bblrSixShifts α 1) t := by
  have hαdual : ∀ j : Fin 4, ‖bblrSixShifts α 1 j‖ ≤ (1 / 4 : ℝ) := by
    intro j
    fin_cases j
    · simpa [bblrSixShifts] using hα 2
    · simpa [bblrSixShifts] using hα 3
    · simpa [bblrSixShifts] using hα 0
    · simpa [bblrSixShifts] using hα 1
  have hαre : ∀ j : Fin 4, -1 / 2 < (α j).re := by
    intro j
    have ha := (abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))).1
    linarith
  have hαdre : ∀ j : Fin 4, -1 / 2 < (bblrSixShifts α 1 j).re := by
    intro j
    have ha := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hαdual j))).1
    linarith
  have hres := fixedAFE_finite_rectangle_residue (fixedAFECompletedKernel G α t)
    (fixedAFERectangleNeighborhood_isOpen t)
    (fixedAFECompletedKernel_differentiableOn_neighborhood G hG t ht α hα)
    (show 0 < t / 2 by linarith)
    (by
      intro z hzr hzi
      exact fixedAFERectangle_subset_neighborhood t ⟨hzr, hzi⟩)
  rw [fixedAFECompletedKernel_zero G α t hG.2.2.1
    (fixedAFEShiftedPoint_ne_zero t α hα)
    (fixedAFEShiftedPoint_ne_one t α hα)] at hres
  change fixedAFERectangleBoundary (fixedAFEMellinIntegrand G α t) (t / 2) = _ at hres
  unfold fixedAFERectangleBoundary at hres
  rw [fixedAFE_truncated_left_eq_dual G α t (t / 2) hG.2.1 hα] at hres
  unfold bblrAFEDiscrepancy fixedAFEHorizontalError fixedAFEVerticalTail
  rw [fixedAFE_AFESum_eq_completed_right_integral G hG α t hαre,
    fixedAFE_AFESum_eq_completed_right_integral G hG (bblrSixShifts α 1) t hαdre]
  unfold verticalIntegral
  change _ = _
  have hp : (2 * Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  simp only [fixedAFEMellinIntegrand, neg_div, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_one,
    Complex.ofReal_neg] at hres ⊢
  field_simp [hp] at hres ⊢
  linear_combination (norm := (ring_nf; simp only [I_sq]; ring)) I * hres

end
end Sechstmoment.Source
