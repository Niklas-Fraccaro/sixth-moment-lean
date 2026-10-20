import Sechstmoment.Zeta.AFE.Four.Specification
import Sechstmoment.Zeta.AFE.Two.Contour


namespace Sechstmoment.Source
open Complex
open scoped BigOperators
noncomputable section

def fixedAFELambda (s : ℂ) : ℂ :=
  d02CompletedPoleRemoved s / (s * (1-s))

def fixedAFEShiftedPoint (t : ℝ) (α : MomentShifts) (j : Fin 4) : ℂ :=
  sourceZetaPoints t j + α j

def fixedAFECompletedKernel (G : ℂ → ℂ)
    (α : MomentShifts) (t : ℝ) (z : ℂ) : ℂ :=
  G z * ∏ j : Fin 4,
    fixedAFELambda (fixedAFEShiftedPoint t α j + z) /
      Gammaℝ (fixedAFEShiftedPoint t α j)

theorem fixedAFELambda_eq_completed {s : ℂ} (hs : s ≠ 0) (hs1 : s ≠ 1) :
    fixedAFELambda s = completedRiemannZeta s := by
  have hden : s * (1-s) ≠ 0 :=
    mul_ne_zero hs (sub_ne_zero.mpr (Ne.symm hs1))
  rw [fixedAFELambda, d02CompletedPoleRemoved_eq hs hs1]
  exact mul_div_cancel_left₀ _ hden

theorem fixedAFELambda_one_sub (s : ℂ) :
    fixedAFELambda (1-s) = fixedAFELambda s := by
  simp only [fixedAFELambda, d02CompletedPoleRemoved_one_sub]
  congr 1
  ring

theorem fixedAFELambda_differentiableAt {s : ℂ} (hs : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ fixedAFELambda s := by
  unfold fixedAFELambda
  exact d02CompletedPoleRemoved_differentiable.differentiableAt.div
    (by fun_prop) (mul_ne_zero hs (sub_ne_zero.mpr (Ne.symm hs1)))

def fixedAFEDualIndex : Fin 4 → Fin 4 := ![2, 3, 0, 1]

@[simp] theorem fixedAFEDualIndex_involutive (j : Fin 4) :
    fixedAFEDualIndex (fixedAFEDualIndex j) = j := by
  fin_cases j <;> rfl

theorem fixedAFEShiftedPoint_dual (t : ℝ) (α : MomentShifts) (j : Fin 4) :
    fixedAFEShiftedPoint t (bblrSixShifts α 1) j =
      1-fixedAFEShiftedPoint t α (fixedAFEDualIndex j) := by
  fin_cases j <;>
    simp [fixedAFEShiftedPoint, sourceZetaPoints, bblrSixShifts, fixedAFEDualIndex] <;>
    ring

theorem fixedAFECompletedKernel_zero (G : ℂ → ℂ) (α : MomentShifts) (t : ℝ)
    (hG : G 0 = 1)
    (hs : ∀ j, fixedAFEShiftedPoint t α j ≠ 0)
    (hs1 : ∀ j, fixedAFEShiftedPoint t α j ≠ 1) :
    fixedAFECompletedKernel G α t 0 = shiftedFourthProduct t α := by
  unfold fixedAFECompletedKernel
  simp only [add_zero, hG, one_mul]
  have he (j : Fin 4) : fixedAFELambda (fixedAFEShiftedPoint t α j) /
      Gammaℝ (fixedAFEShiftedPoint t α j) =
      riemannZeta (fixedAFEShiftedPoint t α j) := by
    rw [fixedAFELambda_eq_completed (hs j) (hs1 j)]
    exact (riemannZeta_def_of_ne_zero (hs j)).symm
  simp_rw [he]
  simp [shiftedFourthProduct, fixedAFEShiftedPoint, sourceZetaPoints,
    Fin.prod_univ_succ, mul_assoc]

theorem fixedAFECompletedKernel_reflection (G : ℂ → ℂ) (α : MomentShifts)
    (t : ℝ) (z : ℂ) (hG : G (-z) = G z)
    (hΓ : ∀ j, Gammaℝ (1-fixedAFEShiftedPoint t α j) ≠ 0) :
    fixedAFECompletedKernel G α t (-z) =
      bblrDualMultiplier t α *
        fixedAFECompletedKernel G (bblrSixShifts α 1) t z := by
  have he (j : Fin 4) :
      fixedAFELambda (fixedAFEShiftedPoint t α j + -z) =
        fixedAFELambda (1-fixedAFEShiftedPoint t α j+z) := by
    rw [show fixedAFEShiftedPoint t α j + -z =
      1-(1-fixedAFEShiftedPoint t α j+z) by ring,
      fixedAFELambda_one_sub]
  unfold fixedAFECompletedKernel bblrDualMultiplier
  rw [hG]
  simp_rw [he, fixedAFEShiftedPoint_dual, zetaChi]
  change G z * (∏ j : Fin 4, fixedAFELambda (1-fixedAFEShiftedPoint t α j+z) /
      Gammaℝ (fixedAFEShiftedPoint t α j)) =
    (∏ j : Fin 4, Gammaℝ (1-fixedAFEShiftedPoint t α j) /
      Gammaℝ (fixedAFEShiftedPoint t α j)) *
      (G z * ∏ j : Fin 4,
        fixedAFELambda (1-fixedAFEShiftedPoint t α (fixedAFEDualIndex j)+z) /
          Gammaℝ (1-fixedAFEShiftedPoint t α (fixedAFEDualIndex j)))
  have hperm (f : Fin 4 → ℂ) :
      (∏ j : Fin 4, f (fixedAFEDualIndex j)) = ∏ j : Fin 4, f j := by
    simp [Fin.prod_univ_succ, fixedAFEDualIndex]
    ring
  rw [hperm (fun j => fixedAFELambda (1-fixedAFEShiftedPoint t α j+z) /
    Gammaℝ (1-fixedAFEShiftedPoint t α j))]
  have hterm (j : Fin 4) :
      (Gammaℝ (1-fixedAFEShiftedPoint t α j) /
        Gammaℝ (fixedAFEShiftedPoint t α j)) *
      (fixedAFELambda (1-fixedAFEShiftedPoint t α j+z) /
        Gammaℝ (1-fixedAFEShiftedPoint t α j)) =
      fixedAFELambda (1-fixedAFEShiftedPoint t α j+z) /
        Gammaℝ (fixedAFEShiftedPoint t α j) := by
    calc
      _ = (fixedAFELambda (1-fixedAFEShiftedPoint t α j+z) /
          Gammaℝ (fixedAFEShiftedPoint t α j)) *
          (Gammaℝ (1-fixedAFEShiftedPoint t α j) /
            Gammaℝ (1-fixedAFEShiftedPoint t α j)) := by ring
      _ = _ := by rw [div_self (hΓ j), mul_one]
  calc
    _ = G z * ∏ j : Fin 4,
        (Gammaℝ (1-fixedAFEShiftedPoint t α j) /
          Gammaℝ (fixedAFEShiftedPoint t α j)) *
        (fixedAFELambda (1-fixedAFEShiftedPoint t α j+z) /
          Gammaℝ (1-fixedAFEShiftedPoint t α j)) := by simp_rw [hterm]
    _ = _ := by rw [Finset.prod_mul_distrib]; ring

theorem fixedAFECompletedKernel_eq_gamma_zeta (G : ℂ → ℂ) (α : MomentShifts)
    (t : ℝ) (z : ℂ)
    (hz : ∀ j, 1 < (fixedAFEShiftedPoint t α j+z).re) :
    fixedAFECompletedKernel G α t z =
      G z * bblrGammaQuotient t α z * (Real.pi : ℂ)^(-2*z) *
        ∏ j : Fin 4, riemannZeta (sourceZetaPoints t j+α j+z) := by
  have hterm (j : Fin 4) :
      fixedAFELambda (fixedAFEShiftedPoint t α j+z) /
        Gammaℝ (fixedAFEShiftedPoint t α j) =
      (Gammaℝ (fixedAFEShiftedPoint t α j+z) /
        Gammaℝ (fixedAFEShiftedPoint t α j)) *
        riemannZeta (fixedAFEShiftedPoint t α j+z) := by
    have hs0 : fixedAFEShiftedPoint t α j+z ≠ 0 := by
      intro h
      have hr := hz j
      norm_num [h] at hr
    have hs1 : fixedAFEShiftedPoint t α j+z ≠ 1 := by
      intro h
      have hr := hz j
      norm_num [h] at hr
    have hΓ := Gammaℝ_ne_zero_of_re_pos (lt_trans (by norm_num) (hz j))
    rw [fixedAFELambda_eq_completed hs0 hs1,
      riemannZeta_def_of_ne_zero hs0]
    symm
    calc
      _ = (completedRiemannZeta (fixedAFEShiftedPoint t α j+z) /
          Gammaℝ (fixedAFEShiftedPoint t α j)) *
          (Gammaℝ (fixedAFEShiftedPoint t α j+z) /
            Gammaℝ (fixedAFEShiftedPoint t α j+z)) := by ring
      _ = _ := by rw [div_self hΓ, mul_one]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpow : ((Real.pi : ℂ)^(-z/2))^4 = (Real.pi : ℂ)^(-2*z) := by
    symm
    rw [show -2*z = (-z/2+-z/2)+(-z/2+-z/2) by ring]
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

theorem fixedAFECompletedKernel_div_eq_gamma_zeta (G : ℂ → ℂ) (α : MomentShifts)
    (t : ℝ) (z : ℂ)
    (hz : ∀ j, 1 < (fixedAFEShiftedPoint t α j+z).re) :
    fixedAFECompletedKernel G α t z / z =
      G z / z * bblrGammaQuotient t α z * (Real.pi : ℂ)^(-2*z) *
        ∏ j : Fin 4, riemannZeta (sourceZetaPoints t j+α j+z) := by
  rw [fixedAFECompletedKernel_eq_gamma_zeta G α t z hz]
  ring

end
end Sechstmoment.Source
