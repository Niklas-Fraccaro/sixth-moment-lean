import SixthMoment.Zeta.AFE.Four.Integrability
import SixthMoment.Zeta.AFE.Four.Kernel


namespace SixthMoment.Source
open Complex Set
open scoped BigOperators Topology
noncomputable section

def fixedAFERectangle (t : ℝ) : Set ℂ :=
  {z | |z.re| ≤ 1 ∧ |z.im| ≤ t / 2}

def fixedAFERectangleNeighborhood (t : ℝ) : Set ℂ :=
  {z | |z.im| < t / 2 + 1}

theorem fixedAFERectangleNeighborhood_isOpen (t : ℝ) :
    IsOpen (fixedAFERectangleNeighborhood t) := by
  exact isOpen_lt (by fun_prop) continuous_const

theorem fixedAFERectangle_subset_neighborhood (t : ℝ) :
    fixedAFERectangle t ⊆ fixedAFERectangleNeighborhood t := by
  intro z hz
  exact lt_of_le_of_lt hz.2 (by linarith)

@[simp] theorem fixedAFEShiftedPoint_re (t : ℝ) (α : MomentShifts) (j : Fin 4) :
    (fixedAFEShiftedPoint t α j).re = 1 / 2 + (α j).re := by
  simp [fixedAFEShiftedPoint]

theorem fixedAFEShiftedPoint_re_pos (t : ℝ) (α : MomentShifts)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ)) (j : Fin 4) :
    0 < (fixedAFEShiftedPoint t α j).re := by
  have ha := (abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))).1
  rw [fixedAFEShiftedPoint_re]
  linarith

theorem fixedAFEShiftedPoint_Gammaℝ_ne_zero (t : ℝ) (α : MomentShifts)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ)) (j : Fin 4) :
    Gammaℝ (fixedAFEShiftedPoint t α j) ≠ 0 := by
  exact Gammaℝ_ne_zero_of_re_pos (fixedAFEShiftedPoint_re_pos t α hα j)

theorem fixedAFEShiftedPoint_ne_zero (t : ℝ) (α : MomentShifts)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ)) (j : Fin 4) :
    fixedAFEShiftedPoint t α j ≠ 0 := by
  intro he
  have hp := fixedAFEShiftedPoint_re_pos t α hα j
  simp [he] at hp

theorem fixedAFEShiftedPoint_ne_one (t : ℝ) (α : MomentShifts)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ)) (j : Fin 4) :
    fixedAFEShiftedPoint t α j ≠ 1 := by
  intro he
  have ha := (abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))).2
  have hr := fixedAFEShiftedPoint_re t α j
  rw [he] at hr
  norm_num at hr
  linarith

theorem fixedAFEShiftedPoint_dual_Gammaℝ_ne_zero (t : ℝ) (α : MomentShifts)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ)) (j : Fin 4) :
    Gammaℝ (1 - fixedAFEShiftedPoint t α j) ≠ 0 := by
  apply Gammaℝ_ne_zero_of_re_pos
  have ha := (abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))).2
  simp only [sub_re, one_re, fixedAFEShiftedPoint_re]
  linarith

theorem fixedAFEArgument_im_abs_lower (t : ℝ) (ht : 0 ≤ t)
    (α : MomentShifts) (hα : ∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ))
    (j : Fin 4) (z : ℂ) :
    t - 1 / 4 - |z.im| ≤ |(fixedAFEShiftedPoint t α j + z).im| := by
  have hs : |(sourceZetaPoints t j).im| = t := by
    fin_cases j <;>
      simp [sourceZetaPoints, criticalLinePoint, abs_of_nonneg ht]
  have ha : |(α j).im| ≤ (1 / 4 : ℝ) :=
    (Complex.abs_im_le_norm (α j)).trans (hα j)
  have hadd := abs_add_le (fixedAFEShiftedPoint t α j + z).im
    (-((α j).im + z.im))
  have hcancel : (fixedAFEShiftedPoint t α j + z).im +
      -((α j).im + z.im) = (sourceZetaPoints t j).im := by
    simp only [fixedAFEShiftedPoint, add_im]
    ring
  rw [hcancel, hs, abs_neg] at hadd
  have htail := abs_add_le (α j).im z.im
  linarith

theorem fixedAFEArgument_im_ne_zero (t : ℝ) (ht : 16 ≤ t)
    (α : MomentShifts) (hα : ∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ))
    (j : Fin 4) {z : ℂ} (hz : z ∈ fixedAFERectangleNeighborhood t) :
    (fixedAFEShiftedPoint t α j + z).im ≠ 0 := by
  apply abs_pos.mp
  have hl := fixedAFEArgument_im_abs_lower t (by linarith) α hα j z
  change |z.im| < t / 2 + 1 at hz
  linarith

theorem fixedAFEArgument_ne_zero (t : ℝ) (ht : 16 ≤ t)
    (α : MomentShifts) (hα : ∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ))
    (j : Fin 4) {z : ℂ} (hz : z ∈ fixedAFERectangleNeighborhood t) :
    fixedAFEShiftedPoint t α j + z ≠ 0 := by
  intro he
  apply fixedAFEArgument_im_ne_zero t ht α hα j hz
  simp [he]

theorem fixedAFEArgument_ne_one (t : ℝ) (ht : 16 ≤ t)
    (α : MomentShifts) (hα : ∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ))
    (j : Fin 4) {z : ℂ} (hz : z ∈ fixedAFERectangleNeighborhood t) :
    fixedAFEShiftedPoint t α j + z ≠ 1 := by
  intro he
  apply fixedAFEArgument_im_ne_zero t ht α hα j hz
  simp [he]

theorem fixedAFEArgument_Gammaℝ_ne_zero (t : ℝ) (ht : 16 ≤ t)
    (α : MomentShifts) (hα : ∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ))
    (j : Fin 4) {z : ℂ} (hz : z ∈ fixedAFERectangleNeighborhood t) :
    Gammaℝ (fixedAFEShiftedPoint t α j + z) ≠ 0 := by
  intro he
  obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp he
  apply fixedAFEArgument_im_ne_zero t ht α hα j hz
  simpa using congrArg Complex.im hn

theorem fixedAFEArgument_rightLine_re_gt_one (t : ℝ) (α : MomentShifts)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ)) (v : ℝ) (j : Fin 4) :
    1 < (fixedAFEShiftedPoint t α j + (1 + (v : ℂ) * I)).re := by
  have ha := (abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))).1
  simp only [add_re, fixedAFEShiftedPoint_re, one_re, mul_re,
    ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
  linarith

theorem fixedAFEArgument_im_abs_lower_on_rectangle (t : ℝ) (ht : 0 ≤ t)
    (α : MomentShifts) (hα : ∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ))
    (j : Fin 4) {z : ℂ} (hz : z ∈ fixedAFERectangle t) :
    t / 2 - 1 / 4 ≤ |(fixedAFEShiftedPoint t α j + z).im| := by
  have hl := fixedAFEArgument_im_abs_lower t ht α hα j z
  have hz' := hz.2
  linarith

theorem fixedAFEArgument_re_mem (t : ℝ) (α : MomentShifts)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ)) (j : Fin 4)
    {z : ℂ} (hz : z ∈ fixedAFERectangle t) :
    (fixedAFEShiftedPoint t α j + z).re ∈ Icc (-1 : ℝ) 2 := by
  have ha := abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))
  have hzr := abs_le.mp hz.1
  simp only [mem_Icc, add_re, fixedAFEShiftedPoint_re]
  constructor <;> linarith [ha.1, ha.2, hzr.1, hzr.2]

theorem fixedAFEArgument_half_re_mem (t : ℝ) (α : MomentShifts)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ)) (j : Fin 4)
    {z : ℂ} (hz : z ∈ fixedAFERectangle t) :
    ((fixedAFEShiftedPoint t α j + z) / 2).re ∈ Icc (-1 : ℝ) 2 := by
  have hr := fixedAFEArgument_re_mem t α hα j hz
  simp only [Complex.div_ofNat_re, mem_Icc]
  constructor <;> linarith [hr.1, hr.2]

theorem fixedAFEArgument_half_one_le_abs_im (t : ℝ) (ht : 16 ≤ t)
    (α : MomentShifts) (hα : ∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ))
    (j : Fin 4) {z : ℂ} (hz : z ∈ fixedAFERectangle t) :
    1 ≤ |((fixedAFEShiftedPoint t α j + z) / 2).im| := by
  have hl := fixedAFEArgument_im_abs_lower_on_rectangle t (by linarith) α hα j hz
  simp only [Complex.div_ofNat_im, abs_div,
    show |(2 : ℝ)| = 2 by norm_num]
  linarith

theorem fixedAFEArgument_one_le_norm_sub_one (t : ℝ) (ht : 16 ≤ t)
    (α : MomentShifts) (hα : ∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ))
    (j : Fin 4) {z : ℂ} (hz : z ∈ fixedAFERectangle t) :
    1 ≤ ‖fixedAFEShiftedPoint t α j + z - 1‖ := by
  have hl := fixedAFEArgument_im_abs_lower_on_rectangle t (by linarith) α hα j hz
  have hn := Complex.abs_im_le_norm (fixedAFEShiftedPoint t α j + z - 1)
  simp only [sub_im, one_im, sub_zero] at hn
  linarith

theorem fixedAFECompletedKernel_differentiableOn_neighborhood
    (G : ℂ → ℂ) (hG : BBLREntireWeight G (fun _ => 0))
    (t : ℝ) (ht : 16 ≤ t) (α : MomentShifts)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ)) :
    DifferentiableOn ℂ (fixedAFECompletedKernel G α t)
      (fixedAFERectangleNeighborhood t) := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  have hdiffG : DifferentiableAt ℂ G z :=
    (hG.1 z (mem_univ z)).differentiableAt
  have hfactor (j : Fin 4) : DifferentiableAt ℂ
      (fun w : ℂ => fixedAFELambda (fixedAFEShiftedPoint t α j + w) /
        Gammaℝ (fixedAFEShiftedPoint t α j)) z := by
    exact ((fixedAFELambda_differentiableAt
      (fixedAFEArgument_ne_zero t ht α hα j hz)
      (fixedAFEArgument_ne_one t ht α hα j hz)).comp z
        (by fun_prop)).div_const _
  unfold fixedAFECompletedKernel
  exact hdiffG.mul (DifferentiableAt.fun_finsetProd (fun j _ => hfactor j))

theorem fixedAFECompletedKernel_differentiableOn_rectangle
    (G : ℂ → ℂ) (hG : BBLREntireWeight G (fun _ => 0))
    (t : ℝ) (ht : 16 ≤ t) (α : MomentShifts)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ)) :
    DifferentiableOn ℂ (fixedAFECompletedKernel G α t) (fixedAFERectangle t) := by
  exact (fixedAFECompletedKernel_differentiableOn_neighborhood G hG t ht α hα).mono
    (fixedAFERectangle_subset_neighborhood t)

theorem fixedAFECompletedKernel_zero_smallShifts
    (G : ℂ → ℂ) (hG : BBLREntireWeight G (fun _ => 0))
    (t : ℝ) (α : MomentShifts)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ)) :
    fixedAFECompletedKernel G α t 0 = shiftedFourthProduct t α := by
  exact fixedAFECompletedKernel_zero G α t hG.2.2.1
    (fixedAFEShiftedPoint_ne_zero t α hα)
    (fixedAFEShiftedPoint_ne_one t α hα)

theorem fixedAFECompletedKernel_reflection_smallShifts
    (G : ℂ → ℂ) (hG : BBLREntireWeight G (fun _ => 0))
    (t : ℝ) (α : MomentShifts)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ)) (z : ℂ) :
    fixedAFECompletedKernel G α t (-z) =
      bblrDualMultiplier t α *
        fixedAFECompletedKernel G (bblrSixShifts α 1) t z := by
  exact fixedAFECompletedKernel_reflection G α t z (hG.2.1 z)
    (fixedAFEShiftedPoint_dual_Gammaℝ_ne_zero t α hα)

end
end SixthMoment.Source
