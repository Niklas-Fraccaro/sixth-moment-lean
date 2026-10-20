import Mathlib.Tactic
import SixthMoment.Analysis.Complex.RealDerivatives
import SixthMoment.Analysis.Gaussian.Integrability
import SixthMoment.Zeta.AFE.Four.GammaComparison

namespace SixthMoment.Source
open Complex Set Metric
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

def bblrTimeGammaSign (j : Fin 4) : ℝ := if j.val < 2 then 1 else -1

def bblrTimeGammaBase (T : ℝ) (α : MomentShifts) (y : ℂ) (j : Fin 4) : ℂ :=
  ((1/2 : ℂ)+α j+(bblrTimeGammaSign j : ℂ)*I*(T : ℂ)*y)/2

def bblrTimeGammaQuotient (T : ℝ) (α : MomentShifts) (z y : ℂ) : ℂ :=
  ∏ j : Fin 4, Gamma (bblrTimeGammaBase T α y j+z/2)/
    Gamma (bblrTimeGammaBase T α y j)

theorem bblrTimeGammaQuotient_ofReal (T : ℝ) (α : MomentShifts) (z : ℂ) (y : ℝ) :
    bblrTimeGammaQuotient T α z (y : ℂ) = bblrGammaQuotient (T*y) α z := by
  unfold bblrTimeGammaQuotient bblrGammaQuotient
  apply Finset.prod_congr rfl
  intro j _
  have hb : bblrTimeGammaBase T α (y : ℂ) j =
      (sourceZetaPoints (T*y) j+α j)/2 := by
    fin_cases j <;> simp [bblrTimeGammaBase,bblrTimeGammaSign,sourceZetaPoints,
      criticalLinePoint] <;> ring
  rw [hb]
  congr 2
  ring

theorem bblrTimeGammaBase_geometry {T A : ℝ} (hA : 0 ≤ A)
    (hT : 8*(A+1) ≤ T) (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ A)
    {y : ℂ} (hyre : y.re ∈ Icc (3/4 : ℝ) (9/4)) (hyim : |y.im| ≤ 1/4)
    (j : Fin 4) :
    T/4 ≤ |(bblrTimeGammaBase T α y j).im| ∧
    -|(bblrTimeGammaBase T α y j).im| ≤ (bblrTimeGammaBase T α y j).re ∧
    ‖bblrTimeGammaBase T α y j‖ ≤ 2*T := by
  have hT0 : 0 < T := by linarith
  have hare := abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))
  have haim := abs_le.mp ((Complex.abs_im_le_norm (α j)).trans (hα j))
  have hyi := abs_le.mp hyim
  have hre : |y.re| ≤ 9/4 := by rw [abs_of_nonneg (by linarith [hyre.1])]; exact hyre.2
  have hyn : ‖y‖ ≤ 5/2 := by
    exact (Complex.norm_le_abs_re_add_abs_im y).trans (by linarith)
  have hs : |bblrTimeGammaSign j| = 1 := by
    unfold bblrTimeGammaSign
    split_ifs <;> norm_num
  have hsi : T/4 ≤ |(bblrTimeGammaBase T α y j).im| := by
    have he : (bblrTimeGammaBase T α y j).im =
        ((α j).im+bblrTimeGammaSign j*T*y.re)/2 := by
      simp [bblrTimeGammaBase, Complex.mul_re, Complex.mul_im]
    rw [he]
    unfold bblrTimeGammaSign
    split_ifs
    · norm_num
      nlinarith [hyre.1, le_abs_self (((α j).im+T*y.re)/2)]
    · norm_num
      change T/4 ≤ |((α j).im-T*y.re)/2|
      nlinarith [hyre.1, neg_le_abs (((α j).im-T*y.re)/2)]
  refine ⟨hsi,?_,?_⟩
  · have he : (bblrTimeGammaBase T α y j).re =
        (1/2+(α j).re-bblrTimeGammaSign j*T*y.im)/2 := by
      simp [bblrTimeGammaBase, Complex.mul_re, Complex.mul_im]
      ring
    rw [he]
    unfold bblrTimeGammaSign
    split_ifs <;> norm_num <;> nlinarith
  · unfold bblrTimeGammaBase
    rw [norm_div,Complex.norm_ofNat]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have hm : ‖(bblrTimeGammaSign j : ℂ)*I*(T : ℂ)*y‖ ≤ T*(5/2) := by
      rw [norm_mul,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,hs,
        Complex.norm_I,one_mul,one_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos hT0]
      exact mul_le_mul_of_nonneg_left hyn hT0.le
    have hh := norm_add_le ((1/2 : ℂ)+α j)
      ((bblrTimeGammaSign j : ℂ)*I*(T : ℂ)*y)
    have ha := norm_add_le (1/2 : ℂ) (α j)
    norm_num at ha
    nlinarith [hα j]

end
end SixthMoment.Source
