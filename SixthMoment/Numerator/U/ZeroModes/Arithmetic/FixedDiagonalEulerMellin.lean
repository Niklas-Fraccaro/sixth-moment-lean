import SixthMoment.Numerator.U.ZeroModes.Arithmetic.CorrelationEuler
import SixthMoment.Numerator.U.ZeroModes.Arithmetic.FixedDiagonalCorrelation


namespace SixthMoment
open Complex Source
open scoped BigOperators
open Classical

set_option maxHeartbeats 0
noncomputable section

theorem bblrDiagonalTerm_eq_fixedEulerMellin {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b) {t : ℝ} (ht : 0 < t)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ 1/8) :
    bblrDiagonalTerm G α a b t = verticalIntegral 1 (fun z =>
      G z/z*(t/(2*Real.pi):ℂ)^(2*z)*((a*b:ℕ):ℂ)^(-(1+z))*
        (bblrAArithmetic (α 0+z) (α 1+z) (α 2+z) (α 3+z)*
          bblrBFactorAt (α 0) (α 1) (α 2) (α 3) z a*
          bblrBFactorAt (α 2) (α 3) (α 0) (α 1) z b)) := by
  have hre (j : Fin 4) : -1/2<(α j).re := by
    have h := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hα j))).1
    linarith
  rw [bblrDiagonalTerm_eq_fixedCorrelationMellin_normalized ha hb hab ht G α hG hre]
  unfold verticalIntegral
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with v
  simp only [Complex.ofReal_one]
  rw [shiftedPairCorrelation_initial_eq_fourZeta_mul_BAt hα
    (show (1/4:ℝ)≤(1+(v:ℂ)*I).re by simp; norm_num) ha hb hab]

end
end SixthMoment
