import SixthMoment.Numerator.V.Asymptotic.LogProfileBound
import SixthMoment.Zeta.Bounds.ZetaLogBound


namespace SixthMoment.Source
open Complex Real Set
open scoped BigOperators
noncomputable section

def noDPRightLine (T R : ℝ) : ℝ := 1+(R+2)/Real.log T

theorem noDPRightLine_shift_lower {T R : ℝ} (hL : 1 ≤ Real.log T)
    {α : ℂ} (hα : ‖α‖ ≤ R/Real.log T) (t : ℝ) :
    1+1/Real.log T ≤ (((noDPRightLine T R:ℝ):ℂ)+(t:ℂ)*I+α).re := by
  have hL0 : 0 < Real.log T := by linarith
  have hre := abs_le.mp ((Complex.abs_re_le_norm α).trans hα)
  have hgap : 1/Real.log T ≤ (R+2)/Real.log T-R/Real.log T := by
    rw [← sub_div]
    apply div_le_div_of_nonneg_right _ hL0.le
    linarith
  simp only [noDPRightLine,add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero]
  linarith [hre.1]

theorem noDPRightLine_in_contour {T R : ℝ} (hR : 0 ≤ R)
    (hL : 4*(R+2) ≤ Real.log T) :
    noDPRightLine T R ∈ Icc (1:ℝ) (5/4) := by
  have hL0 : 0 < Real.log T := by linarith
  have hnonneg : 0 ≤ (R+2)/Real.log T := div_nonneg (by linarith) hL0.le
  have hupper : (R+2)/Real.log T ≤ 1/4 := by
    apply (div_le_iff₀ hL0).mpr
    linarith
  unfold noDPRightLine
  exact ⟨by linarith,by linarith⟩

theorem four_zeta_starting_line_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T R : ℝ, 1 ≤ Real.log T → 0 ≤ R →
      ∀ α : Fin 4 → ℂ, (∀ j, ‖α j‖ ≤ R/Real.log T) → ∀ t : ℝ,
      ‖∏ j : Fin 4, riemannZeta
        (((noDPRightLine T R:ℝ):ℂ)+(t:ℂ)*I+α j)‖ ≤ C*(Real.log T)^4 := by
  obtain ⟨C,hC,hzeta⟩ := riemannZeta_log_line_bound
  refine ⟨C^4,by positivity,?_⟩
  intro T R hL _hR α hα t
  rw [norm_prod]
  calc
    _ ≤ ∏ _j : Fin 4, C*Real.log T := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro j _
      exact hzeta (Real.log T) hL _ (noDPRightLine_shift_lower hL (hα j) t)
    _ = _ := by simp; ring

end
end SixthMoment.Source
