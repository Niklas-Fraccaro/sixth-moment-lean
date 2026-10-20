import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Sechstmoment.Zeta.Regularized


namespace Sechstmoment.Source
open Complex Real Set Metric
noncomputable section

theorem riemannZeta_laurent_uniform_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ 1 →
      ‖riemannZeta (1+z)-z⁻¹‖ ≤ C := by
  have hcont : Continuous (deriv polarRegularizedZeta) :=
    polarRegularizedZeta_differentiable.deriv.continuous
  obtain ⟨B,hB⟩ := (isCompact_closedBall (1:ℂ) 1).exists_bound_of_continuousOn hcont.continuousOn
  let C := max 1 B
  refine ⟨C,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro z hz hnorm
  have hs : 1+z ≠ (1:ℂ) := by simpa using hz
  have H := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun s (_ : s ∈ closedBall (1:ℂ) 1) => polarRegularizedZeta_differentiable s)
    (fun s hs => (hB s hs).trans (le_max_right (1:ℝ) B))
    (convex_closedBall (1:ℂ) 1) (by simp : (1:ℂ) ∈ closedBall (1:ℂ) 1)
    (show 1+z ∈ closedBall (1:ℂ) 1 by simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left] using hnorm)
  have he : polarRegularizedZeta (1+z)-1 = z*(riemannZeta (1+z)-z⁻¹) := by
    rw [polarRegularizedZeta_of_ne_one hs,add_sub_cancel_left,mul_sub,mul_inv_cancel₀ hz]
  rw [polarRegularizedZeta_one,he,norm_mul,add_sub_cancel_left] at H
  exact (mul_le_mul_iff_of_pos_left (norm_pos_iff.mpr hz)).mp
    (H.trans_eq (mul_comm C ‖z‖))

theorem scaled_riemannZeta_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ L →
      ‖riemannZeta (1+z/(L:ℂ))/(L:ℂ)-1/z‖ ≤ C/L := by
  obtain ⟨C,hC,hbound⟩ := riemannZeta_laurent_uniform_bound
  refine ⟨C,hC,?_⟩
  intro L hL z hz hnorm
  have hL0 : 0 < L := by linarith
  have hLC : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL0.ne'
  have hsmall : ‖z/(L:ℂ)‖ ≤ 1 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL0]
    exact (div_le_one hL0).mpr hnorm
  have H := hbound (z/(L:ℂ)) (div_ne_zero hz hLC) hsmall
  have he : riemannZeta (1+z/(L:ℂ))/(L:ℂ)-1/z =
      (riemannZeta (1+z/(L:ℂ))-(z/(L:ℂ))⁻¹)/(L:ℂ) := by
    field_simp
  rw [he,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL0]
  exact div_le_div_of_nonneg_right H hL0.le

end
end Sechstmoment.Source
