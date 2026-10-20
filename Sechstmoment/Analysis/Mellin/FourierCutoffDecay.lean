import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Sechstmoment.Analysis.Mellin.FourierCutoffUniform


namespace Sechstmoment.Source
open Complex Real MeasureTheory
open scoped ContDiff FourierTransform
noncomputable section

theorem schwartz_fourier_power_norm_bound (h : SchwartzMap ℝ ℂ) (n : ℕ) (x : ℝ) :
    (2*Real.pi* |x|)^n*‖𝓕 (h:ℝ → ℂ) x‖ ≤ ∫ ξ : ℝ, ‖iteratedDeriv n h ξ‖ := by
  have hi (j : ℕ) : Integrable (iteratedDeriv j (h:ℝ → ℂ)) :=
    (integrable_norm_iff ((h.smooth').continuous_iteratedDeriv j (by simp)).aestronglyMeasurable).mp
      (schwartz_iteratedDeriv_norm_integrable h j)
  have he : 𝓕 (iteratedDeriv n (h:ℝ → ℂ)) x =
      (2*Real.pi*I*(x:ℂ))^n • 𝓕 (h:ℝ → ℂ) x := by
    simpa only using! congrFun
      (Real.fourier_iteratedDeriv h.smooth' (fun j _ => hi j) (n := n) (by simp)) x
  have H : ‖𝓕 (iteratedDeriv n (h:ℝ → ℂ)) x‖ ≤ ∫ ξ : ℝ, ‖iteratedDeriv n h ξ‖ := by
    rw [Real.fourier_eq]
    apply (norm_integral_le_integral_norm _).trans_eq
    simp only [Circle.norm_smul]
  have hcoef : ‖(2*Real.pi*I*(x:ℂ):ℂ)‖ = 2*Real.pi* |x| := by
    simp
  rw [he,norm_smul,norm_pow,hcoef] at H
  exact H

theorem noDPFourierCutoff_uniform_fourier_decay (h : SchwartzMap ℝ ℂ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 1 ≤ H → ∀ x : ℝ,
      (2*Real.pi* |x|)^n*‖𝓕 (noDPFourierCutoff h H) x‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := noDPFourierCutoff_uniform_derivative_mass h n
  refine ⟨C,hC,?_⟩
  intro H hH x
  have hH0 : 0 < H := by linarith
  exact (schwartz_fourier_power_norm_bound (noDPFourierCutoffSchwartz h H hH0) n x).trans (hbound H hH)

theorem noDPFourierCutoff_uniform_inverse_decay (h : SchwartzMap ℝ ℂ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 1 ≤ H → ∀ x : ℝ,
      (2*Real.pi* |x|)^n*‖𝓕⁻ (noDPFourierCutoff h H) x‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := noDPFourierCutoff_uniform_fourier_decay h n
  refine ⟨C,hC,?_⟩
  intro H hH x
  rw [fourierInv_eq_fourier_neg]
  simpa only [abs_neg] using hbound H hH (-x)

end
end Sechstmoment.Source
