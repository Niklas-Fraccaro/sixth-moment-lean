import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linarith

namespace Sechstmoment

open MeasureTheory
open scoped InnerProductSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem l2_integral_norm_sq (f : α →₂[μ] ℂ) :
    (∫ x, ‖f x‖^2 ∂μ) = ‖f‖^2 := by
  calc
    (∫ x, ‖f x‖^2 ∂μ) = ∫ x, RCLike.re (inner ℂ (f x) (f x)) ∂μ := by
      simp only [inner_self_eq_norm_sq]
    _ = RCLike.re (∫ x, inner ℂ (f x) (f x) ∂μ) :=
      integral_re (L2.integrable_inner (𝕜 := ℂ) f f)
    _ = RCLike.re (inner ℂ f f) := by rw [← L2.inner_def]
    _ = ‖f‖^2 := inner_self_eq_norm_sq f

theorem integral_cauchy_schwarz (f g : α →₂[μ] ℂ) :
    ‖∫ x, star (f x) * g x ∂μ‖^2 ≤
      (∫ x, ‖f x‖^2 ∂μ) * (∫ x, ‖g x‖^2 ∂μ) := by
  rw [l2_integral_norm_sq, l2_integral_norm_sq]
  have h : ‖inner ℂ f g‖ ≤ ‖f‖*‖g‖ := norm_inner_le_norm f g
  have hi : inner ℂ f g = ∫ x, star (f x) * g x ∂μ := by
    rw [L2.inner_def]
    simp only [RCLike.inner_apply']
    rfl
  rw [hi] at h
  calc
    ‖∫ x, star (f x) * g x ∂μ‖^2 ≤ (‖f‖*‖g‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ‖f‖^2 * ‖g‖^2 := by rw [mul_pow]

end Sechstmoment
