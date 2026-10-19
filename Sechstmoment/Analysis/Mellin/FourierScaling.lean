import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! Exact positive real Fourier scaling, retaining the Jacobian. -/

namespace Sechstmoment.Source
open Complex Real MeasureTheory
open scoped FourierTransform
noncomputable section

theorem fourier_positive_scale (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) (y : ℝ) :
    𝓕 (fun x : ℝ => (a:ℂ)*f (a*x)) y = 𝓕 f (y/a) := by
  let g : ℝ → ℂ := fun u => Complex.exp (((-2*Real.pi*(u*(y/a)):ℝ):ℂ)*I)*f u
  have hscale := Measure.integral_comp_mul_left g a
  rw [Real.fourier_eq',Real.fourier_eq']
  simp only [Real.inner_apply,smul_eq_mul]
  calc
    _ = (a:ℂ)*(∫ x : ℝ, g (a*x)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      have he : -2*Real.pi*(x*y) = -2*Real.pi*((a*x)*(y/a)) := by
        field_simp [ha.ne']
      change Complex.exp (((-2*Real.pi*(x*y):ℝ):ℂ)*I)*((a:ℂ)*f (a*x)) = _
      unfold g
      rw [he]
      ring
    _ = (a:ℂ)*(|a⁻¹| • ∫ u : ℝ, g u) := congrArg (fun z : ℂ => (a:ℂ)*z) hscale
    _ = _ := by
      simp [g,abs_of_pos (inv_pos.mpr ha),RCLike.real_smul_eq_coe_mul,ha.ne',mul_assoc]

end
end Sechstmoment.Source
