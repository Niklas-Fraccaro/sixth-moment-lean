import Mathlib.Analysis.Calculus.MeanValue
import Sechstmoment.Numerator.V.Contour.AlmostHolomorphicWeight


namespace Sechstmoment.Source
open Complex Real Set MeasureTheory
open scoped ContDiff
noncomputable section

theorem smooth_dyadic_weight_translate_zero {w : ℝ → ℂ}
    (hws : tsupport w ⊆ Icc (1:ℝ) 2) {T q v : ℝ}
    (hT : 0 < T) (hq : |q| ≤ T/2) (hv : v ∉ Icc (T/2) (3*T)) :
    w ((v+q)/T) = 0 := by
  apply Function.notMem_support.mp
  intro hm
  have H := hws (subset_tsupport w hm)
  have hlow := (le_div_iff₀ hT).mp H.1
  have hupp := (div_le_iff₀ hT).mp H.2
  have hq' := abs_le.mp hq
  exact hv ⟨by linarith [hq'.2],by linarith [hq'.1]⟩

theorem smooth_compact_weight_translation_bound {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2) :
    ∃ D : ℝ, 0 < D ∧ ∀ T : ℝ, 0 < T → ∀ q v : ℝ,
      ‖w ((v+q)/T)-w (v/T)‖ ≤ D*|q|/T := by
  obtain ⟨D,hD,hbound⟩ := smooth_compact_weight_derivative_bound hw hws 1
  refine ⟨D,hD,?_⟩
  intro T hT q v
  have H := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x (_ : x ∈ (univ : Set ℝ)) => (hw.differentiable (by simp)).differentiableAt)
    (fun x (_ : x ∈ (univ : Set ℝ)) => by simpa only [iteratedDeriv_one] using hbound x)
    (convex_univ : Convex ℝ (univ : Set ℝ)) (mem_univ (v/T)) (mem_univ ((v+q)/T))
  have he : (v+q)/T-v/T = q/T := by ring
  simpa only [he,Real.norm_eq_abs,abs_div,abs_of_pos hT,mul_div_assoc] using H

theorem smooth_compact_weight_integrated_translation {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ q : ℝ, |q| ≤ T/2 →
      ∀ F : ℝ → ℂ, AEStronglyMeasurable F volume → ∀ M : ℝ, 0 ≤ M →
      (∀ v ∈ Icc (T/2) (3*T), ‖F v‖ ≤ M) →
      ‖(∫ v : ℝ, F v*w ((v+q)/T))-(∫ v : ℝ, F v*w (v/T))‖ ≤ C*M*|q| := by
  obtain ⟨D,hD,hdelta⟩ := smooth_compact_weight_translation_bound hw hws
  obtain ⟨B,hB,hbound⟩ := smooth_compact_weight_derivative_bound hw hws 0
  have hB' (x : ℝ) : ‖w x‖ ≤ B := by simpa only [iteratedDeriv_zero] using hbound x
  refine ⟨3*D,by positivity,?_⟩
  intro T hT q hq F hF M hM hnorm
  have hT0 : 0 < T := by linarith
  have horder : T/2 ≤ 3*T := by linarith
  let S := Icc (T/2) (3*T)
  have hi (a : ℝ) : IntegrableOn (fun v : ℝ => F v*w ((v+a)/T)) S := by
    have hiconst : IntegrableOn (fun _ : ℝ => M*B) S :=
      (continuous_const : Continuous (fun _ : ℝ => M*B)).continuousOn.integrableOn_Icc
    apply hiconst.mono'
      ((hF.mul (hw.continuous.comp (by fun_prop)).aestronglyMeasurable).restrict)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    change ‖F v*w ((v+a)/T)‖ ≤ M*B
    rw [norm_mul]
    exact mul_le_mul (hnorm v hv) (hB' _) (norm_nonneg _) hM
  have hi0 : IntegrableOn (fun v : ℝ => F v*w (v/T)) S := by
    simpa only [add_zero] using hi 0
  have heq (a : ℝ) (ha : |a| ≤ T/2) :
      (∫ v in S, F v*w ((v+a)/T)) = ∫ v : ℝ, F v*w ((v+a)/T) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    rw [smooth_dyadic_weight_translate_zero hws hT0 ha hv,mul_zero]
  have heq0 : (∫ v in S, F v*w (v/T)) = ∫ v : ℝ, F v*w (v/T) := by
    simpa only [add_zero] using heq 0 (by rw [abs_zero]; positivity)
  rw [← heq q hq,← heq0,← integral_sub (hi q) hi0]
  have H := norm_setIntegral_le_of_norm_le_const
    (f := fun v : ℝ => F v*w ((v+q)/T)-F v*w (v/T))
    (C := M*(D*|q|/T)) (μ := volume) (s := S) measure_Icc_lt_top
    (fun v hv => by
      rw [← mul_sub,norm_mul]
      exact mul_le_mul (hnorm v hv) (hdelta T hT0 q v) (norm_nonneg _) hM)
  apply H.trans
  dsimp only [S]
  rw [Real.volume_real_Icc_of_le horder]
  have he : M*(D*|q|/T)*(3*T-T/2) = (5/2:ℝ)*D*M*|q| := by
    field_simp [hT0.ne']
    ring
  rw [he]
  nlinarith [mul_nonneg (mul_nonneg hD.le hM) (abs_nonneg q)]

end
end Sechstmoment.Source
