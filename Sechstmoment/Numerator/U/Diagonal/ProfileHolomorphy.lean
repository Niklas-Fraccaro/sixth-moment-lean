import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Sechstmoment.Analysis.Mellin.ProfileInversion

/-! Genuine entire continuation of the actual compactly supported profile transform. -/

namespace Sechstmoment
open Complex Real MeasureTheory Set Filter Metric
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 0

theorem profileLaplaceTransform_hasDerivAt {f : ℝ → ℂ}
    (hf : HasCompactSupport f) (hc : Continuous f) (w₀ : ℂ) :
    HasDerivAt (profileLaplaceTransform f)
      (∫ x : ℝ, Complex.exp (w₀*(x:ℂ))*(x:ℂ)*f x) w₀ := by
  obtain ⟨A,hA⟩ := (show IsCompact (tsupport f) from hf).isBounded.exists_norm_le
  let B : ℝ := max A 1
  have hB : 0 ≤ B := by dsimp [B]; exact (by norm_num : (0:ℝ) ≤ 1).trans (le_max_right _ _)
  have hBx (x : ℝ) (hx : f x ≠ 0) : ‖x‖ ≤ B :=
    (hA x (subset_tsupport f hx)).trans (le_max_left _ _)
  let F : ℂ → ℝ → ℂ := fun w x => Complex.exp (w*(x:ℂ))*f x
  let D : ℂ → ℝ → ℂ := fun w x => Complex.exp (w*(x:ℂ))*(x:ℂ)*f x
  let M : ℝ := Real.exp ((‖w₀‖+1)*B)*B
  have hFc (w : ℂ) : Continuous (F w) := by dsimp [F]; fun_prop
  have hDc (w : ℂ) : Continuous (D w) := by dsimp [D]; fun_prop
  have hFi : Integrable (F w₀) := (hFc w₀).integrable_of_hasCompactSupport hf.mul_left
  have hnorm : ∀ x : ℝ, ∀ w ∈ ball w₀ 1, ‖D w x‖ ≤ M*‖f x‖ := by
    intro x w hw
    by_cases hx : f x=0
    · simp [D,hx]
    · have hwr : ‖w‖ ≤ ‖w₀‖+1 := by
        have hd : ‖w-w₀‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hw
        have hn : ‖w‖ ≤ ‖w-w₀‖+‖w₀‖ := by
          simpa only [sub_add_cancel] using norm_add_le (w-w₀) w₀
        linarith
      have he : (w*(x:ℂ)).re ≤ (‖w₀‖+1)*B := by
        calc
          _ ≤ ‖w*(x:ℂ)‖ := Complex.re_le_norm _
          _ = ‖w‖*‖x‖ := by rw [norm_mul,Complex.norm_real]
          _ ≤ (‖w₀‖+1)*B := mul_le_mul hwr (hBx x hx) (norm_nonneg _) (by positivity)
      dsimp [D,M]
      rw [norm_mul,norm_mul,Complex.norm_exp,Complex.norm_real]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (Real.exp_le_exp.mpr he) (hBx x hx) (norm_nonneg _) (Real.exp_pos _).le)
        (norm_nonneg _)
  have hd : ∀ x : ℝ, ∀ w ∈ ball w₀ 1, HasDerivAt (fun z => F z x) (D w x) w := by
    intro x w hw
    dsimp [F,D]
    simpa only [one_mul,Function.comp_apply,id_eq] using!
      ((Complex.hasDerivAt_exp (w*(x:ℂ))).comp w ((hasDerivAt_id w).mul_const (x:ℂ))).mul_const (f x)
  have H := hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds w₀ (by norm_num : (0:ℝ)<1))
    (Eventually.of_forall (fun w => (hFc w).aestronglyMeasurable)) hFi (hDc w₀).aestronglyMeasurable
    (Eventually.of_forall hnorm) ((hc.integrable_of_hasCompactSupport hf).norm.const_mul M)
    (Eventually.of_forall hd)
  exact H.2

theorem profileLaplaceTransform_differentiable {f : ℝ → ℂ}
    (hf : HasCompactSupport f) (hc : Continuous f) : Differentiable ℂ (profileLaplaceTransform f) :=
  fun w => (profileLaplaceTransform_hasDerivAt hf hc w).differentiableAt

theorem profileLaplaceTransform_entire {f : ℝ → ℂ}
    (hf : HasCompactSupport f) (hc : Continuous f) :
    AnalyticOnNhd ℂ (profileLaplaceTransform f) univ :=
  Complex.analyticOnNhd_univ_iff_differentiable.mpr (profileLaplaceTransform_differentiable hf hc)

end
end Sechstmoment
