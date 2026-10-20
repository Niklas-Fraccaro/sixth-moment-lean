import Mathlib.MeasureTheory.Integral.DominatedConvergence
import SixthMoment.Numerator.V.Chi.ShiftedKernel


namespace SixthMoment.Source
open Complex Real MeasureTheory
open scoped BigOperators
noncomputable section

theorem chi_time_series_insertion {ι : Type*} [Countable ι]
    (w : ℝ → ℂ) (T c : ℝ) (u : ℂ) (a : ι → ℂ) (r : ι → ℝ)
    (hr : ∀ n, 0 < r n)
    (hi : Integrable (fun t : ℝ => zetaChi (1-((c:ℂ)+(t:ℂ)*I)+u)*w (t/T)))
    (hs : Summable (fun n => ‖a n‖*(r n)^(-c))) :
    HasSum (fun n => a n*noDPChiTimeTransform w T c u (r n))
      ((1/(2*Real.pi):ℂ)*(∫ t : ℝ,
        (zetaChi (1-((c:ℂ)+(t:ℂ)*I)+u)*w (t/T))*
          (∑' n, a n*(r n:ℂ)^(-((c:ℂ)+(t:ℂ)*I))))) := by
  let M : ℝ → ℂ := fun t => zetaChi (1-((c:ℂ)+(t:ℂ)*I)+u)*w (t/T)
  let A : ι → ℝ := fun n => ‖a n‖*(r n)^(-c)
  let F : ι → ℝ → ℂ := fun n t => a n*(r n:ℂ)^(-((c:ℂ)+(t:ℂ)*I))*M t
  have hFn (n : ι) (t : ℝ) : ‖F n t‖ = A n*‖M t‖ := by
    dsimp only [F,A]
    rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hr n)]
    simp
  have hFi (n : ι) : Integrable (F n) := by
    have hp : Continuous (fun t : ℝ => (r n:ℂ)^(-((c:ℂ)+(t:ℂ)*I))) := by
      apply Continuous.const_cpow (by fun_prop)
      exact Or.inl (Complex.ofReal_ne_zero.mpr (hr n).ne')
    apply (hi.norm.const_mul (A n)).mono'
      ((continuous_const.mul hp).aestronglyMeasurable.mul hi.aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun t => le_of_eq (hFn n t))
  have hFs : Summable (fun n => ∫ t : ℝ, ‖F n t‖) := by
    have he (n : ι) : (∫ t : ℝ, ‖F n t‖) = A n*(∫ t : ℝ, ‖M t‖) := by
      simp_rw [hFn]
      exact integral_const_mul _ _
    simp_rw [he]
    exact hs.mul_right _
  have hterm (n : ι) : (1/(2*Real.pi):ℂ)*(∫ t : ℝ, F n t) =
      a n*noDPChiTimeTransform w T c u (r n) := by
    have he : F n = fun t : ℝ => a n*((r n:ℂ)^(-((c:ℂ)+(t:ℂ)*I))*
        zetaChi (1-((c:ℂ)+(t:ℂ)*I)+u)*w (t/T)) := by
      funext t
      dsimp only [F,M]
      ring
    rw [he,integral_const_mul,noDPChiTimeTransform]
    ring
  have heq (t : ℝ) : (∑' n, F n t) =
      M t*(∑' n, a n*(r n:ℂ)^(-((c:ℂ)+(t:ℂ)*I))) := by
    dsimp only [F]
    rw [tsum_mul_right]
    ring
  have H := (hasSum_integral_of_summable_integral_norm hFi hFs).mul_left (1/(2*Real.pi):ℂ)
  simpa only [hterm,heq] using H

end
end SixthMoment.Source
