import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Sechstmoment.Analysis.Mellin.SmoothMellinInversion

/-! Absolutely convergent series may be inserted into the literal smooth
Mellin inversion formula. The only series hypothesis is its ordinary absolute
convergence on the starting line. -/

namespace Sechstmoment.Source
open Complex Real MeasureTheory Set
open scoped Topology ContDiff BigOperators
noncomputable section

theorem smooth_mellin_series_inversion {ι : Type*} [Countable ι]
    {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    (κ : ℝ) (a : ι → ℂ) (r : ι → ℝ) (hr : ∀ n, 0 < r n)
    (hs : Summable (fun n => ‖a n‖*(r n)^(-κ))) :
    HasSum (fun n => a n*w (r n))
      ((1/(2*Real.pi):ℂ)*
        (∫ v : ℝ, mellin w ((κ:ℂ)+(v:ℂ)*I)*
          (∑' n, a n*(r n:ℂ)^(-((κ:ℂ)+(v:ℂ)*I))))) := by
  let M := fun v : ℝ => mellin w ((κ:ℂ)+(v:ℂ)*I)
  let A := fun n => ‖a n‖*(r n)^(-κ)
  let F := fun (n : ι) (v : ℝ) => a n*(r n:ℂ)^(-((κ:ℂ)+(v:ℂ)*I))*M v
  have hM : Integrable M := smooth_dyadic_mellin_vertical_integrable hw hws κ
  have hMc : Continuous M := smooth_mellin_line_continuous hw hws κ
  have hFn (n : ι) (v : ℝ) : ‖F n v‖ = A n*‖M v‖ := by
    dsimp only [F,A]
    rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hr n)]
    simp only [neg_re,add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero]
  have hFc (n : ι) : Continuous (F n) := by
    have hp : Continuous (fun v : ℝ => (r n:ℂ)^(-((κ:ℂ)+(v:ℂ)*I))) := by
      apply Continuous.const_cpow (by fun_prop)
      exact Or.inl (Complex.ofReal_ne_zero.mpr (hr n).ne')
    exact (continuous_const.mul hp).mul hMc
  have hFi (n : ι) : Integrable (F n) := by
    apply (hM.norm.const_mul (A n)).mono' (hFc n).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun v => le_of_eq (hFn n v))
  have hFs : Summable (fun n => ∫ v : ℝ, ‖F n v‖) := by
    have heq (n : ι) : (∫ v : ℝ, ‖F n v‖) = A n*(∫ v : ℝ, ‖M v‖) := by
      simp_rw [hFn]
      exact integral_const_mul _ _
    simp_rw [heq]
    exact hs.mul_right _
  have hterm (n : ι) :
      (1/(2*Real.pi):ℂ)*(∫ v : ℝ, F n v) = a n*w (r n) := by
    have heq : F n = fun v : ℝ => a n*(M v*(r n:ℂ)^(-((κ:ℂ)+(v:ℂ)*I))) := by
      funext v
      dsimp only [F]
      ring
    rw [heq,integral_const_mul]
    calc
      _ = a n*((1/(2*Real.pi):ℂ)*
          (∫ v : ℝ, M v*(r n:ℂ)^(-((κ:ℂ)+(v:ℂ)*I)))) := by ring
      _ = _ := by rw [smooth_dyadic_mellin_inversion_integral hw hws κ (hr n)]
  have heq (v : ℝ) : (∑' n, F n v) =
      M v*(∑' n, a n*(r n:ℂ)^(-((κ:ℂ)+(v:ℂ)*I))) := by
    dsimp only [F]
    rw [tsum_mul_right]
    ring
  have H := (hasSum_integral_of_summable_integral_norm hFi hFs).mul_left
    (1/(2*Real.pi):ℂ)
  simpa only [hterm,heq] using H

theorem smooth_mellin_series_inversion_eq {ι : Type*} [Countable ι]
    {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    (κ : ℝ) (a : ι → ℂ) (r : ι → ℝ) (hr : ∀ n, 0 < r n)
    (hs : Summable (fun n => ‖a n‖*(r n)^(-κ))) :
    (∑' n, a n*w (r n)) = (1/(2*Real.pi):ℂ)*
      (∫ v : ℝ, mellin w ((κ:ℂ)+(v:ℂ)*I)*
        (∑' n, a n*(r n:ℂ)^(-((κ:ℂ)+(v:ℂ)*I)))) :=
  (smooth_mellin_series_inversion hw hws κ a r hr hs).tsum_eq

theorem smooth_mellin_dirichlet_inversion {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    (κ : ℝ) (a : ℕ+ → ℂ) {x : ℝ} (hx : 0 < x)
    (hs : Summable (fun n => ‖a n‖*(n:ℝ)^(-κ))) :
    (∑' n : ℕ+, a n*w ((n:ℝ)/x)) = (1/(2*Real.pi):ℂ)*
      (∫ v : ℝ, mellin w ((κ:ℂ)+(v:ℂ)*I)*(x:ℂ)^((κ:ℂ)+(v:ℂ)*I)*
        (∑' n : ℕ+, a n*(n:ℂ)^(-((κ:ℂ)+(v:ℂ)*I)))) := by
  have hn (n : ℕ+) : 0 < (n:ℝ) := by exact_mod_cast n.pos
  have hsum : Summable (fun n : ℕ+ => ‖a n‖*((n:ℝ)/x)^(-κ)) := by
    apply (hs.mul_right (x^κ)).congr
    intro n
    rw [Real.div_rpow (hn n).le hx.le,Real.rpow_neg hx.le,div_inv_eq_mul]
    ring
  have hp (v : ℝ) :
      (∑' n : ℕ+, a n*(((n:ℝ)/x:ℝ):ℂ)^(-((κ:ℂ)+(v:ℂ)*I))) =
        (x:ℂ)^((κ:ℂ)+(v:ℂ)*I)*
          (∑' n : ℕ+, a n*(n:ℂ)^(-((κ:ℂ)+(v:ℂ)*I))) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg (hn n).le hx.le,
      Complex.cpow_neg (x:ℂ),div_inv_eq_mul]
    norm_cast
    ring
  have H := smooth_mellin_series_inversion_eq hw hws κ a
    (fun n : ℕ+ => (n:ℝ)/x) (fun n => div_pos (hn n) hx) hsum
  simpa only [hp,mul_assoc] using H

end
end Sechstmoment.Source
