import Sechstmoment.Numerator.V.Arithmetic.FourDirichletSeries
import Sechstmoment.Numerator.V.Chi.SeriesInsertion
import Sechstmoment.Numerator.V.Chi.ShiftedIntegrability

/-! Exact Dirichlet insertion for the actual shifted four-zeta chi integral. -/

namespace Sechstmoment.Source
open Complex Real Set MeasureTheory
open NoDPGlobalLFactorization
open scoped BigOperators
noncomputable section

theorem four_zeta_chi_time_series_insertion {w : ℝ → ℂ}
    (hw : Continuous w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {T c N : ℝ} {u : ℂ} {β : Fin 4 → ℂ} (hT : 1 ≤ T) (hN : 0 < N)
    (hc : c-u.re ∈ Icc (1/8:ℝ) (15/8)) (hu : |u.im| ≤ T/2)
    (hβ : ∀ j, 1 < c+(β j).re) :
    HasSum (fun m : ℕ+ => fourAF β m*noDPChiTimeTransform w T c u ((m:ℝ)/N))
      ((1/(2*Real.pi):ℂ)*(∫ t : ℝ,
        (zetaChi (1-((c:ℂ)+(t:ℂ)*I)+u)*w (t/T))*
          ((N:ℂ)^((c:ℂ)+(t:ℂ)*I)*
            ∏ j : Fin 4, riemannZeta ((c:ℂ)+(t:ℂ)*I+β j)))) := by
  have hm (m : ℕ+) : 0 < (m:ℝ) := by exact_mod_cast m.pos
  have hs : Summable (fun m : ℕ+ => ‖fourAF β m‖*((m:ℝ)/N)^(-c)) := by
    apply ((fourAF_dirichlet_absolute hβ).mul_right (N^c)).congr
    intro m
    rw [Real.div_rpow (hm m).le hN.le,Real.rpow_neg hN.le,div_inv_eq_mul]
    ring
  have hp (t : ℝ) :
      (∑' m : ℕ+, fourAF β m*(((m:ℝ)/N:ℝ):ℂ)^(-((c:ℂ)+(t:ℂ)*I))) =
        (N:ℂ)^((c:ℂ)+(t:ℂ)*I)*
          ∏ j : Fin 4, riemannZeta ((c:ℂ)+(t:ℂ)*I+β j) := by
    calc
      _ = (N:ℂ)^((c:ℂ)+(t:ℂ)*I)*
          (∑' m : ℕ+, fourAF β m*(m:ℂ)^(-((c:ℂ)+(t:ℂ)*I))) := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro m
        rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg (hm m).le hN.le,
          Complex.cpow_neg (N:ℂ),div_inv_eq_mul]
        norm_cast
        ring
      _ = _ := by
        rw [(fourAF_dirichlet_hasSum β ((c:ℂ)+(t:ℂ)*I) (by
          intro j
          simpa only [add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero] using hβ j)).tsum_eq]
  have H := chi_time_series_insertion w T c u (fun m : ℕ+ => fourAF β m)
    (fun m : ℕ+ => (m:ℝ)/N) (fun m => div_pos (hm m) hN)
    (chi_shift_compact_time_weight_integrable hw hws hT hc hu) hs
  simpa only [hp] using H

end
end Sechstmoment.Source
