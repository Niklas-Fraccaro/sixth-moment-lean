import Sechstmoment.Numerator.V.Arithmetic.FourDirichletSeries

/-! Positive-index and rescaled absolute mass for the literal fourfold
Dirichlet coefficients on the common logarithmic line. -/

namespace Sechstmoment.Source
open Complex Real
open NoDPGlobalLFactorization
noncomputable section
set_option maxHeartbeats 1000000

theorem fourAF_dirichlet_absolute_mass_eq {β : Fin 4 → ℂ} {c : ℝ} :
    (∑' m : ℕ+, ‖fourAF β m‖*(m:ℝ)^(-c)) =
      ∑' n : ℕ, ‖LSeries.term (fourAF β) (c:ℂ) n‖ := by
  calc
    _ = ∑' m : ℕ+, ‖LSeries.term (fourAF β) (c:ℂ) m‖ := by
      apply tsum_congr
      intro m
      have hm : 0 < (m:ℝ) := by exact_mod_cast m.pos
      rw [LSeries.norm_term_eq,ite_eq_right (Nat.ne_of_gt m.pos),ofReal_re,
        Real.rpow_neg hm.le,div_eq_mul_inv]
    _ = _ := tsum_pnat_eq_tsum_of_eq_zero
      (f := fun n : ℕ => ‖LSeries.term (fourAF β) (c:ℂ) n‖)
      (by rw [LSeries.term_zero,norm_zero])

theorem fourAF_scaled_log_line_absolute_mass_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T R : ℝ, 1 ≤ Real.log T →
      ∀ β : Fin 4 → ℂ, (∀ j, ‖β j‖ ≤ R/Real.log T) → ∀ N : ℝ, 0 < N →
      Summable (fun m : ℕ+ => ‖fourAF β m‖*((m:ℝ)/N)^(-noDPRightLine T R)) ∧
      (∑' m : ℕ+, ‖fourAF β m‖*((m:ℝ)/N)^(-noDPRightLine T R)) ≤
        C*N^(noDPRightLine T R)*(Real.log T)^4 := by
  obtain ⟨C,hC,hbound⟩ := fourAF_log_line_absolute_mass_bound
  refine ⟨C,hC,?_⟩
  intro T R hL β hβ N hN
  have hL0 : 0 < Real.log T := by linarith
  have hgap (j : Fin 4) : 1+1/Real.log T ≤ noDPRightLine T R+(β j).re := by
    simpa using noDPRightLine_shift_lower hL (hβ j) 0
  have hc (j : Fin 4) : 1 < noDPRightLine T R+(β j).re :=
    lt_of_lt_of_le (by linarith [one_div_pos.mpr hL0]) (hgap j)
  have hs := fourAF_dirichlet_absolute hc
  have he (m : ℕ+) :
      ‖fourAF β m‖*((m:ℝ)/N)^(-noDPRightLine T R) =
        N^(noDPRightLine T R)*(‖fourAF β m‖*(m:ℝ)^(-noDPRightLine T R)) := by
    have hm : 0 < (m:ℝ) := by exact_mod_cast m.pos
    rw [Real.div_rpow hm.le hN.le,Real.rpow_neg hN.le,div_inv_eq_mul]
    ring
  refine ⟨(hs.mul_left _).congr (fun m => (he m).symm),?_⟩
  simp_rw [he]
  rw [tsum_mul_left,fourAF_dirichlet_absolute_mass_eq]
  have H := mul_le_mul_of_nonneg_left (hbound T R hL β hβ)
    (Real.rpow_nonneg hN.le (noDPRightLine T R))
  convert H using 1
  ring

end
end Sechstmoment.Source
