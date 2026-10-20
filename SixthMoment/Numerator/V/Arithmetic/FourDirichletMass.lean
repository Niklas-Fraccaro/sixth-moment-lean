import SixthMoment.Arithmetic.Euler.FourL.FourCoefficients
import SixthMoment.Numerator.V.Arithmetic.StartingLine
import SixthMoment.Zeta.DirichletL.AbsoluteMass


namespace SixthMoment.Source
open Complex Real Set
open NoDPGlobalConvolution NoDPGlobalLFactorization
open scoped BigOperators LSeries.notation
noncomputable section

theorem powerAF_absolute_mass {a : ℂ} {c : ℝ} (hc : 1 < c+a.re) :
    (∑' n : ℕ, ‖LSeries.term (powerAF a) (c:ℂ) n‖) =
      zetaDirichletMajorant (c+a.re) := by
  unfold zetaDirichletMajorant
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    rw [LSeries.term_zero,norm_zero,Nat.cast_zero,
      Real.zero_rpow (by linarith : c+a.re ≠ 0),div_zero]
  · have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [LSeries.term_def₀ ArithmeticFunction.map_zero,powerAF_apply a n hn,norm_mul]
    rw [show (n:ℂ) = ((n:ℝ):ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hn0,
      Complex.norm_cpow_eq_rpow_re_of_pos hn0]
    simp only [neg_re,ofReal_re]
    rw [← Real.rpow_add hn0,show -a.re+(-c) = -(c+a.re) by ring,
      Real.rpow_neg hn0.le,one_div]

theorem arithmeticFunction_absolute_mass_mul_le {f g : ArithmeticFunction ℂ} {c : ℝ}
    (hf : LSeriesSummable f (c:ℂ)) (hg : LSeriesSummable g (c:ℂ)) :
    (∑' n : ℕ, ‖LSeries.term ((f*g:ArithmeticFunction ℂ):ℕ → ℂ) (c:ℂ) n‖) ≤
      (∑' n : ℕ, ‖LSeries.term f (c:ℂ) n‖)*
        (∑' n : ℕ, ‖LSeries.term g (c:ℂ) n‖) := by
  rw [← ArithmeticFunction.coe_mul]
  exact dirichlet_convolution_absolute_mass_le hf hg

theorem fourAF_absolute_mass_le {β : Fin 4 → ℂ} {c : ℝ}
    (hc : ∀ j, 1 < c+(β j).re) :
    (∑' n : ℕ, ‖LSeries.term (fourAF β) (c:ℂ) n‖) ≤
      ∏ j : Fin 4, zetaDirichletMajorant (c+(β j).re) := by
  have hs (j : Fin 4) : LSeriesSummable (powerAF (β j)) (c:ℂ) :=
    (powerAF_hasSum (β j) (c:ℂ) (by simpa only [add_re,ofReal_re] using hc j)).LSeriesSummable
  have h23 := arithmeticFunction_absolute_mass_mul_le (hs 2) (hs 3)
  have h123 := arithmeticFunction_absolute_mass_mul_le (hs 1)
    (ArithmeticFunction.LSeriesSummable_mul (hs 2) (hs 3))
  have h0123 := arithmeticFunction_absolute_mass_mul_le (hs 0)
    (ArithmeticFunction.LSeriesSummable_mul (hs 1)
      (ArithmeticFunction.LSeriesSummable_mul (hs 2) (hs 3)))
  unfold fourAF
  apply h0123.trans
  rw [powerAF_absolute_mass (hc 0)]
  calc
    _ ≤ zetaDirichletMajorant (c+(β 0).re)*
        ((∑' n : ℕ, ‖LSeries.term (powerAF (β 1)) (c:ℂ) n‖)*
          (∑' n : ℕ, ‖LSeries.term
            ((powerAF (β 2)*powerAF (β 3):ArithmeticFunction ℂ):ℕ → ℂ) (c:ℂ) n‖)) :=
      mul_le_mul_of_nonneg_left h123 (zetaDirichletMajorant_nonneg _)
    _ ≤ zetaDirichletMajorant (c+(β 0).re)*
        ((∑' n : ℕ, ‖LSeries.term (powerAF (β 1)) (c:ℂ) n‖)*
          ((∑' n : ℕ, ‖LSeries.term (powerAF (β 2)) (c:ℂ) n‖)*
            (∑' n : ℕ, ‖LSeries.term (powerAF (β 3)) (c:ℂ) n‖))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left h23 (tsum_nonneg (fun _ => norm_nonneg _)))
        (zetaDirichletMajorant_nonneg _)
    _ = _ := by
      rw [powerAF_absolute_mass (hc 1),powerAF_absolute_mass (hc 2),powerAF_absolute_mass (hc 3)]
      simp only [Fin.prod_univ_four]
      ring

theorem fourAF_log_line_absolute_mass_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T R : ℝ, 1 ≤ Real.log T →
      ∀ β : Fin 4 → ℂ, (∀ j, ‖β j‖ ≤ R/Real.log T) →
      (∑' n : ℕ, ‖LSeries.term (fourAF β) (noDPRightLine T R:ℂ) n‖) ≤
        C*(Real.log T)^4 := by
  obtain ⟨C,hC,hzeta⟩ := riemannZeta_log_line_bound
  refine ⟨C^4,by positivity,?_⟩
  intro T R hL β hβ
  have hL0 : 0 < Real.log T := by linarith
  have hgap (j : Fin 4) : 1+1/Real.log T ≤ noDPRightLine T R+(β j).re := by
    simpa using noDPRightLine_shift_lower hL (hβ j) 0
  have hc (j : Fin 4) : 1 < noDPRightLine T R+(β j).re :=
    lt_of_lt_of_le (by linarith [one_div_pos.mpr hL0]) (hgap j)
  apply (fourAF_absolute_mass_le hc).trans
  calc
    _ ≤ ∏ _j : Fin 4, C*Real.log T := by
      apply Finset.prod_le_prod₀ (fun j _ => zetaDirichletMajorant_nonneg _)
      intro j _
      rw [← riemannZeta_real_norm (hc j)]
      exact hzeta (Real.log T) hL _ (by simpa only [ofReal_re] using hgap j)
    _ = _ := by simp; ring

end
end SixthMoment.Source
