import Mathlib.Analysis.PSeries
import Mathlib.Tactic
import Sechstmoment.Zeta.Regularized


namespace Sechstmoment

open Real Complex
open scoped BigOperators

noncomputable section

def zetaDirichletMajorant (b : ℝ) : ℝ := ∑' n : ℕ, 1/(n:ℝ)^b

theorem zetaDirichletMajorant_nonneg (b : ℝ) : 0 ≤ zetaDirichletMajorant b := by
  apply tsum_nonneg
  intro n
  exact one_div_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg _) b)

theorem riemannZeta_norm_le_dirichlet {s : ℂ} {b : ℝ} (hb : 1 < b) (hs : b ≤ s.re) :
    ‖riemannZeta s‖ ≤ zetaDirichletMajorant b := by
  rw [zeta_eq_tsum_one_div_nat_cpow (hb.trans_le hs)]
  apply tsum_of_norm_bounded (Real.summable_one_div_nat_rpow.mpr hb).hasSum
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, Complex.zero_cpow (Complex.ne_zero_of_one_lt_re (hb.trans_le hs)),
      div_zero, norm_zero]
    positivity
  · have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [norm_div, norm_one]
    rw [show (n:ℂ) = ((n:ℝ):ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
    apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos hnpos b)
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn) hs

theorem finiteRiemannZetaProduct_norm_le_dirichlet {ι : Type*}
    (s : Finset ι) (z : ι → ℂ) {b : ℝ} (hb : 1 < b) (hz : ∀ i ∈ s, b ≤ (z i).re) :
    ‖∏ i ∈ s, riemannZeta (z i)‖ ≤ (zetaDirichletMajorant b)^s.card := by
  calc
    _ ≤ ∏ i ∈ s, ‖riemannZeta (z i)‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ _i ∈ s, zetaDirichletMajorant b := by
      exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
        (fun i hi => riemannZeta_norm_le_dirichlet hb (hz i hi))
    _ = _ := by simp

end

end Sechstmoment
