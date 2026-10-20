import Mathlib.NumberTheory.LSeries.Dirichlet
import SixthMoment.Zeta.Bounds.MellinZetaDirichletBounds


namespace SixthMoment
open Real Complex ArithmeticFunction
open scoped BigOperators LSeries.notation ArithmeticFunction.Moebius
noncomputable section

theorem riemannZeta_inv_eq_moebius_series {s : ℂ} (hs : 1<s.re) :
    (riemannZeta s)⁻¹=LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s := by
  have h := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at h
  exact inv_eq_of_mul_eq_one_right h

theorem riemannZeta_inv_norm_le_dirichlet {s : ℂ} {b : ℝ}
    (hb : 1<b) (hs : b≤s.re) :
    ‖(riemannZeta s)⁻¹‖≤zetaDirichletMajorant b := by
  rw [riemannZeta_inv_eq_moebius_series (hb.trans_le hs),LSeries]
  apply tsum_of_norm_bounded (Real.summable_one_div_nat_rpow.mpr hb).hasSum
  intro n
  by_cases hn : n=0
  · subst n
    simp only [LSeries.term_zero,norm_zero]
    positivity
  · have hnpos : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [LSeries.term_of_ne_zero hn,norm_div]
    have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖≤1 := by
      norm_cast
      exact ArithmeticFunction.abs_moebius_le_one
    calc
      _ ≤ 1/‖(n:ℂ)^s‖ := by gcongr
      _ = 1/(n:ℝ)^s.re := by
        rw [show (n:ℂ)=((n:ℝ):ℂ) by simp,
          Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
      _ ≤ 1/(n:ℝ)^b := by
        apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos hnpos b)
        exact Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn) hs

end
end SixthMoment
