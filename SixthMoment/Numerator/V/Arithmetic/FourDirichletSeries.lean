import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import SixthMoment.Numerator.V.Arithmetic.FourDirichletMass


namespace SixthMoment.Source
open Complex Real Set
open NoDPGlobalConvolution NoDPGlobalLFactorization
open scoped BigOperators
noncomputable section

theorem fourAF_hasSum (β : Fin 4 → ℂ) (s : ℂ)
    (hs : ∀ j, 1 < (s+β j).re) :
    LSeriesHasSum (fourAF β) s (∏ j : Fin 4, riemannZeta (s+β j)) := by
  have H := ArithmeticFunction.LSeriesHasSum_mul (powerAF_hasSum (β 0) s (hs 0))
    (ArithmeticFunction.LSeriesHasSum_mul (powerAF_hasSum (β 1) s (hs 1))
      (ArithmeticFunction.LSeriesHasSum_mul (powerAF_hasSum (β 2) s (hs 2))
        (powerAF_hasSum (β 3) s (hs 3))))
  simpa only [fourAF,Fin.prod_univ_four,mul_assoc] using! H

theorem fourAF_dirichlet_hasSum (β : Fin 4 → ℂ) (s : ℂ)
    (hs : ∀ j, 1 < (s+β j).re) :
    HasSum (fun m : ℕ+ => fourAF β m*(m:ℂ)^(-s))
      (∏ j : Fin 4, riemannZeta (s+β j)) := by
  have H := fourAF_hasSum β s hs
  change HasSum (LSeries.term (fourAF β) s) _ at H
  have Hpos : HasSum (fun m : ℕ+ => LSeries.term (fourAF β) s m)
      (∏ j : Fin 4, riemannZeta (s+β j)) :=
    hasSum_pnat_iff.mpr (by simpa only [LSeries.term_zero,add_zero] using H)
  simpa only [LSeries.term_def₀ ArithmeticFunction.map_zero] using Hpos

theorem fourAF_dirichlet_absolute {β : Fin 4 → ℂ} {c : ℝ}
    (hc : ∀ j, 1 < c+(β j).re) :
    Summable (fun m : ℕ+ => ‖fourAF β m‖*(m:ℝ)^(-c)) := by
  have H := (fourAF_hasSum β (c:ℂ) (by simpa only [add_re,ofReal_re] using hc)).LSeriesSummable.norm
  have Hpos := summable_pnat_iff_summable_nat.mpr H
  apply Hpos.congr
  intro m
  rw [LSeries.term_def₀ ArithmeticFunction.map_zero,norm_mul]
  have hm : 0 < (m:ℝ) := by exact_mod_cast m.pos
  rw [show (m:ℂ) = ((m:ℝ):ℂ) by simp,Complex.norm_cpow_eq_rpow_re_of_pos hm]
  simp

end
end SixthMoment.Source
