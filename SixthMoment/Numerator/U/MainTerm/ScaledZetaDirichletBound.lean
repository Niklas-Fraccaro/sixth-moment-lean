import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons
import SixthMoment.Zeta.Bounds.MellinZetaDirichletBounds


namespace SixthMoment

open Real Complex MeasureTheory Set
open scoped BigOperators

noncomputable section

theorem zetaDirichletMajorant_le_one_add_inv {b : ℝ} (hb : 1 < b) :
    zetaDirichletMajorant b ≤ 1 + 1/(b-1) := by
  unfold zetaDirichletMajorant
  have hbn : 0 < b := by linarith
  have hp : -b < -1 := by linarith
  have hsum : Summable (fun n : ℕ => 1/(n:ℝ)^b) := Real.summable_one_div_nat_rpow.mpr hb
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-b)) (Ici (1:ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : -b ≤ 0)).mono
      (fun x hx => zero_lt_one.trans_le (mem_Ici.mp hx))
  have htail := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x^(-b)) 1 (by simpa using hanti)
    (integrableOn_Ioi_rpow_of_lt hp (by norm_num : 0 < ((1:ℕ):ℝ)))
    (fun x hx => Real.rpow_nonneg (by linarith [mem_Ioi.mp hx]) _)
  have hint : (∫ x : ℝ in Ioi 1, x ^ (-b)) = 1/(b-1) := by
    rw [integral_Ioi_rpow_of_lt hp zero_lt_one, Real.one_rpow]
    field_simp [show b - 1 ≠ 0 by linarith, show -b + 1 ≠ 0 by linarith]
    ring
  norm_num only [Nat.cast_one] at htail
  rw [hint] at htail
  have hdecomp := hsum.sum_add_tsum_nat_add 2
  have hpoint : ∀ n : ℕ, 1/(n:ℝ)^b = (n:ℝ)^(-b) := by
    intro n
    rw [Real.rpow_neg (Nat.cast_nonneg _), one_div]
  simp only [hpoint] at hdecomp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Real.zero_rpow (neg_ne_zero.mpr hbn.ne'), Real.one_rpow,
    zero_add] at hdecomp
  have ht : (∑' n : ℕ, ((n+2:ℕ):ℝ)^(-b)) ≤ 1/(b-1) := by
    simpa only [Nat.add_assoc, Nat.add_one] using htail
  simp_rw [hpoint]
  rw [← hdecomp]
  linarith

theorem scaled_riemannZeta_norm_le {L r : ℝ} {w : ℂ}
    (hL : 1 ≤ L) (hr : 0 < r) (hw : r ≤ w.re) :
    ‖riemannZeta (1 + w / (L:ℂ)) / (L:ℂ)‖ ≤ 1 + 1/r := by
  have hLpos : 0 < L := by linarith
  have hb : 1 < 1 + r/L := by linarith [div_pos hr hLpos]
  have hs : 1 + r/L ≤ (1+w/(L:ℂ)).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.div_ofReal_re]
    exact add_le_add_right (div_le_div_of_nonneg_right hw hLpos.le) 1
  have hz : ‖riemannZeta (1+w/(L:ℂ))‖ ≤ 1 + L/r := by
    calc
      _ ≤ zetaDirichletMajorant (1+r/L) := riemannZeta_norm_le_dirichlet hb hs
      _ ≤ 1 + 1/((1+r/L)-1) := zetaDirichletMajorant_le_one_add_inv hb
      _ = 1+L/r := by
        rw [show 1 + r/L - 1 = r/L by ring]
        field_simp
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hLpos.le]
  calc
    _ ≤ (1+L/r)/L := div_le_div_of_nonneg_right hz hLpos.le
    _ = 1/L+1/r := by field_simp
    _ ≤ 1+1/r := by
      have hdiv : 1/L ≤ 1 := (div_le_iff₀ hLpos).mpr (by simpa using hL)
      exact add_le_add_left hdiv (1/r)

theorem scaled_riemannZeta_norm_bound_one {L : ℝ} {w : ℂ}
    (hL : 1 ≤ L) (hw : 1 ≤ w.re) :
    ‖riemannZeta (1 + w / (L:ℂ)) / (L:ℂ)‖ ≤ 2 := by
  convert scaled_riemannZeta_norm_le (r := 1) hL zero_lt_one hw using 1
  norm_num

end

end SixthMoment
