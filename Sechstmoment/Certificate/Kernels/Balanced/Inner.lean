import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Sechstmoment.Analysis.Integration.PolynomialIntegral

namespace Sechstmoment

open scoped BigOperators

noncomputable def evalDegreeFour (p : Fin 5 → ℝ) (x : ℝ) : ℝ :=
  ∑ k : Fin 5, p k * x^k.val

noncomputable def shiftedCoefficient (p : Fin 5 → ℝ) (delta sign : ℝ)
    (k : Fin 5) : ℝ :=
  ∑ r : Fin 5, if k.val ≤ r.val then
    p r * (Nat.choose r.val k.val) * delta^(r.val-k.val) * sign^k.val else 0

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem shiftedPolynomial_exact (p : Fin 5 → ℝ) (delta sign x : ℝ) :
    evalDegreeFour p (delta+sign*x) =
      ∑ k : Fin 5, shiftedCoefficient p delta sign k * x^k.val := by
  norm_num [evalDegreeFour, shiftedCoefficient, Fin.sum_univ_succ, Nat.choose]
  ring

noncomputable def productCoefficient (p q : Fin 5 → ℝ) (k : Fin 9) : ℝ :=
  ∑ i : Fin 5, ∑ j : Fin 5,
    if i.val+j.val = k.val then p i * q j else 0

theorem polynomialProduct_exact (p q : Fin 5 → ℝ) (x : ℝ) :
    evalDegreeFour p x * evalDegreeFour q x =
      ∑ k : Fin 9, productCoefficient p q k * x^k.val := by
  norm_num [evalDegreeFour, productCoefficient, Fin.sum_univ_succ]
  ring

noncomputable def innerCoefficient (p q : Fin 5 → ℝ) (delta : ℝ) : Fin 9 → ℝ :=
  productCoefficient (shiftedCoefficient p delta (-1))
    (shiftedCoefficient q (-delta) (-1))

theorem denominator_integrand_polynomial (p q : Fin 5 → ℝ) (delta x : ℝ) :
    evalDegreeFour p (delta-x) * evalDegreeFour q (-delta-x) =
      ∑ k : Fin 9, innerCoefficient p q delta k * x^k.val := by
  have hp := shiftedPolynomial_exact p delta (-1) x
  have hq := shiftedPolynomial_exact q (-delta) (-1) x
  simp only [neg_one_mul, sub_eq_add_neg] at hp hq ⊢
  rw [hp, hq]
  exact polynomialProduct_exact _ _ x

/-- Exact evaluation of the inner integral in equation (4.2).
No asymptotic relation to zeta moments is asserted by this theorem. -/
theorem denominator_inner_integral (p q : Fin 5 → ℝ) (delta h : ℝ) :
    (∫ x in -h..h, evalDegreeFour p (delta-x) * evalDegreeFour q (-delta-x)) =
      2*innerCoefficient p q delta 0*h +
      2*innerCoefficient p q delta 2*h^3/3 +
      2*innerCoefficient p q delta 4*h^5/5 +
      2*innerCoefficient p q delta 6*h^7/7 +
      2*innerCoefficient p q delta 8*h^9/9 := by
  simp_rw [denominator_integrand_polynomial]
  rw [integral_finite_polynomial]
  norm_num [Fin.sum_univ_succ]
  ring

end Sechstmoment
