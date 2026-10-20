import SixthMoment.Analysis.Quadrature.NewtonCotes

namespace SixthMoment
open scoped BigOperators

noncomputable def affineCoefficient13 (c : Fin 13 → ℝ) (a w : ℝ)
    (k : Fin 13) : ℝ :=
  ∑ r : Fin 13, if k.val ≤ r.val then
    c r*(Nat.choose r.val k.val : ℝ)*a^(r.val-k.val)*w^k.val else 0

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem affinePolynomial13_exact (c : Fin 13 → ℝ) (a w x : ℝ) :
    (∑ r : Fin 13, c r*(a+w*x)^r.val) =
      ∑ k : Fin 13, affineCoefficient13 c a w k*x^k.val := by
  norm_num [affineCoefficient13, Fin.sum_univ_succ, Nat.choose]
  ring

theorem affine_interval_integral (f : ℝ → ℝ) (a b : ℝ) :
    (∫ x in a..b, f x) = (b-a)*(∫ u in (0 : ℝ)..1, f (a+(b-a)*u)) := by
  have h := intervalIntegral.smul_integral_comp_add_mul
    (a := (0 : ℝ)) (b := 1) f (b-a) a
  have he : a+(b-a)*1 = b := by ring
  simpa only [mul_zero, add_zero, he, smul_eq_mul] using h.symm

theorem nc_interval_integral_exact (c : Fin 13 → ℝ) (a b : ℝ) :
    (∫ x in a..b, ∑ k : Fin 13, c k*x^k.val) =
      (b-a)*(∑ j : Fin 13, ncWeight j *
        (∑ k : Fin 13, c k*(a+(b-a)*(j.val/12))^k.val)) := by
  rw [affine_interval_integral]
  simp_rw [affinePolynomial13_exact]
  rw [nc_integral_exact]

end SixthMoment
