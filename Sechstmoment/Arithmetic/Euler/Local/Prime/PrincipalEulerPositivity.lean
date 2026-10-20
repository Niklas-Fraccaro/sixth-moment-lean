import Sechstmoment.Arithmetic.Euler.Local.Prime.PrincipalEulerErrorBound


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem principal_euler_positive (x : ℝ) (hx0 : 0≤x) (hx1 : x<1) : 0<(1-x)^4*(1+4*x+x^2) := by
  apply mul_pos (pow_pos (sub_pos.mpr hx1) 4)
  nlinarith [sq_nonneg x]
theorem prime_reciprocal_in_unit_interval (p : ℕ) (hp : Nat.Prime p) : 0<(p:ℝ)⁻¹ ∧ (p:ℝ)⁻¹<1 := by
  have h1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  constructor
  · positivity
  · exact (inv_lt_one₀ (by positivity : (0:ℝ)<p)).mpr h1

end Sechstmoment.Source.NoDPLocal
