import Mathlib.Analysis.SpecificLimits.Normed
import Sechstmoment.Arithmetic.Euler.Local.Bounds.WeightedTailMajorant


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem polynomial_geometric_summable (s B : ℝ) (hs : ‖s‖<1) :
    Summable (fun n : ℕ => ((n:ℝ)+B)^3*s^n) := by
  have h0 := summable_geometric_of_norm_lt_one hs
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hs
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hs
  have h3 := summable_pow_mul_geometric_of_norm_lt_one 3 hs
  convert ((h3.add (h2.mul_left (3*B))).add (h1.mul_left (3*B^2))).add (h0.mul_left (B^3)) using 1
  ext n
  simp only [pow_one]
  ring

end Sechstmoment.Source.NoDPLocal
