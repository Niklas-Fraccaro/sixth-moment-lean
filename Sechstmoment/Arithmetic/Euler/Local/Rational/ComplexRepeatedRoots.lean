import Sechstmoment.Arithmetic.Euler.Local.Coefficients.CoefficientMaps


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem coeff4_all_one (n : ℕ) : coeff4 (1:ℂ) 1 1 1 n=((n:ℂ)+1)*((n:ℂ)+2)*((n:ℂ)+3)/6 := by
  have H := coeff4_map Complex.ofRealHom (1:ℝ) 1 1 1 n
  rw [coeff4_equal_roots] at H
  simpa using H.symm

end Sechstmoment.Source.NoDPLocal
