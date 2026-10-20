import Sechstmoment.Arithmetic.Euler.Local.Bounds.SymmetricBounds


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

noncomputable def principalCorrection (x : ℂ) (h : ℕ) : ℂ :=
  x^h*((((h:ℂ)+2)*((h:ℂ)+1)/2)-(h:ℂ)*((h:ℂ)+2)*x+(h:ℂ)*((h:ℂ)+1)/2*x^2)
theorem principalCorrection_from_numerator (x : ℂ) (h : ℕ) :
    principalCorrection x h=x^h*(numerator (1:ℂ) 1 1 1 h x-
      (h:ℂ)*((h:ℂ)+1)*((h:ℂ)+2)/6*(1-x)^3) := by
  rw [numerator_all_one]
  unfold principalCorrection
  ring

end Sechstmoment.Source.NoDPLocal
