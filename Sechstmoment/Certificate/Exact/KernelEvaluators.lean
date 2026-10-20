import Mathlib.Data.Int.Basic
import Sechstmoment.Arithmetic.Exact.Polynomials
import Sechstmoment.Certificate.Scale
import Std


namespace Sechstmoment.Finite

def shifted (p : List ℤ) (delta sign : ℤ) : List ℤ :=
  (List.range 5).map fun k => sum ((List.range 5).map fun r =>
    if k ≤ r then coef p r * scale^(4-r) * choose r k * delta^(r-k) * sign^k else 0)

end Sechstmoment.Finite
