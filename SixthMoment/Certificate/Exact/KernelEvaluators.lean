import Mathlib.Data.Int.Basic
import SixthMoment.Arithmetic.Exact.Polynomials
import SixthMoment.Certificate.Scale
import Std


namespace SixthMoment.Finite

def shifted (p : List ℤ) (delta sign : ℤ) : List ℤ :=
  (List.range 5).map fun k => sum ((List.range 5).map fun r =>
    if k ≤ r then coef p r * scale^(4-r) * choose r k * delta^(r-k) * sign^k else 0)

end SixthMoment.Finite
