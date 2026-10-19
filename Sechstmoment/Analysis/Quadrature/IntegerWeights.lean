import Mathlib.Data.Int.Basic
import Std

/-! Exact integer evaluator. No integral or moment asymptotic is assumed here.
The link to the mathematical denominator is a separate theorem obligation. -/

namespace Sechstmoment.Finite

def ncNumerators : List ℤ :=
  [1364651, 9903168, -7587864, 35725120, -51491295, 87516288,
    -87797136, 87516288, -51491295, 35725120, -7587864, 9903168, 1364651]

end Sechstmoment.Finite
