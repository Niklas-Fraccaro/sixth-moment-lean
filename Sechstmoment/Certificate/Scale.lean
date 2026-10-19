import Mathlib.Data.Int.Basic
import Std

namespace Sechstmoment

def base : Nat := 100000000

set_option maxRecDepth 100000
set_option maxHeartbeats 0

end Sechstmoment

/-! Exact integer evaluator. No integral or moment asymptotic is assumed here.
The link to the mathematical denominator is a separate theorem obligation. -/

namespace Sechstmoment.Finite

def base : ℕ := 100000000
def scale : ℤ := 24 * (base : ℤ)

end Sechstmoment.Finite
