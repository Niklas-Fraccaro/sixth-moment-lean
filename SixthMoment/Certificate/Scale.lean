import Mathlib.Data.Int.Basic
import Std

namespace SixthMoment

def base : Nat := 100000000

set_option maxRecDepth 100000
set_option maxHeartbeats 0

end SixthMoment


namespace SixthMoment.Finite

def base : ℕ := 100000000
def scale : ℤ := 24 * (base : ℤ)

end SixthMoment.Finite
