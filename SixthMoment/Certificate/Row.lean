import SixthMoment.Zeta.TestTypes
import Std

namespace SixthMoment

structure TestDatum where
  index : Nat
  typ : TestType
  A : Nat
  B : Nat
  degree : Nat
  coefficient : Int
  deriving DecidableEq, Repr

set_option maxRecDepth 100000
set_option maxHeartbeats 0

end SixthMoment
