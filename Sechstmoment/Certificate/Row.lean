import Sechstmoment.Zeta.TestTypes
import Std

namespace Sechstmoment

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

end Sechstmoment
