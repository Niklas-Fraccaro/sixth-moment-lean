import Std

namespace SixthMoment

inductive TestType where
  | U | V
  deriving DecidableEq, Repr

set_option maxRecDepth 100000
set_option maxHeartbeats 0

end SixthMoment
