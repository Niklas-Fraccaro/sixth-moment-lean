import Std

namespace Sechstmoment

inductive TestType where
  | U | V
  deriving DecidableEq, Repr

set_option maxRecDepth 100000
set_option maxHeartbeats 0

end Sechstmoment
