import Sechstmoment.Denominator.Unbalanced.Conjugation

namespace Sechstmoment

def D04UnbalancedDenominatorAsymptotic : Prop :=
  D04UnbalancedMinusAsymptotic ∧ D04UnbalancedPlusAsymptotic

end Sechstmoment
