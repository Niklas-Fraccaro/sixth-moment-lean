import SixthMoment.Denominator.Unbalanced.Conjugation

namespace SixthMoment

def D04UnbalancedDenominatorAsymptotic : Prop :=
  D04UnbalancedMinusAsymptotic ∧ D04UnbalancedPlusAsymptotic

end SixthMoment
