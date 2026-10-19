import Sechstmoment.Denominator.Unbalanced.Conjugation

/-! D04 has both unbalanced phases. Each component is the literal actual
polynomial-height asymptotic with the original unbalanced denominator kernel. -/
namespace Sechstmoment

def D04UnbalancedDenominatorAsymptotic : Prop :=
  D04UnbalancedMinusAsymptotic ∧ D04UnbalancedPlusAsymptotic

end Sechstmoment
