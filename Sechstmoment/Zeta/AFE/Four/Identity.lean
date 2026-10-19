import Sechstmoment.Zeta.AFE.Four.IntegralIdentity
import Sechstmoment.Zeta.AFE.Four.SpecificationBridge

namespace Sechstmoment.Source
noncomputable section

/-- The literal fixed-weight source proposition, with no AFE hypothesis. -/
theorem bblrFixedAFE_proved : BBLRv1FixedApproximateFEInput := by
  exact bblrFixedAFE_of_uniform_smallShifts fixedAFE_uniform_smallShifts

end
end Sechstmoment.Source
