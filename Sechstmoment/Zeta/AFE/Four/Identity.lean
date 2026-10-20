import Sechstmoment.Zeta.AFE.Four.IntegralIdentity
import Sechstmoment.Zeta.AFE.Four.SpecificationBridge

namespace Sechstmoment.Source
noncomputable section

theorem bblrFixedAFE_proved : BBLRv1FixedApproximateFEInput := by
  exact bblrFixedAFE_of_uniform_smallShifts fixedAFE_uniform_smallShifts

end
end Sechstmoment.Source
