import SixthMoment.Zeta.AFE.Four.IntegralIdentity
import SixthMoment.Zeta.AFE.Four.SpecificationBridge

namespace SixthMoment.Source
noncomputable section

theorem bblrFixedAFE_proved : BBLRv1FixedApproximateFEInput := by
  exact bblrFixedAFE_of_uniform_smallShifts fixedAFE_uniform_smallShifts

end
end SixthMoment.Source
