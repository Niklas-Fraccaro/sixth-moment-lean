import Sechstmoment.Certificate.Profiles.GramEndpoint
import Sechstmoment.Certificate.Profiles.Limits

/-! The complete scalar denominator profile limit at one shared stage.
Both independent original integral kernels converge to their exact
certified rational denominator, with every original pair retained. -/

namespace Sechstmoment
open Filter
open scoped Topology
noncomputable section

set_option maxHeartbeats 2000000

/-- The shared actual U/V profile family recovers the entire exact certified
Gram denominator. This is scalar concentration, with no literature inputs
or actual zeta Gram asymptotic taken as assumptions. -/
theorem certificateProfileDenominator_tendsto :
    Tendsto certificateProfileDenominator atTop (𝓝 (Finite.finiteDenominator : ℝ)) := by
  rw [← certificatePointDenominator_eq_finite]
  exact certificateProfileDenominator_tendsto_point

end
end Sechstmoment
