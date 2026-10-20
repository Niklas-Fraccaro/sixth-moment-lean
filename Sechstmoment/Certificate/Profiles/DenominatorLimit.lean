import Sechstmoment.Certificate.Profiles.GramEndpoint
import Sechstmoment.Certificate.Profiles.Limits


namespace Sechstmoment
open Filter
open scoped Topology
noncomputable section

set_option maxHeartbeats 2000000

theorem certificateProfileDenominator_tendsto :
    Tendsto certificateProfileDenominator atTop (𝓝 (Finite.finiteDenominator : ℝ)) := by
  rw [← certificatePointDenominator_eq_finite]
  exact certificateProfileDenominator_tendsto_point

end
end Sechstmoment
