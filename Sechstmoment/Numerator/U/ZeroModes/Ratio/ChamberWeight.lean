import Sechstmoment.Numerator.U.ZeroModes.Contour.RatioWeight
import Sechstmoment.Numerator.U.ZeroModes.PolarChamberInvariance

namespace Sechstmoment.Source
open Complex
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

theorem a03ZeroModeRatioWeight_chamber (m n : Bool) (α : MomentShifts) (z : ℂ) :
    a03ZeroModeRatioWeight (a03ZeroModeChamberShifts m n α) z=a03ZeroModeRatioWeight α z := by
  cases m <;> cases n <;>
    norm_num [a03ZeroModeRatioWeight,a03ZeroModeRatioRoot,a03ZeroModeChamberShifts,a03ZeroModePairPermutation]
    <;> ring_nf <;> simp

theorem a03ZeroModeRatioWeight_dual (α : MomentShifts) (z : ℂ) :
    a03ZeroModeRatioWeight (bblrSixShifts α 1) z=a03ZeroModeRatioWeight α z := by
  norm_num [a03ZeroModeRatioWeight,a03ZeroModeRatioRoot,bblrSixShifts]
  ring_nf

end
end Sechstmoment.Source
