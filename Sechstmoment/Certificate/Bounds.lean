import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum

namespace Sechstmoment

def declaredBound : ℚ := 1077094746 / 26265625
def numeratorLower : ℚ := 46159
def denominatorUpper : ℚ := 18854000000000
def certifiedBound : ℚ := 362880 * numeratorLower ^ 2 / denominatorUpper

theorem denominatorUpper_pos : 0 < denominatorUpper := by norm_num [denominatorUpper]
theorem numeratorLower_pos : 0 < numeratorLower := by norm_num [numeratorLower]
theorem certifiedBound_exact : certifiedBound = 1208080410327 / 29459375000 := by
  norm_num [certifiedBound, numeratorLower, denominatorUpper]
theorem certifiedBound_gt_declared : declaredBound < certifiedBound := by
  norm_num [declaredBound, certifiedBound, numeratorLower, denominatorUpper]
theorem declaredBound_gt_41007 : (41007 : ℚ) / 1000 < declaredBound := by
  norm_num [declaredBound]
theorem certificate_cross_product :
    362880 * 46159 ^ 2 * 26265625 - 1077094746 * 18854000000000 =
      (287356512870000000 : ℤ) := by norm_num

end Sechstmoment
