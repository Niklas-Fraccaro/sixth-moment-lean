import Sechstmoment.Certificate.Exact.DenominatorBound
import Sechstmoment.Certificate.Profiles.Denominator

/-! The literal endpoint Gram sum is exactly the existing certified rational
denominator.  This uses the original triangular pairs and multiplicities,
the proved kernel/integer bridges, and the proved complete block aggregation. -/

namespace Sechstmoment
noncomputable section

set_option maxHeartbeats 500000

theorem certificatePairZeroKernel_eq_integer (ij : ℕ × ℕ) :
    (if ij.1 = ij.2 then (1 : ℝ) else 2) *
      certificateGramZeroKernel (Finite.feature ij.1) (Finite.feature ij.2)
        (certificateFeatureEndpoints (Finite.feature ij.1) (Finite.feature ij.2)) =
      (Finite.pairZero ij : ℝ) /
        ((Finite.d0Denominator : ℝ) * (Finite.scale : ℝ) ^ 13) := by
  rw [certificateGramZeroKernel_endpoints]
  by_cases hij : ij.1 = ij.2 <;>
    simp [Finite.pairZero, hij, Int.cast_mul, mul_div_assoc]

theorem certificatePairMinusKernel_eq_integer (ij : ℕ × ℕ) :
    (if ij.1 = ij.2 then (1 : ℝ) else 2) *
      certificateGramMinusKernel (Finite.feature ij.1) (Finite.feature ij.2)
        (certificateFeatureEndpoints (Finite.feature ij.1) (Finite.feature ij.2)) =
      (Finite.pairMinus ij : ℝ) /
        ((Finite.dminusDenominator : ℝ) * (Finite.scale : ℝ) ^ 13) := by
  rw [certificateGramMinusKernel_endpoints]
  by_cases hij : ij.1 = ij.2 <;>
    simp [Finite.pairMinus, hij, Int.cast_mul, mul_div_assoc]

theorem certificateGramZeroSum_eq_integer :
    (Finite.pairs.map (fun ij =>
      (if ij.1 = ij.2 then (1 : ℝ) else 2) *
        certificateGramZeroKernel (Finite.feature ij.1) (Finite.feature ij.2)
          (certificateFeatureEndpoints (Finite.feature ij.1) (Finite.feature ij.2)))).sum =
      (Finite.totalZeroInteger : ℝ) /
        ((Finite.d0Denominator : ℝ) * (Finite.scale : ℝ) ^ 13) := by
  simp_rw [certificatePairZeroKernel_eq_integer]
  rw [Finite.total_zero_covers_pairs, integer_sum_cast, List.map_map]
  simp only [Function.comp_def, div_eq_mul_inv]
  rw [List.sum_map_mul_right]

theorem certificateGramMinusSum_eq_integer :
    (Finite.pairs.map (fun ij =>
      (if ij.1 = ij.2 then (1 : ℝ) else 2) *
        certificateGramMinusKernel (Finite.feature ij.1) (Finite.feature ij.2)
          (certificateFeatureEndpoints (Finite.feature ij.1) (Finite.feature ij.2)))).sum =
      (Finite.totalMinusInteger : ℝ) /
        ((Finite.dminusDenominator : ℝ) * (Finite.scale : ℝ) ^ 13) := by
  simp_rw [certificatePairMinusKernel_eq_integer]
  rw [Finite.total_minus_covers_pairs, integer_sum_cast, List.map_map]
  simp only [Function.comp_def, div_eq_mul_inv]
  rw [List.sum_map_mul_right]

/-- The terminal scalar profile-denominator target is the original exact
certified denominator, with its factor 1/2 and scale unchanged. -/
theorem certificatePointDenominator_eq_finite :
    certificatePointDenominator = (Finite.finiteDenominator : ℝ) := by
  unfold certificatePointDenominator
  rw [certificateGramZeroSum_eq_integer, certificateGramMinusSum_eq_integer]
  unfold Finite.finiteDenominator
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end
end Sechstmoment
