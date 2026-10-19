import Sechstmoment.Numerator.U.Bounds.SharpGammaFrontReduction
import Sechstmoment.Numerator.U.OffDiagonal
import Sechstmoment.Numerator.U.ZeroModes.EightEtaFrontSharpMainBudget

/-! The original rectangular quantitative A03 error form. The contour,
source loss and native cutoff parameters are fixed before T; all front
reconstruction and source comparison estimates are proved production inputs. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 2000000

private theorem sharp_envelope_ge_one {T a b ε : ℝ} (hT : 1≤T)
    (ha : 0≤a) (hb : 0≤b) (hε : 0<ε) :
    1≤T^(rectangularFirstExponent a b ε)+T^(rectangularSecondExponent a b ε) := by
  have hp : 0≤rectangularFirstExponent a b ε := by
    dsimp [rectangularFirstExponent]
    linarith only [ha,hb,hε]
  exact (Real.one_le_rpow hT hp).trans (le_add_of_nonneg_right
    (Real.rpow_nonneg (zero_le_one.trans hT) _))

private theorem sharp_first_power_le_envelope {T a b ε : ℝ} (hT : 0≤T) :
    T^(rectangularFirstExponent a b ε)≤
      T^(rectangularFirstExponent a b ε)+T^(rectangularSecondExponent a b ε) :=
  le_add_of_nonneg_right (Real.rpow_nonneg hT _)

private theorem norm_eight_bool_sum_le (F : Bool→Bool→Bool→ℂ) (E : ℝ)
    (hF : ∀ dual m n,‖F dual m n‖≤E) : ‖∑dual : Bool,∑m : Bool,∑n : Bool,F dual m n‖≤8*E := by
  calc
    _≤∑dual : Bool,∑m : Bool,∑n : Bool,‖F dual m n‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro dual _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro m _
      exact norm_sum_le _ _
    _≤∑_dual : Bool,∑_m : Bool,∑_n : Bool,E := by
      apply Finset.sum_le_sum
      intro dual _
      apply Finset.sum_le_sum
      intro m _
      exact Finset.sum_le_sum (fun n _ => hF dual m n)
    _=_ := by simp only [Fintype.sum_bool]; ring

end
end Sechstmoment
