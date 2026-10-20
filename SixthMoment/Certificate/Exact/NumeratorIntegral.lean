import Mathlib.Algebra.BigOperators.Group.List.Basic
import SixthMoment.Certificate.Exact.NumeratorBound
import SixthMoment.Numerator.Kernels.Integral

namespace SixthMoment
open scoped BigOperators
open _root_.SixthMoment.Finite

def numeratorSecondMass (f : Feature) : Nat :=
  if f.typ = .U then f.B else Finite.base-f.B

noncomputable def numeratorFeatureKernel (f : Feature) : ℝ :=
  numeratorPointKernel (fun r => (coef f.poly r.val : ℝ))
    ((f.A : ℝ)/(Finite.base : ℝ))
    ((numeratorSecondMass f : ℝ)/(Finite.base : ℝ))

theorem numerator_feature_lengths : ∀ f ∈ features, f.A ≤ numeratorSecondMass f :=
  by decide +kernel

theorem integer_sum_cast (xs : List Int) :
    (Finite.sum xs : ℝ) = (xs.map fun (z : Int) => (z : ℝ)).sum := by
  unfold Finite.sum
  rw [← List.sum_eq_foldl, Int.cast_list_sum]

theorem numeratorFeatureInteger_kernel {f : Feature}
    (h : f.A ≤ numeratorSecondMass f) :
    (numeratorFeatureInteger f : ℝ)/(numeratorDenominator : ℝ) =
      numeratorFeatureKernel f := by
  have hab : (f.A : ℝ)/(Finite.base : ℝ) ≤
      (numeratorSecondMass f : ℝ)/(Finite.base : ℝ) := by
    apply div_le_div_of_nonneg_right
    · exact_mod_cast h
    · norm_num [Finite.base]
  unfold numeratorFeatureKernel
  rw [numeratorPointKernel_polynomial _ hab]
  norm_num only [Finite.base, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
  rw [← numerator_integer_integral_0, ← numerator_integer_integral_1,
    ← numerator_integer_integral_2, ← numerator_integer_integral_3,
    ← numerator_integer_integral_4]
  unfold numeratorFeatureInteger
  change (Finite.sum ((List.range 5).map fun r =>
    coef f.poly r * numeratorMonomialInteger r f.A (numeratorSecondMass f)) : ℝ) /
      (numeratorDenominator : ℝ) = _
  norm_num [Finite.sum, List.range_succ, Int.cast_add, Int.cast_mul]
  ring

noncomputable def finiteNumeratorKernel : ℝ := (features.map numeratorFeatureKernel).sum

theorem finiteNumerator_kernel : (finiteNumerator : ℝ) = finiteNumeratorKernel := by
  unfold finiteNumerator
  rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast]
  unfold numeratorInteger
  rw [integer_sum_cast, List.map_map, div_eq_mul_inv,
    ← List.sum_map_mul_right]
  unfold finiteNumeratorKernel
  apply congrArg List.sum
  apply List.map_congr_left
  intro f hf
  change (numeratorFeatureInteger f : ℝ)*(numeratorDenominator : ℝ)⁻¹ =
    numeratorFeatureKernel f
  simpa only [div_eq_mul_inv] using
    numeratorFeatureInteger_kernel (numerator_feature_lengths f hf)

theorem finiteNumeratorKernel_gt_lower : (46159 : ℝ) < finiteNumeratorKernel := by
  rw [← finiteNumerator_kernel]
  exact_mod_cast finite_numerator_gt_lower

end SixthMoment
