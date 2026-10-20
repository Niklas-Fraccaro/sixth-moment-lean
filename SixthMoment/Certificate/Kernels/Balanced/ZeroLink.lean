import SixthMoment.Certificate.Kernels.Balanced.Segments

namespace SixthMoment
open _root_.SixthMoment.Finite

theorem denominatorZeroKernel_eq_integer (A B C D : Nat) (p q : List Int) :
    denominatorZeroKernel (fun k => (coef p k.val : ℝ)) (fun k => (coef q k.val : ℝ))
      (realEndpoint A) (realEndpoint B) (realEndpoint C) (realEndpoint D) =
      ((Finite.d0 A B C D p q : Int) : ℝ)/
        ((Finite.d0Denominator : ℝ)*(Finite.scale : ℝ)^13) := by
  let f := fun t => denominatorZeroIntegrand (fun k => (coef p k.val : ℝ))
    (fun k => (coef q k.val : ℝ))
    (realEndpoint A) (realEndpoint B) (realEndpoint C) (realEndpoint D) t
  let ks := integerD0Knots A B C D
  have hint : ∀ l ∈ ks, ∀ u ∈ ks,
      IntervalIntegrable f MeasureTheory.volume (realEndpoint l) (realEndpoint u) := by
    intro l hl u hu
    exact denominatorZeroIntegrand_intervalIntegrable _ _
      (realEndpoint_nonneg _) (realEndpoint_nonneg _) (realEndpoint_nonneg _) (realEndpoint_nonneg _)
      ⟨realEndpoint_nonneg _, normalized_knot_upper hl⟩
      ⟨realEndpoint_nonneg _, normalized_knot_upper hu⟩
  have hs := interval_sum_consecutive f realEndpoint 0 ks hint
  rw [list_headD_eq_head ks 0 (integerD0Knots_nonempty A B C D),
    list_getLastD_eq_getLast ks 0 (integerD0Knots_nonempty A B C D)] at hs
  rw [(integerD0Knots_endpoints A B C D).1, (integerD0Knots_endpoints A B C D).2] at hs
  simp only [realEndpoint_zero, realEndpoint_min, realEndpoint_add] at hs
  rw [denominatorZeroKernel_one_dimensional _ _
    (realEndpoint_nonneg _) (realEndpoint_nonneg _) (realEndpoint_nonneg _) (realEndpoint_nonneg _)]
  change (∫ t in 0..min (realEndpoint A+realEndpoint B) (realEndpoint C+realEndpoint D), f t) = _
  rw [← hs]
  calc
    ((ks.zip ks.tail).map (fun lr => ∫ t in realEndpoint lr.1..realEndpoint lr.2, f t)).sum =
      ((ks.zip ks.tail).map (fun lr => ((integerD0Segment A B C D p q lr.1 lr.2 : Int) : ℝ)/
        ((Finite.d0Denominator : ℝ)*(Finite.scale : ℝ)^13))).sum := by
      congr 1
      apply List.map_congr_left
      intro lr hlr
      exact denominator_segment_integral p q hlr
    _ = _ := by
      rw [d0_eq_segments, integer_sum_cast, List.map_map]
      simp only [Function.comp_def, div_eq_mul_inv]
      rw [List.sum_map_mul_right]

end SixthMoment
