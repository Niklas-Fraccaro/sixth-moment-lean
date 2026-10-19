import Sechstmoment.Analysis.Integration.IntervalSubdivision
import Sechstmoment.Certificate.Kernels.Balanced.NormalizedKnots

namespace Sechstmoment
open scoped BigOperators
open _root_.Sechstmoment.Finite

def integerD0Segment (A B C D : Nat) (p q : List Int) (left right : Nat) : Int :=
  24*((right : Int)-left)*Finite.sum ((List.range 13).map fun (j : Nat) =>
    let t : Int := 24*left+2*((right : Int)-left)*j
    let H := (Finite.scale-24*A-24*B-24*C-24*D+2*t)/2
    coef ncNumerators j*w6 t (24*A) (24*B) (24*C) (24*D)*
      integerInner p q (12*((A : Int)+B-C-D)) H)

theorem d0_eq_segments (A B C D : Nat) (p q : List Int) :
    Finite.d0 A B C D p q =
      Finite.sum (((integerD0Knots A B C D).zip (integerD0Knots A B C D).tail).map
        (fun lr => integerD0Segment A B C D p q lr.1 lr.2)) := by
  rfl

theorem ncNumerator_eq_list (j : Fin 13) : ncNumerator j = Finite.coef ncNumerators j.val := by
  fin_cases j <;> norm_num [ncNumerator, ncNumerators, coef]

theorem sum_range13_fin (f : Nat → ℝ) :
    ((List.range 13).map f).sum = ∑ j : Fin 13, f j.val := by
  norm_num [List.range_succ, Fin.sum_univ_succ]

theorem integer_quadrature_node (left right : Nat) (j : Fin 13) :
    realEndpoint left+(realEndpoint right-realEndpoint left)*((j.val : ℝ)/12) =
      ((24*(left : Int)+2*((right : Int)-left)*j.val : Int) : ℝ)/(Finite.scale : ℝ) := by
  simp only [realEndpoint_scale]
  push_cast
  field_simp
  ring

theorem denominator_natural_node (p q : List Int) (A B C D : Nat) (t : Int) :
    denominatorZeroIntegrand (fun k => (coef p k.val : ℝ))
      (fun k => (coef q k.val : ℝ))
      (realEndpoint A) (realEndpoint B) (realEndpoint C) (realEndpoint D)
      (t/(Finite.scale : ℝ)) =
      ((w6 t (24*A) (24*B) (24*C) (24*D)*
        integerInner p q (12*((A : Int)+B-C-D))
          ((Finite.scale-24*A-24*B-24*C-24*D+2*t)/2) : Int) : ℝ)/
          (6*315*(Finite.scale : ℝ)^12) := by
  simpa only [realEndpoint_scale, Int.cast_natCast] using
    denominator_integer_node p q A B C D t

theorem denominator_segment_integral (p q : List Int) {A B C D left right : Nat}
    (hp : (left,right) ∈ (integerD0Knots A B C D).zip (integerD0Knots A B C D).tail) :
    (∫ t in realEndpoint left..realEndpoint right,
      denominatorZeroIntegrand (fun k => (coef p k.val : ℝ))
        (fun k => (coef q k.val : ℝ))
        (realEndpoint A) (realEndpoint B) (realEndpoint C) (realEndpoint D) t) =
      ((integerD0Segment A B C D p q left right : Int) : ℝ)/
        ((Finite.d0Denominator : ℝ)*(Finite.scale : ℝ)^13) := by
  rw [denominatorZero_subinterval_quadrature _ _
    (realEndpoint_nonneg _) (realEndpoint_nonneg _) (realEndpoint_nonneg _) (realEndpoint_nonneg _)
    (realEndpoint_nonneg _) (normalized_knot_upper (List.mem_of_mem_tail (List.of_mem_zip hp).2))
    (normalized_knots_order hp) (normalized_knots_avoid hp)]
  simp_rw [integer_quadrature_node, denominator_natural_node]
  simp only [ncWeight, ncNumerator_eq_list, integerD0Segment, Int.cast_mul,
    Int.cast_ofNat, Int.cast_sub, Int.cast_natCast, integer_sum_cast, List.map_map,
    Function.comp_def, sum_range13_fin]
  norm_num only [Finite.d0Denominator, Int.cast_mul, Int.cast_ofNat]
  have hw : realEndpoint right-realEndpoint left =
      24*((right : ℝ)-left)/(Finite.scale : ℝ) := by
    simp only [realEndpoint_scale]
    ring
  rw [hw]
  simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  field_simp [Finite.d0Denominator]
  ring

end Sechstmoment
