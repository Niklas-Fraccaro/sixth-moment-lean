import Mathlib.Algebra.BigOperators.Intervals
import Sechstmoment.Certificate.Gram.Grouping

/-! Exact bilinear and triangular norm expansions of the actual certificate.
All 15931 pairs and their diagonal/off-diagonal multiplicities are retained. -/
namespace Sechstmoment
open Complex
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

private theorem groupingNorm_list_sum_flatMap {α : Type} (l : List α) (f : α → List ℝ) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatMap_cons,List.sum_append,List.map_cons,List.sum_cons,ih]

private theorem groupingNorm_sum_range {R : Type} [AddCommMonoid R] (n : ℕ) (f : ℕ → R) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ,Finset.sum_range_succ,ih]

/-- Indexed enumeration is exactly the original ordered feature list. -/
theorem certificateFeatures_indexed :
    (List.range 178).map Finite.feature = Finite.features := by decide +kernel

/-- Complete exact bilinear expansion, before passing to real parts. -/
theorem certificateZetaTest_bilinear_feature_sum
    (profiles profiles' : TestType → ℝ → ℝ → ℝ) (T t : ℝ) :
    certificateZetaTest profiles T t * star (certificateZetaTest profiles' T t) =
      ∑ i ∈ Finset.range 178, ∑ j ∈ Finset.range 178,
        featureZetaTest profiles T t (Finite.feature i) *
          star (featureZetaTest profiles' T t (Finite.feature j)) := by
  simp only [certificateZetaTest_eq_feature_sum,←certificateFeatures_indexed,
    List.map_map,Function.comp_def,groupingNorm_sum_range,star_sum,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]

private theorem groupingNorm_square_to_triangle (n : ℕ) (a : ℕ → ℕ → ℝ)
    (ha : ∀ i j, a i j = a j i) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, a i j) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n-i),
        (if i = i+j then (1:ℝ) else 2)*a i (i+j) := by
  have hsplit : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, a i j) =
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, if i≤j then a i j else 0) +
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, if j < i then a i j else 0) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i≤j
    · have hn : ¬j < i := by omega
      simp [h,hn]
    · have hl : j < i := by omega
      simp [h,hl]
  have hlower : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, if j < i then a i j else 0) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, if i < j then a i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [ha j i]
  rw [hsplit,hlower,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [←Finset.sum_add_distrib]
  have hpoint (j : ℕ) : (if i≤j then a i j else 0)+(if i < j then a i j else 0) =
      if i≤j then (if i=j then (1:ℝ) else 2)*a i j else 0 := by
    by_cases hle : i≤j
    · by_cases heq : i=j
      · subst j; simp
      · have hlt : i < j := by omega
        simp [hle,heq,hlt]; ring
    · have hlt : ¬i < j := by omega
      simp [hle,hlt]
  simp_rw [hpoint]
  rw [←Finset.sum_filter]
  have hset : (Finset.range n).filter (fun j => i≤j) = Finset.Ico i n := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
    omega
  rw [hset,Finset.sum_Ico_eq_sum_range]

/-- Pointwise norm of the actual projected certificate, over the literal
triangular pair enumeration with multiplicity one on its diagonal and two
elsewhere.  The integer certificate scale is unchanged. -/
theorem certificateZetaTest_norm_sq_pair_sum
    (profiles : TestType → ℝ → ℝ → ℝ) (T t : ℝ) :
    ‖certificateZetaTest profiles T t‖^2 =
      (Finite.pairs.map fun ij => (if ij.1=ij.2 then (1:ℝ) else 2)*
        (featureZetaTest profiles T t (Finite.feature ij.1)*
          star (featureZetaTest profiles T t (Finite.feature ij.2))).re).sum := by
  have hs : ‖certificateZetaTest profiles T t‖^2 =
      ∑ i ∈ Finset.range 178, ∑ j ∈ Finset.range 178,
        (featureZetaTest profiles T t (Finite.feature i)*
          star (featureZetaTest profiles T t (Finite.feature j))).re := by
    have hn : ‖certificateZetaTest profiles T t‖^2 =
        (certificateZetaTest profiles T t*star (certificateZetaTest profiles T t)).re := by
      simp [←Complex.normSq_eq_norm_sq,Complex.mul_re,Complex.normSq_apply]
    rw [hn,certificateZetaTest_bilinear_feature_sum]
    simp
  rw [hs,groupingNorm_square_to_triangle]
  · unfold Finite.pairs
    rw [List.map_flatMap,groupingNorm_list_sum_flatMap,groupingNorm_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [List.map_map,groupingNorm_sum_range]
    rfl
  · intro i j
    simp [Complex.mul_re]
    ring

end
end Sechstmoment
