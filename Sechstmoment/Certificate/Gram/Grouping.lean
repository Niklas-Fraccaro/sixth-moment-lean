import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Tactic.ComputeDegree
import Sechstmoment.Certificate.Exact.GramEntries
import Sechstmoment.Certificate.Tests

namespace Sechstmoment
open Complex Polynomial
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

def certificateFeatureRows (x : Finite.Feature) : List TestDatum :=
  certificate.filter fun d => decide (d.typ = x.typ ∧ d.A = x.A ∧ d.B = x.B)

set_option maxHeartbeats 0 in
theorem certificateFeatureRows_permutation :
    (Finite.features.flatMap certificateFeatureRows).Perm certificate := by
  decide +kernel

def featureTestPolynomial (x : Finite.Feature) : ℝ[X] :=
  Polynomial.ofFn 5 (fun r : Fin 5 => (Finite.coef x.poly r.val : ℝ))

theorem featureTestPolynomial_coeff (x : Finite.Feature) (r : Fin 5) :
    (featureTestPolynomial x).coeff r.val = (Finite.coef x.poly r.val : ℝ) := by
  simp [featureTestPolynomial,r.isLt]

theorem featureTestPolynomial_natDegree (x : Finite.Feature) :
    (featureTestPolynomial x).natDegree ≤ 4 := by
  have h := Polynomial.ofFn_natDegree_lt (R := ℝ) (n := 5) (by omega)
    (fun r : Fin 5 => (Finite.coef x.poly r.val : ℝ))
  exact Nat.le_of_lt_succ h

def featureRawZetaTest (profiles : TestType → ℝ → ℝ → ℝ)
    (T t : ℝ) (x : Finite.Feature) : ℂ :=
  rawZetaTest x.typ T t (featureTestPolynomial x)
    (profiles x.typ ((x.A : ℝ)/base)) (profiles x.typ ((x.B : ℝ)/base))

def featureZetaTest (profiles : TestType → ℝ → ℝ → ℝ)
    (T t : ℝ) (x : Finite.Feature) : ℂ :=
  phaseProjection (criticalChi t) (featureRawZetaTest profiles T t x)

private theorem grouping_list_sum_flatMap {α : Type} (l : List α) (f : α → List ℂ) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatMap_cons,List.sum_append,List.map_cons,List.sum_cons,ih]

private theorem grouping_list_sum_fin (l : List TestDatum) (f : TestDatum → Fin 5 → ℂ) :
    (l.map fun d => ∑ r : Fin 5, f d r).sum =
      ∑ r : Fin 5, (l.map fun d => f d r).sum := by
  induction l with
  | nil => simp
  | cons d ds ih => simp only [List.map_cons,List.sum_cons,ih,Finset.sum_add_distrib]

private theorem grouping_list_sum_mul (l : List TestDatum) (f : TestDatum → ℂ) (b : ℂ) :
    (l.map fun d => f d*b).sum = (l.map f).sum*b := by
  induction l with
  | nil => simp
  | cons d ds ih => simp only [List.map_cons,List.sum_cons,ih,add_mul]

private theorem grouping_filter_sum (x : Finite.Feature) (f : TestDatum → ℤ) :
    ((certificateFeatureRows x).map f).sum =
      (certificate.map fun d => if d.typ = x.typ ∧ d.A = x.A ∧ d.B = x.B then f d else 0).sum := by
  unfold certificateFeatureRows
  generalize certificate = l
  induction l with
  | nil => simp
  | cons d ds ih =>
    by_cases h : d.typ = x.typ ∧ d.A = x.A ∧ d.B = x.B
    · rw [List.filter_cons_of_pos (by simpa only [decide_eq_true_eq] using h)]
      simp only [List.map_cons,List.sum_cons,ite_eq_left h,ih]
    · rw [List.filter_cons_of_neg (by simpa only [decide_eq_true_eq] using h)]
      simp only [List.map_cons,List.sum_cons,ite_eq_right h,zero_add,ih]

private theorem grouping_aggregate_coefficient (x : Finite.Feature) (r : Fin 5)
    (hx : x ∈ Finite.features) :
    (((certificateFeatureRows x).map fun d =>
      d.coefficient*Finite.coef (Finite.cheb d.degree) r.val).sum : ℂ) =
        (Finite.coef x.poly r.val : ℂ) := by
  rw [grouping_filter_sum]
  have h := congrArg (fun p : List ℤ => Finite.coef p r.val)
    (Finite.features_aggregate_correct x hx)
  have he : Finite.coef (Finite.aggregate x) r.val =
      (certificate.map fun d => if d.typ = x.typ ∧ d.A = x.A ∧ d.B = x.B then
        d.coefficient*Finite.coef (Finite.cheb d.degree) r.val else 0).sum := by
    simp [Finite.aggregate,Finite.coef,r.isLt,Finite.sum,←List.sum_eq_foldl]
  rw [he] at h
  exact_mod_cast h

private theorem grouping_manuscriptTestPolynomial_natDegree_le_four (m : ℕ) :
    (manuscriptTestPolynomial m).natDegree ≤ 4 := by
  unfold manuscriptTestPolynomial
  split <;> compute_degree!

private theorem grouping_manuscriptTestPolynomial_coeff_eq_cheb
    (m : ℕ) (hm : m ≤ 4) (r : Fin 5) :
    (manuscriptTestPolynomial m).coeff r.val =
      (Finite.coef (Finite.cheb m) r.val : ℝ) := by
  interval_cases m <;> fin_cases r <;>
    norm_num [manuscriptTestPolynomial,Finite.coef,Finite.cheb,Polynomial.coeff_add,
      Polynomial.coeff_sub,Polynomial.coeff_mul,Polynomial.coeff_X_pow,
      Polynomial.coeff_one,Polynomial.coeff_X]

private theorem rawZetaTest_finite_polynomial (τ : TestType) (T t : ℝ)
    (p : ℝ[X]) (hp : p.natDegree ≤ 4) (f g : ℝ → ℝ) :
    rawZetaTest τ T t p f g =
      ∑ r : Fin 5, (p.coeff r.val : ℂ)*
        rawZetaTest τ T t (Polynomial.X^r.val) f g := by
  have hc : zetaCp T t p = ∑ r : Fin 5,
      (p.coeff r.val : ℂ)*centeredZetaDerivative T r.val (criticalLinePoint t) := by
    unfold zetaCp zetaPolynomialDerivative
    rw [p.sum_over_range' (fun n => by simp) 5 (by omega)]
    exact (Fin.sum_univ_eq_sum_range _ 5).symm
  have hm (r : Fin 5) : zetaCp T t (Polynomial.X^r.val) =
      centeredZetaDerivative T r.val (criticalLinePoint t) := by
    simp [zetaCp,zetaPolynomialDerivative,Polynomial.X_pow_eq_monomial,Polynomial.sum_monomial_index]
  cases τ <;> simp only [rawZetaTest,hc,hm,Finset.sum_mul,Finset.mul_sum]
  all_goals apply Finset.sum_congr rfl; intro r _; ring

theorem featureRawZetaTest_eq_original_rows
    (profiles : TestType → ℝ → ℝ → ℝ) (T t : ℝ)
    {x : Finite.Feature} (hx : x ∈ Finite.features) :
    featureRawZetaTest profiles T t x =
      ((certificateFeatureRows x).map fun d => (d.coefficient : ℂ)*
        rawZetaTest d.typ T t (manuscriptTestPolynomial d.degree)
          (profiles d.typ ((d.A : ℝ)/base)) (profiles d.typ ((d.B : ℝ)/base))).sum := by
  rw [featureRawZetaTest,rawZetaTest_finite_polynomial _ _ _ _
    (featureTestPolynomial_natDegree x)]
  have he : ((certificateFeatureRows x).map fun d => (d.coefficient : ℂ)*
      rawZetaTest d.typ T t (manuscriptTestPolynomial d.degree)
        (profiles d.typ ((d.A : ℝ)/base)) (profiles d.typ ((d.B : ℝ)/base))).sum =
    ((certificateFeatureRows x).map fun d => ∑ r : Fin 5,
      ((d.coefficient*Finite.coef (Finite.cheb d.degree) r.val : ℤ) : ℂ)*
        rawZetaTest x.typ T t (Polynomial.X^r.val)
          (profiles x.typ ((x.A : ℝ)/base)) (profiles x.typ ((x.B : ℝ)/base))).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro d hd
    obtain ⟨hc,hkey⟩ := List.mem_filter.mp hd
    have hk : d.typ = x.typ ∧ d.A = x.A ∧ d.B = x.B := of_decide_eq_true hkey
    rw [rawZetaTest_finite_polynomial _ _ _ _ (grouping_manuscriptTestPolynomial_natDegree_le_four _),
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [grouping_manuscriptTestPolynomial_coeff_eq_cheb d.degree (certificate_valid d hc).2.2.1 r]
    simp only [hk.1,hk.2.1,hk.2.2,Int.cast_mul ]
    push_cast
    ring
  rw [he,grouping_list_sum_fin]
  apply Finset.sum_congr rfl
  intro r _
  rw [grouping_list_sum_mul]
  have hc : ((certificateFeatureRows x).map fun d =>
      ((d.coefficient*Finite.coef (Finite.cheb d.degree) r.val : ℤ) : ℂ)).sum =
      (Finite.coef x.poly r.val : ℂ) := by
    have he := Int.cast_list_sum (R := ℂ)
      ((certificateFeatureRows x).map fun d =>
        d.coefficient*Finite.coef (Finite.cheb d.degree) r.val)
    simp only [List.map_map,Function.comp_def] at he
    rw [←he]
    exact grouping_aggregate_coefficient x r hx
  rw [hc,featureTestPolynomial_coeff]
  norm_cast

theorem certificateRawZetaTest_eq_feature_sum
    (profiles : TestType → ℝ → ℝ → ℝ) (T t : ℝ) :
    certificateRawZetaTest profiles T t =
      (Finite.features.map (featureRawZetaTest profiles T t)).sum := by
  unfold certificateRawZetaTest
  rw [← (certificateFeatureRows_permutation.map _).sum_eq]
  rw [List.map_flatMap,grouping_list_sum_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro x hx
  exact (featureRawZetaTest_eq_original_rows profiles T t hx).symm

private theorem grouping_phaseProjection_sum (χ : ℂ) (l : List ℂ) :
    phaseProjection χ l.sum = (l.map (phaseProjection χ)).sum := by
  induction l with
  | nil => simp [phaseProjection]
  | cons a l ih => simp only [List.sum_cons,List.map_cons,phaseProjection_add,ih]

theorem certificateZetaTest_eq_feature_sum
    (profiles : TestType → ℝ → ℝ → ℝ) (T t : ℝ) :
    certificateZetaTest profiles T t =
      (Finite.features.map (featureZetaTest profiles T t)).sum := by
  unfold certificateZetaTest
  rw [certificateRawZetaTest_eq_feature_sum,grouping_phaseProjection_sum,List.map_map]
  rfl

end
end Sechstmoment
