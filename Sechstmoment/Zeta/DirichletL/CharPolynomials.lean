import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic


open Complex Finset
open scoped BigOperators ComplexConjugate Classical

namespace Sechstmoment.Source
noncomputable section

theorem char_conj_orthogonality (q : ℕ) [NeZero q] (a b : ZMod q) :
    ∑ χ : DirichletCharacter ℂ q, conj (χ a) * χ b =
      if IsUnit a ∧ a = b then (q.totient : ℂ) else 0 := by
  classical
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    have hc (χ : DirichletCharacter ℂ q) :
        conj (χ (u : ZMod q)) = χ ((u : ZMod q)⁻¹) := by
      rw [← RCLike.star_def, MulChar.star_apply', MulChar.inv_apply,
        Ring.inverse_unit, ZMod.inv_coe_unit]
    simp_rw [hc]
    simpa only [Units.isUnit, true_and] using
      (DirichletCharacter.sum_char_inv_mul_char_eq ℂ u.isUnit b)
  · simp [MulChar.map_nonunit _ ha, ha]

theorem finite_transform_parseval {ι κ : Type*} [Fintype ι] [Fintype κ]
    (U : κ → ι → ℂ) (A : ι → ℂ) (m : ι → ℝ)
    (hU : ∀ a b, ∑ k, conj (U k a) * U k b =
      if a = b then (m a : ℂ) else 0) :
    ∑ k, ‖∑ a, A a * U k a‖ ^ 2 = ∑ a, m a * ‖A a‖ ^ 2 := by
  classical
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
    ← Complex.conj_mul']
  calc
    (∑ k, conj (∑ a, A a * U k a) * ∑ b, A b * U k b) =
        ∑ a, ∑ b, conj (A b) * A a * ∑ k, conj (U k b) * U k a := by
      simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ a, (m a : ℂ) * (conj (A a) * A a) := by
      simp_rw [hU]
      simp [mul_comm, mul_left_comm]

theorem char_parseval (q : ℕ) [NeZero q] (A : ZMod q → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ a, A a * χ a‖ ^ 2 =
      (q.totient : ℝ) * ∑ a : ZMod q with IsUnit a, ‖A a‖ ^ 2 := by
  have h := finite_transform_parseval (fun χ : DirichletCharacter ℂ q => fun a => χ a)
    A (fun a => if IsUnit a then (q.totient : ℝ) else 0) (by
      intro a b
      rw [char_conj_orthogonality]
      by_cases hab : a = b
      · subst b
        by_cases ha : IsUnit a <;> simp [ha]
      · simp [hab])
  simpa [Finset.mul_sum, Finset.sum_filter, ite_mul] using h

theorem finite_sum_norm_sq_le {ι : Type*} (s : Finset ι) (c : ι → ℂ) :
    ‖∑ n ∈ s, c n‖ ^ 2 ≤ (s.card : ℝ) * ∑ n ∈ s, ‖c n‖ ^ 2 := by
  calc
    _ ≤ (∑ n ∈ s, ‖c n‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ _ := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun n => ‖c n‖)

def charResidueFibre (q : ℕ) (s : Finset ℕ) (a : ZMod q) : Finset ℕ :=
  s.filter (fun n : ℕ => (n : ZMod q) = a)

theorem charPolynomial_eq_grouped (q : ℕ) [NeZero q] (s : Finset ℕ)
    (c : ℕ → ℂ) (χ : DirichletCharacter ℂ q) :
    (∑ n ∈ s, c n * χ n) =
      ∑ a : ZMod q, (∑ n ∈ charResidueFibre q s a, c n) * χ a := by
  symm
  calc
    _ = ∑ a : ZMod q, ∑ n ∈ charResidueFibre q s a, c n * χ n := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      rw [(Finset.mem_filter.mp hn).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _

theorem charPolynomial_parseval (q : ℕ) [NeZero q] (s : Finset ℕ) (c : ℕ → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ s, c n * χ n‖ ^ 2 =
      (q.totient : ℝ) *
        ∑ a : ZMod q with IsUnit a, ‖∑ n ∈ charResidueFibre q s a, c n‖ ^ 2 := by
  simp_rw [charPolynomial_eq_grouped q s c]
  exact char_parseval q _

theorem charPolynomial_l2_bound_of_fibre (q : ℕ) [NeZero q]
    (s : Finset ℕ) (c : ℕ → ℂ) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ a : ZMod q, ((charResidueFibre q s a).card : ℝ) ≤ M) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ s, c n * χ n‖ ^ 2 ≤
      (q.totient : ℝ) * M * ∑ n ∈ s, ‖c n‖ ^ 2 := by
  rw [charPolynomial_parseval]
  calc
    _ ≤ (q.totient : ℝ) *
        ∑ a : ZMod q with IsUnit a, M * ∑ n ∈ charResidueFibre q s a, ‖c n‖ ^ 2 := by
      gcongr with a ha
      exact (finite_sum_norm_sq_le _ c).trans
        (mul_le_mul_of_nonneg_right (hM a) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    _ ≤ (q.totient : ℝ) *
        ∑ a : ZMod q, M * ∑ n ∈ charResidueFibre q s a, ‖c n‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q.totient)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => mul_nonneg hM0 (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    _ = _ := by
      unfold charResidueFibre
      rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _)]
      ring

theorem charResidueFibre_card_le (q : ℕ) [NeZero q] (N : ℕ)
    (s : Finset ℕ) (hs : ∀ n ∈ s, n ≤ N) (a : ZMod q) :
    (charResidueFibre q s a).card ≤ N / q + 1 := by
  have h := Finset.card_le_card_of_injOn (s := charResidueFibre q s a)
    (t := Finset.range (N / q + 1)) (fun n : ℕ => n / q) ?_ ?_
  · simpa using h
  · intro n hn
    have hn' := (Finset.mem_filter.mp hn).1
    have hd : n / q ≤ N / q := Nat.div_le_div_right (hs n hn')
    simpa only [Finset.mem_coe, Finset.mem_range] using Nat.lt_succ_of_le hd
  · intro n hn m hm hdiv
    change n / q = m / q at hdiv
    have hn' := (Finset.mem_filter.mp hn).2
    have hm' := (Finset.mem_filter.mp hm).2
    have hmod : n % q = m % q := by
      simpa only [ZMod.val_natCast] using congrArg ZMod.val (hn'.trans hm'.symm)
    have hn := Nat.mod_add_div n q
    have hm := Nat.mod_add_div m q
    rw [hmod, hdiv] at hn
    omega

theorem charPolynomial_l2_bound_nat (q : ℕ) [NeZero q] (N : ℕ) (c : ℕ → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ Finset.Icc 1 N, c n * χ n‖ ^ 2 ≤
      (q.totient : ℝ) * (1 + (N : ℝ) / q) *
        ∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 := by
  apply charPolynomial_l2_bound_of_fibre q (Finset.Icc 1 N) c _ (by positivity)
  intro a
  have h := charResidueFibre_card_le q N (Finset.Icc 1 N)
    (fun _ hn => (Finset.mem_Icc.mp hn).2) a
  have hc : ((charResidueFibre q (Finset.Icc 1 N) a).card : ℝ) ≤ (N / q : ℕ) + 1 :=
    by exact_mod_cast h
  exact hc.trans (by have hdiv := Nat.cast_div_le (α := ℝ) (m := N) (n := q); linarith)

theorem charPolynomial_l2_bound (q : ℕ) [NeZero q] (X : ℝ) (hX : 0 ≤ X)
    (c : ℕ → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, c n * χ n‖ ^ 2 ≤
      (q.totient : ℝ) * (1 + X / q) *
        ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ‖c n‖ ^ 2 := by
  apply (charPolynomial_l2_bound_nat q ⌊X⌋₊ c).trans
  gcongr
  exact Nat.floor_le hX

end
end Sechstmoment.Source
