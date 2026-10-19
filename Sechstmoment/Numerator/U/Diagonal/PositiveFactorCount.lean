import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-!
# Actual averaged positive factor-pair counts

These are unconditional finite counting bounds. They supply the averaged
factor counts needed by the central near-resonant error strategy; they do
not assume or conclude an analytic moment estimate.
-/
namespace Sechstmoment
open scoped BigOperators

/-- The actual positive pairs whose product is at most P, enumerated by the
first factor and the exact integer quotient for the second factor. -/
def positiveProductFactorPairs (P : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 P).biUnion fun n => (Finset.Icc 1 (P/n)).image fun m => (n,m)

theorem mem_positiveProductFactorPairs {P n m : ℕ} :
    (n,m) ∈ positiveProductFactorPairs P ↔ 0<n ∧ 0<m ∧ n*m≤P := by
  constructor
  · intro hp
    obtain ⟨a,ha,hpa⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hpa
    have han : 0<a := by have hh := (Finset.mem_Icc.mp ha).1; omega
    have hbm : 0<b := by have hh := (Finset.mem_Icc.mp hb).1; omega
    have hdiv := (Finset.mem_Icc.mp hb).2
    have hmul := (Nat.le_div_iff_mul_le han).mp hdiv
    have he1 := (Prod.mk.inj he).1
    have he2 := (Prod.mk.inj he).2
    subst a
    subst b
    exact ⟨han,hbm,by simpa [Nat.mul_comm] using hmul⟩
  · rintro ⟨hn,hm,hprod⟩
    apply Finset.mem_biUnion.mpr
    have hnP : n≤P := by nlinarith
    refine ⟨n,Finset.mem_Icc.mpr ⟨by omega,hnP⟩,?_⟩
    apply Finset.mem_image.mpr
    refine ⟨m,Finset.mem_Icc.mpr ⟨by omega,?_⟩,rfl⟩
    exact (Nat.le_div_iff_mul_le hn).mpr (by simpa [Nat.mul_comm] using hprod)

/-- Disjoint first-factor fibers give the exact finite quotient count. -/
theorem positiveProductFactorPairs_card_eq_quotient_sum (P : ℕ) :
    (positiveProductFactorPairs P).card = ∑ n ∈ Finset.Icc 1 P, P/n := by
  have hd : (↑(Finset.Icc 1 P) : Set ℕ).PairwiseDisjoint
      (fun n => (Finset.Icc 1 (P/n)).image fun m => (n,m)) := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro p hpa hpb
    obtain ⟨u,hu,heu⟩ := Finset.mem_image.mp hpa
    obtain ⟨v,hv,hev⟩ := Finset.mem_image.mp hpb
    apply hab
    exact (Prod.mk.inj (heu.trans hev.symm)).1
  unfold positiveProductFactorPairs
  rw [Finset.card_biUnion hd]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.card_image_of_injective _ (by intro x y he; exact (Prod.mk.inj he).2)]
  simp [Nat.card_Icc]

/-- The exact integer-quotient sum bounds the actual enumeration. -/
theorem positiveProductFactorPairs_card_le_quotient_sum (P : ℕ) :
    (positiveProductFactorPairs P).card ≤ ∑ n ∈ Finset.Icc 1 P, P/n := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 P,
        ((Finset.Icc 1 (P/n)).image fun m => (n,m)).card := Finset.card_biUnion_le
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.card_image_of_injective _ (by intro x y he; exact (Prod.mk.inj he).2)]
      simp [Nat.card_Icc]

/-- Real-valued harmonic majorant for the exact quotient sum. -/
theorem positiveProductFactorPairs_card_le_harmonic (P : ℕ) :
    ((positiveProductFactorPairs P).card : ℝ) ≤ (P:ℝ)*(harmonic P : ℝ) := by
  have hcard := positiveProductFactorPairs_card_le_quotient_sum P
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 P, ((P/n : ℕ):ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ n ∈ Finset.Icc 1 P, (P:ℝ)/(n:ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0<n := by have hh := (Finset.mem_Icc.mp hn).1; omega
      have hprod : (P/n)*n ≤ P := Nat.div_mul_le_self P n
      have hnreal : (0:ℝ)<n := by exact_mod_cast hnpos
      apply (le_div_iff₀ hnreal).mpr
      exact_mod_cast hprod
    _ = (P:ℝ)*(harmonic P : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      exact div_eq_mul_inv _ _

/-- A true averaged divisor count, with no divisor-growth assumption. -/
theorem positiveProductFactorPairs_card_le_log (P : ℕ) :
    ((positiveProductFactorPairs P).card : ℝ) ≤ (P:ℝ)*(1+Real.log (P:ℝ)) := by
  exact (positiveProductFactorPairs_card_le_harmonic P).trans
    (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log P) (Nat.cast_nonneg P))

/-- The genuine reciprocal-product average is bounded by the square of the
harmonic sum, using the actual finite pairs rather than a divisor estimate. -/
theorem positiveProductFactorPairs_reciprocal_sum_le_harmonic_sq (P : ℕ) :
    (∑ p ∈ positiveProductFactorPairs P, 1/((p.1*p.2 : ℕ):ℝ)) ≤ (harmonic P : ℝ)^2 := by
  have hsub : positiveProductFactorPairs P ⊆ (Finset.Icc 1 P) ×ˢ (Finset.Icc 1 P) := by
    intro p hp
    have hb := mem_positiveProductFactorPairs.mp hp
    apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_Icc.mpr
    · exact ⟨by omega,by nlinarith [hb.1,hb.2.1,hb.2.2]⟩
    · exact ⟨by omega,by nlinarith [hb.1,hb.2.1,hb.2.2]⟩
  have hH : (harmonic P : ℝ) = ∑ n ∈ Finset.Icc 1 P, (n:ℝ)⁻¹ := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  calc
    _ ≤ ∑ p ∈ (Finset.Icc 1 P) ×ˢ (Finset.Icc 1 P), 1/((p.1*p.2 : ℕ):ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    _ = _ := by
      rw [Finset.sum_product]
      simp only [Nat.cast_mul,one_div,mul_inv]
      rw [← Finset.sum_mul_sum,← hH]
      ring

theorem positiveProductFactorPairs_reciprocal_sum_le_log_sq (P : ℕ) :
    (∑ p ∈ positiveProductFactorPairs P, 1/((p.1*p.2 : ℕ):ℝ)) ≤
      (1+Real.log (P:ℝ))^2 := by
  have hH : 0 ≤ (harmonic P : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hbound := harmonic_le_one_add_log P
  exact (positiveProductFactorPairs_reciprocal_sum_le_harmonic_sq P).trans (by nlinarith)

end Sechstmoment
