import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

/-! The elementary mean value of the explicit 2-adic loss in SALT's Estermann bound. -/
namespace DivisorProof
open Finset
open scoped BigOperators
noncomputable section

abbrev twoAdicWeight (n : ℕ) : ℝ := Real.sqrt ((2 : ℝ) ^ n.factorization 2)

theorem twoAdicWeight_nonneg (n : ℕ) : 0 ≤ twoAdicWeight n :=
  Real.sqrt_nonneg _

theorem twoAdicWeight_of_odd {n : ℕ} (hn : ¬ 2 ∣ n) : twoAdicWeight n = 1 := by
  simp [twoAdicWeight, Nat.factorization_eq_zero_of_not_dvd hn]

theorem twoAdicWeight_two_mul {n : ℕ} (hn : n ≠ 0) :
    twoAdicWeight (2*n) = Real.sqrt 2 * twoAdicWeight n := by
  have he : (2*n).factorization 2 = 1+n.factorization 2 := by
    rw [Nat.factorization_mul (by decide) hn]
    simp [Nat.prime_two.factorization_self]
  simp [twoAdicWeight, he, pow_add, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]

/-- Exact reindexing of positive multiples; zero is deliberately excluded. -/
theorem sum_positive_multiples_eq (F : ℕ → ℝ) (N : ℕ) {d : ℕ} (hd : 0 < d) :
    (∑ w ∈ (Icc 1 N).filter (fun w => d ∣ w), F (w/d)) =
      ∑ c ∈ Icc 1 (N/d), F c := by
  apply Finset.sum_bij (fun w _ => w/d)
  · intro w hw
    obtain ⟨hw,hdw⟩ := mem_filter.mp hw
    exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (mem_Icc.mp hw).1 hdw) hd,
      Nat.div_le_div_right (mem_Icc.mp hw).2⟩
  · intro w hw v hv heq
    have hw' := (mem_filter.mp hw).2
    have hv' := (mem_filter.mp hv).2
    calc w = (w/d)*d := (Nat.div_mul_cancel hw').symm
      _ = (v/d)*d := by rw [heq]
      _ = v := Nat.div_mul_cancel hv'
  · intro c hc
    refine ⟨c*d, mem_filter.mpr ⟨mem_Icc.mpr ⟨?_,?_
      ⟩,dvd_mul_left d c⟩,Nat.mul_div_cancel c hd⟩
    · exact Nat.mul_pos (mem_Icc.mp hc).1 hd
    · exact (Nat.mul_le_mul_right d (mem_Icc.mp hc).2).trans (Nat.div_mul_le_self N d)
  · intro w _
    rfl

/-- The explicit 2-adic factor has an absolute mean value, with constant four. -/
theorem twoAdicWeight_sum_le (N : ℕ) :
    (∑ n ∈ Icc 1 N, twoAdicWeight n) ≤ 4*(N : ℝ) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hN : N = 0
    · simp [hN]
    have hhalf : N/2 < N := Nat.div_lt_self (Nat.pos_of_ne_zero hN) (by decide)
    have hs := ih (N/2) hhalf
    have heven :
        (∑ n ∈ (Icc 1 N).filter (fun n => 2 ∣ n), twoAdicWeight n) =
          Real.sqrt 2 * ∑ n ∈ Icc 1 (N/2), twoAdicWeight n := by
      calc _ = ∑ n ∈ (Icc 1 N).filter (fun n => 2 ∣ n),
          Real.sqrt 2 * twoAdicWeight (n/2) := by
            apply sum_congr rfl
            intro n hn
            obtain ⟨hn,hd⟩ := mem_filter.mp hn
            have hp : 0 < n/2 := Nat.div_pos (Nat.le_of_dvd (mem_Icc.mp hn).1 hd) (by decide)
            conv_lhs => rw [← Nat.mul_div_cancel' hd]
            exact twoAdicWeight_two_mul hp.ne'
        _ = _ := by rw [← mul_sum, sum_positive_multiples_eq _ _ (by decide : 0 < 2)]
    have hodd :
        (∑ n ∈ (Icc 1 N).filter (fun n => ¬ 2 ∣ n), twoAdicWeight n) ≤ (N : ℝ) := by
      calc _ = ∑ n ∈ (Icc 1 N).filter (fun n => ¬ 2 ∣ n), (1 : ℝ) := by
            apply sum_congr rfl
            intro n hn
            exact twoAdicWeight_of_odd (mem_filter.mp hn).2
        _ = (((Icc 1 N).filter (fun n => ¬ 2 ∣ n)).card : ℝ) := by simp
        _ ≤ ((Icc 1 N).card : ℝ) := by exact_mod_cast card_filter_le (Icc 1 N) _
        _ = N := by simp
    have hdiv : (N/2 : ℕ)*2 ≤ N := Nat.div_mul_le_self N 2
    have hdivr : (N/2 : ℕ) ≤ (N : ℝ)/2 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      exact_mod_cast hdiv
    have hsqrt : Real.sqrt 2 ≤ (3/2 : ℝ) := by
      apply (Real.sqrt_le_iff).mpr
      norm_num
    rw [← Finset.sum_filter_add_sum_filter_not (Icc 1 N) (fun n => 2 ∣ n), heven]
    calc _ ≤ Real.sqrt 2 * (4*(N/2 : ℕ)) + (N : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)) hodd
      _ ≤ (3/2 : ℝ)*(4*((N : ℝ)/2))+(N : ℝ) := by gcongr
      _ = _ := by ring

theorem twoAdicWeight_multiple_sum_le (N : ℕ) {d : ℕ} (hd : 0 < d) :
    (∑ w ∈ (Icc 1 N).filter (fun w => d ∣ w), twoAdicWeight (w/d)) ≤
      4*(N : ℝ)/(d : ℝ) := by
  rw [sum_positive_multiples_eq _ _ hd]
  apply (twoAdicWeight_sum_le (N/d)).trans
  have hdiv : (N/d)*d ≤ N := Nat.div_mul_le_self N d
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  apply (le_div_iff₀ hdr).mpr
  have hh : ((N/d : ℕ) : ℝ)*(d : ℝ) ≤ N := by exact_mod_cast hdiv
  nlinarith

theorem twoAdicWeight_sum_le_real {Y : ℝ} (hY : 0 ≤ Y) :
    (∑ n ∈ Icc 1 ⌊Y⌋₊, twoAdicWeight n) ≤ 4*Y :=
  (twoAdicWeight_sum_le _).trans (by gcongr; exact Nat.floor_le hY)

/-- The 2-adic loss disappears on averaging over the modulus, with the full `1/d` saving. -/
theorem estermann_product_multiple_sum_le {W M : ℝ} (hW : 0 < W) (hM : 0 ≤ M)
    {d : ℕ} (hd : 0 < d) :
    (∑ w ∈ (Icc 1 ⌊4*W⌋₊).filter (fun w : ℕ => W ≤ (w:ℝ) ∧ d ∣ w),
      twoAdicWeight (w/d)*(w:ℝ)^(1/2:ℝ)*(1+M/(w:ℝ))) ≤
        32*W^(1/2:ℝ)*(W+M)/(d:ℝ) := by
  let s := (Icc 1 ⌊4*W⌋₊).filter (fun w : ℕ => W ≤ (w:ℝ) ∧ d ∣ w)
  have hsub : s ⊆ (Icc 1 ⌊4*W⌋₊).filter (fun w => d ∣ w) := by
    intro w hw
    exact mem_filter.mpr ⟨(mem_filter.mp hw).1,(mem_filter.mp hw).2.2⟩
  have hc : (∑ w ∈ s, twoAdicWeight (w/d)) ≤ 16*W/(d:ℝ) := by
    calc _ ≤ ∑ w ∈ (Icc 1 ⌊4*W⌋₊).filter (fun w => d ∣ w), twoAdicWeight (w/d) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun w _ _ => twoAdicWeight_nonneg _)
      _ ≤ 4*(⌊4*W⌋₊:ℝ)/(d:ℝ) := twoAdicWeight_multiple_sum_le _ hd
      _ ≤ _ := by
        have hh := Nat.floor_le (by positivity : 0 ≤ 4*W)
        exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  have hb (w : ℕ) (hw : w ∈ s) :
      (w:ℝ)^(1/2:ℝ)*(1+M/(w:ℝ)) ≤ 2*W^(1/2:ℝ)*(1+M/W) := by
    obtain ⟨hwr,hWw,_⟩ := mem_filter.mp hw
    have hwp : (0:ℝ) < w := hW.trans_le hWw
    have hwupper : (w:ℝ) ≤ 4*W :=
      (show (w:ℝ) ≤ (⌊4*W⌋₊:ℝ) by exact_mod_cast (mem_Icc.mp hwr).2).trans
        (Nat.floor_le (by positivity))
    have hroot : (w:ℝ)^(1/2:ℝ) ≤ 2*W^(1/2:ℝ) := by
      apply (Real.rpow_le_rpow hwp.le hwupper (by norm_num : (0:ℝ) ≤ 1/2)).trans_eq
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hW.le]
      norm_num [← Real.sqrt_eq_rpow]
    exact mul_le_mul hroot (add_le_add le_rfl (div_le_div_of_nonneg_left hM hW hWw))
      (by positivity) (by positivity)
  change ∑ w ∈ s, twoAdicWeight (w/d)*(w:ℝ)^(1/2:ℝ)*(1+M/(w:ℝ)) ≤ _
  calc _ = ∑ w ∈ s, twoAdicWeight (w/d)*((w:ℝ)^(1/2:ℝ)*(1+M/(w:ℝ))) := by
        apply sum_congr rfl; intro w _; ring
    _ ≤ ∑ w ∈ s, twoAdicWeight (w/d)*(2*W^(1/2:ℝ)*(1+M/W)) :=
      sum_le_sum (fun w hw => mul_le_mul_of_nonneg_left (hb w hw) (twoAdicWeight_nonneg _))
    _ = (∑ w ∈ s, twoAdicWeight (w/d))*(2*W^(1/2:ℝ)*(1+M/W)) := by rw [sum_mul]
    _ ≤ (16*W/(d:ℝ))*(2*W^(1/2:ℝ)*(1+M/W)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by field_simp; norm_num

end
end DivisorProof
