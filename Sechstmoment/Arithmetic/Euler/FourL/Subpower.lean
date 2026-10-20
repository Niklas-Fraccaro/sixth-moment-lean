import Sechstmoment.Arithmetic.Divisors.Subpower
import Sechstmoment.Arithmetic.Euler.FourL.CoefficientFactorization

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Sechstmoment.Source.NoDPGlobalLFactorization
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest NoDPGlobalConvolution
open scoped BigOperators
noncomputable section

theorem cubicHeight_majorant (h : ℕ) : 32*cubicHeight h ≤ (24*((h:ℝ)+1))^3 := by
  unfold cubicHeight
  calc
    _ ≤ 64*((h:ℝ)+6)^3 := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = (4*((h:ℝ)+6))^3 := by ring
    _ ≤ _ := pow_le_pow_left₀ (by positivity)
      (by have := Nat.cast_nonneg (α := ℝ) h; linarith) 3

theorem local_height_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 →
      (∏ p ∈ n.primeFactors, 32*cubicHeight (n.factorization p)) ≤ C*(n:ℝ)^ε := by
  obtain ⟨D,hD,hbound⟩ := divisor_prime_cost_subpower (ε := ε/3) (C := 24) (by linarith) (by norm_num)
  refine ⟨(D+1)^3,by positivity,?_⟩
  intro n hn
  have H : (n.divisors.card:ℝ)*24^n.primeFactors.card ≤ (D+1)*(n:ℝ)^(ε/3) :=
    (hbound n hn).trans (by gcongr; linarith)
  calc
    _ ≤ ∏ p ∈ n.primeFactors, (24*((n.factorization p:ℝ)+1))^3 :=
      Finset.prod_le_prod₀ (fun _ _ => by unfold cubicHeight; positivity)
        (fun p _ => cubicHeight_majorant (n.factorization p))
    _ = ((n.divisors.card:ℝ)*24^n.primeFactors.card)^3 := by
      rw [Finset.prod_pow,Finset.prod_mul_distrib,Finset.prod_const]
      rw [Nat.card_divisors hn,Nat.cast_prod]
      simp only [Nat.cast_add,Nat.cast_one]
      ring
    _ ≤ ((D+1)*(n:ℝ)^(ε/3))^3 := pow_le_pow_left₀ (by positivity) H 3
    _ = _ := by
      have Heq : ((n:ℝ)^(ε/3))^3 = (n:ℝ)^ε := by
        rw [← Real.rpow_natCast _ 3,← Real.rpow_mul (Nat.cast_nonneg n)]
        congr 1
        norm_num
      rw [mul_pow,Heq]

theorem primeScale_product (n : ℕ) (hn : n ≠ 0) (ρ : ℝ) :
    (∏ p ∈ n.primeFactors, (primeScale p ρ)^(n.factorization p)) = (n:ℝ)^ρ := by
  unfold primeScale
  have H (p : ℕ) : ((p:ℝ)^ρ)^(n.factorization p) = ((p:ℝ)^(n.factorization p))^ρ := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (Nat.cast_nonneg p),
      ← Real.rpow_natCast,← Real.rpow_mul (Nat.cast_nonneg p)]
    rw [mul_comm]
  simp_rw [H]
  rw [Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
  congr 1
  exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm

theorem correction_power_bound (n : ℕ) (hn : n ≠ 0) (s : Fin 4 → ℂ) (u : ℕ → ℂ)
    (hu : ∀ p ∈ n.primeFactors, ‖u p‖ ≤ 1) (ρ : ℝ) (_hρ : 0 ≤ ρ)
    (hs : ∀ j, ‖s j‖ ≤ ρ) (z : ℂ) (hz : ρ ≤ z.re) :
    ‖arithmeticCorrection n s u z‖ ≤
      (∏ p ∈ n.primeFactors, 32*cubicHeight (n.factorization p)) * (n:ℝ)^ρ := by
  have hregion (p : ℕ) (hp : p ∈ n.primeFactors) :
      primeScale p ρ * ‖eulerParameter p (u p) z‖ ≤ 1 := by
    have hprime := Nat.prime_of_mem_primeFactors hp
    rw [eulerParameter,norm_mul]
    calc
      _ ≤ primeScale p ρ * (1*‖(p:ℂ)^(-z)‖) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hu p hp) (norm_nonneg _))
          (Real.rpow_nonneg (Nat.cast_nonneg p) ρ)
      _ = (p:ℝ)^(ρ-z.re) := by
        rw [one_mul,Complex.norm_natCast_cpow_of_pos hprime.pos,Complex.neg_re]
        exact (Real.rpow_add (by exact_mod_cast hprime.pos) ρ (-z.re)).symm
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast hprime.one_le) (by linarith)
  have H := arithmeticCorrection_bound n hn s u z (fun p => primeScale p ρ)
    (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) ρ)
    (fun p hp => primeRoot_bound p (Nat.prime_of_mem_primeFactors hp) _ ρ (hs 0))
    (fun p hp => primeRoot_bound p (Nat.prime_of_mem_primeFactors hp) _ ρ (hs 1))
    (fun p hp => primeRoot_bound p (Nat.prime_of_mem_primeFactors hp) _ ρ (hs 2))
    (fun p hp => primeRoot_bound p (Nat.prime_of_mem_primeFactors hp) _ ρ (hs 3)) hregion
  apply H.trans_eq
  rw [Finset.prod_mul_distrib,primeScale_product n hn ρ]

theorem arithmeticCorrection_subpower (κ ε : ℝ) (hκ : 0 < κ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 → ∀ s : Fin 4 → ℂ,
      (∀ j, ‖s j‖ ≤ min κ (ε/2)) → ∀ u : ℕ → ℂ,
      (∀ p ∈ n.primeFactors, ‖u p‖ ≤ 1) → ∀ z : ℂ, κ ≤ z.re →
        ‖arithmeticCorrection n s u z‖ ≤ C*(n:ℝ)^ε := by
  obtain ⟨C,hC,hcost⟩ := local_height_subpower (ε/2) (by linarith)
  refine ⟨C,hC,?_⟩
  intro n hn s hs u hu z hz
  have hδ : 0 ≤ min κ (ε/2) := le_min hκ.le (by linarith)
  calc
    _ ≤ (∏ p ∈ n.primeFactors,32*cubicHeight (n.factorization p)) * (n:ℝ)^(min κ (ε/2)) :=
      correction_power_bound n hn s u hu _ hδ hs z ((min_le_left _ _).trans hz)
    _ ≤ (C*(n:ℝ)^(ε/2)) * (n:ℝ)^(min κ (ε/2)) :=
      mul_le_mul_of_nonneg_right (hcost n hn) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = C*(n:ℝ)^(ε/2+min κ (ε/2)) := by
      rw [mul_assoc,← Real.rpow_add (by exact_mod_cast Nat.pos_of_ne_zero hn)]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
        (by have := min_le_right κ (ε/2); linarith)

end
end Sechstmoment.Source.NoDPGlobalLFactorization
