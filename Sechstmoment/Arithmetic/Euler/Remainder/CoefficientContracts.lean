import Sechstmoment.Arithmetic.Euler.Remainder.Configurations

/-! Normalization, exact prime-power coefficients, and the global support restriction. -/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Sechstmoment.Source.NoDPGlobalRest
open NoDPLocal NoDPResidues NoDPLocalClosure
open scoped BigOperators
noncomputable section

theorem leftDegree_le_two (j : Fin 8) : leftDegree j ≤ 2 := by
  fin_cases j <;> decide

theorem rightDegree_le_two (j : Fin 8) : rightDegree j ≤ 2 := by
  fin_cases j <;> decide

def emptyConfiguration : Configuration := ⟨∅, fun p => False.elim (Finset.notMem_empty _ p.property)⟩
def primeConfiguration (p : Nat.Primes) (j : Fin 8) : Configuration := ⟨{p}, fun _ => j⟩

theorem emptyConfiguration_index : configIndex emptyConfiguration = (1,1) := by
  simp [configIndex, configLeft, configRight, emptyConfiguration]

theorem gamma_one_one (s : Fin 4 → ℂ) : gamma s (1,1) = 1 := by
  rw [← emptyConfiguration_index, gamma_config]
  apply Finset.prod_eq_one
  intro p _
  exact False.elim (Finset.notMem_empty p.val p.property)

theorem primeConfiguration_index (p : Nat.Primes) (j : Fin 8) :
    configIndex (primeConfiguration p j) = (p.val^leftDegree j, p.val^rightDegree j) := by
  apply Prod.ext
  · exact (Finset.prod_coe_sort ({p} : Finset Nat.Primes)
      (fun q => q.val ^ leftDegree j)).trans (Finset.prod_singleton _ _)
  · exact (Finset.prod_coe_sort ({p} : Finset Nat.Primes)
      (fun q => q.val ^ rightDegree j)).trans (Finset.prod_singleton _ _)

theorem gamma_prime_choice (s : Fin 4 → ℂ) (p : Nat.Primes) (j : Fin 8) :
    gamma s (p.val^leftDegree j, p.val^rightDegree j) = localCoeff p s j := by
  rw [← primeConfiguration_index, gamma_config]
  exact (Finset.prod_coe_sort ({p} : Finset Nat.Primes)
    (fun q => localCoeff q s j)).trans (Finset.prod_singleton _ _)

theorem config_degrees_le_two (c : Configuration) (p : Nat.Primes) :
    (configLeft c).factorization p.val ≤ 2 ∧ (configRight c).factorization p.val ≤ 2 := by
  by_cases hp : p ∈ c.1
  · rw [(config_factorization_mem c p hp).1, (config_factorization_mem c p hp).2]
    exact ⟨leftDegree_le_two _, rightDegree_le_two _⟩
  · rw [(config_factorization_not_mem c p hp).1, (config_factorization_not_mem c p hp).2]
    norm_num

theorem gamma_vanishes_high_degree (s : Fin 4 → ℂ) (n : ℕ × ℕ) (p : Nat.Primes)
    (hn : 3 ≤ n.1.factorization p.val ∨ 3 ≤ n.2.factorization p.val) : gamma s n = 0 := by
  apply gamma_outside
  rintro ⟨c, rfl⟩
  have H := config_degrees_le_two c p
  change 3 ≤ (configLeft c).factorization p.val ∨ 3 ≤ (configRight c).factorization p.val at hn
  omega

theorem gamma_nonzero_support (s : Fin 4 → ℂ) (n : ℕ × ℕ) (hn : gamma s n ≠ 0) :
    0 < n.1 ∧ 0 < n.2 ∧ ∀ p : Nat.Primes,
      n.1.factorization p.val ≤ 2 ∧ n.2.factorization p.val ≤ 2 := by
  have hr : n ∈ Set.range configIndex := by
    by_contra h
    exact hn (gamma_outside s n h)
  obtain ⟨c, rfl⟩ := hr
  exact ⟨configLeft_pos c, configRight_pos c, config_degrees_le_two c⟩

end
end Sechstmoment.Source.NoDPGlobalRest
