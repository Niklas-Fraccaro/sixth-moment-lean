import Sechstmoment.Arithmetic.Euler.Residues.PrimePowerCoefficients

/-! The finite correction indexed by an integer and its genuine local series. -/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
namespace Sechstmoment.Source.NoDPResidues
open NoDPLocal Finset
open scoped BigOperators
noncomputable def arithmeticCorrection (n : ℕ) (shifts : Fin 4 → ℂ) (u : ℕ → ℂ) (s : ℂ) : ℂ :=
  eulerCoeff (fun p k => primeCorrection p shifts (u p) k s) n

@[simp] theorem arithmeticCorrection_zero (shifts : Fin 4 → ℂ) (u : ℕ → ℂ) (s : ℂ) :
    arithmeticCorrection 0 shifts u s = 0 := by simp [arithmeticCorrection]
@[simp] theorem arithmeticCorrection_one (shifts : Fin 4 → ℂ) (u : ℕ → ℂ) (s : ℂ) :
    arithmeticCorrection 1 shifts u s = 1 := by simp [arithmeticCorrection]

theorem arithmeticCorrection_eq_finite (n : ℕ) (hn : n ≠ 0) (shifts : Fin 4 → ℂ) (u : ℕ → ℂ) (s : ℂ) :
    arithmeticCorrection n shifts u s = finiteCorrection n.primeFactors shifts u n.factorization s := by
  rw [arithmeticCorrection, eulerCoeff_nonzero _ n hn]
  rfl

theorem arithmeticCorrection_prime_pow (p : ℕ) (hp : p.Prime) (k : ℕ)
    (shifts : Fin 4 → ℂ) (u : ℕ → ℂ) (s : ℂ) :
    arithmeticCorrection (p^k) shifts u s = primeCorrection p shifts (u p) k s :=
  eulerCoeff_prime_pow _ (fun p => primeCorrection_base p shifts (u p) s) p hp k

theorem arithmeticCorrection_coprime (m n : ℕ) (hmn : m.Coprime n)
    (shifts : Fin 4 → ℂ) (u : ℕ → ℂ) (s : ℂ) :
    arithmeticCorrection (m*n) shifts u s = arithmeticCorrection m shifts u s*arithmeticCorrection n shifts u s :=
  eulerCoeff_coprime _ m n hmn

theorem arithmeticCorrection_entire (n : ℕ) (shifts : Fin 4 → ℂ) (u : ℕ → ℂ) :
    Differentiable ℂ (arithmeticCorrection n shifts u) := by
  by_cases hn : n = 0
  · subst n
    change Differentiable ℂ (fun _ : ℂ => (0:ℂ))
    exact differentiable_const 0
  have H : arithmeticCorrection n shifts u = finiteCorrection n.primeFactors shifts u n.factorization :=
    funext (arithmeticCorrection_eq_finite n hn shifts u)
  rw [H]
  exact finiteCorrection_entire _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero) shifts u _

theorem arithmeticCorrection_continuous (n : ℕ) (shifts : Fin 4 → ℂ) (u : ℕ → ℂ) :
    Continuous (arithmeticCorrection n shifts u) := (arithmeticCorrection_entire n shifts u).continuous

theorem arithmeticCorrection_ramified (n : ℕ) (shifts : Fin 4 → ℂ) (u : ℕ → ℂ)
    (hu : ∀ p ∈ n.primeFactors, u p = 0) (s : ℂ) :
    arithmeticCorrection n shifts u s = shiftedCoeff shifts n := by
  by_cases hn : n = 0
  · simp [hn, arithmeticCorrection, shiftedCoeff]
  rw [arithmeticCorrection_eq_finite n hn shifts u s, finiteCorrection_ramified _ shifts u hu]
  exact (eulerCoeff_nonzero _ n hn).symm

theorem arithmeticCorrection_congr (n : ℕ) (shifts : Fin 4 → ℂ) (u v : ℕ → ℂ)
    (hu : ∀ p ∈ n.primeFactors, u p = v p) (s : ℂ) :
    arithmeticCorrection n shifts u s = arithmeticCorrection n shifts v s := by
  by_cases hn : n = 0
  · simp [hn]
  rw [arithmeticCorrection_eq_finite n hn, arithmeticCorrection_eq_finite n hn]
  exact finiteCorrection_congr _ shifts u v _ _ hu (fun _ _ => rfl) s

theorem arithmeticCorrection_norm (n : ℕ) (hn : n ≠ 0) (shifts : Fin 4 → ℂ) (u : ℕ → ℂ) (s : ℂ) :
    ‖arithmeticCorrection n shifts u s‖ = ∏ p ∈ n.primeFactors, ‖primeCorrection p shifts (u p) (n.factorization p) s‖ := by
  rw [arithmeticCorrection_eq_finite n hn, finiteCorrection_norm]

section Region
variable (n : ℕ) (hn : n ≠ 0) (shifts : Fin 4 → ℂ) (u : ℕ → ℂ) (s : ℂ) (r : ℕ → ℝ)
  (hr : ∀ p ∈ n.primeFactors, 0 ≤ r p)
  (ha : ∀ p ∈ n.primeFactors, ‖primeRoot p (shifts 0)‖ ≤ r p)
  (hb : ∀ p ∈ n.primeFactors, ‖primeRoot p (shifts 1)‖ ≤ r p)
  (hc : ∀ p ∈ n.primeFactors, ‖primeRoot p (shifts 2)‖ ≤ r p)
  (hd : ∀ p ∈ n.primeFactors, ‖primeRoot p (shifts 3)‖ ≤ r p)
include hn hr ha hb hc hd

theorem arithmeticCorrection_bound (ht : ∀ p ∈ n.primeFactors, r p*‖eulerParameter p (u p) s‖ ≤ 1) :
    ‖arithmeticCorrection n shifts u s‖ ≤ ∏ p ∈ n.primeFactors, 32*cubicHeight (n.factorization p)*(r p)^(n.factorization p) := by
  rw [arithmeticCorrection_eq_finite n hn]
  exact finiteCorrection_bound _ shifts u _ s r hr ha hb hc hd ht

theorem arithmeticSeries_factorization (ht : ∀ p ∈ n.primeFactors, r p*‖eulerParameter p (u p) s‖ < 1) :
    finiteDenominator n.primeFactors shifts u s*finiteSeries n.primeFactors shifts u n.factorization s =
      arithmeticCorrection n shifts u s := by
  rw [arithmeticCorrection_eq_finite n hn]
  exact finiteEuler_factorization _ shifts u _ s r hr ha hb hc hd ht

theorem arithmeticSeries_rational (ht : ∀ p ∈ n.primeFactors, r p*‖eulerParameter p (u p) s‖ < 1) :
    finiteSeries n.primeFactors shifts u n.factorization s =
      arithmeticCorrection n shifts u s/finiteDenominator n.primeFactors shifts u s := by
  rw [arithmeticCorrection_eq_finite n hn]
  exact finiteEuler_rational _ shifts u _ s r hr ha hb hc hd ht

theorem arithmeticDenominator_ne_zero (ht : ∀ p ∈ n.primeFactors, r p*‖eulerParameter p (u p) s‖ < 1) :
    finiteDenominator n.primeFactors shifts u s ≠ 0 :=
  finiteDenominator_ne_zero _ shifts u s r hr ha hb hc hd ht

end Region

theorem arithmeticCorrection_ambient (n : ℕ) (hn : n ≠ 0) (P : Finset ℕ)
    (hP : n.primeFactors ⊆ P) (shifts : Fin 4 → ℂ) (u : ℕ → ℂ) (s : ℂ) :
    finiteCorrection P shifts u n.factorization s = arithmeticCorrection n shifts u s := by
  rw [arithmeticCorrection_eq_finite n hn]
  unfold finiteCorrection
  symm
  apply Finset.prod_subset hP
  intro p _ hpn
  have hz : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hpn
  rw [hz, primeCorrection_base]

theorem arithmeticCorrection_ramified_independent (n : ℕ) (shifts : Fin 4 → ℂ) (u : ℕ → ℂ)
    (hu : ∀ p ∈ n.primeFactors, u p = 0) (s t : ℂ) :
    arithmeticCorrection n shifts u s = arithmeticCorrection n shifts u t := by
  rw [arithmeticCorrection_ramified n shifts u hu s, arithmeticCorrection_ramified n shifts u hu t]

end Sechstmoment.Source.NoDPResidues
