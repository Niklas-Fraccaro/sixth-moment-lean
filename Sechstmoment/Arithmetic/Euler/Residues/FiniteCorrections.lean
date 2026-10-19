import Sechstmoment.Arithmetic.Euler.Residues.HolomorphicCorrections

/-!
# Finite Euler corrections
The series below is a product of genuine convergent local series. No global
Dirichlet-L identification is asserted by this module.
-/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
namespace Sechstmoment.Source.NoDPResidues
open NoDPLocal Finset
open scoped BigOperators

noncomputable def finiteCorrection (P : Finset ℕ) (shifts : Fin 4 → ℂ)
    (u : ℕ → ℂ) (h : ℕ → ℕ) (s : ℂ) : ℂ := ∏ p ∈ P, primeCorrection p shifts (u p) (h p) s
noncomputable def finiteDenominator (P : Finset ℕ) (shifts : Fin 4 → ℂ)
    (u : ℕ → ℂ) (s : ℂ) : ℂ := ∏ p ∈ P,
  denom (primeRoot p (shifts 0)) (primeRoot p (shifts 1))
    (primeRoot p (shifts 2)) (primeRoot p (shifts 3)) (eulerParameter p (u p) s)
noncomputable def finiteSeries (P : Finset ℕ) (shifts : Fin 4 → ℂ)
    (u : ℕ → ℂ) (h : ℕ → ℕ) (s : ℂ) : ℂ := ∏ p ∈ P,
  localSeries (primeRoot p (shifts 0)) (primeRoot p (shifts 1))
    (primeRoot p (shifts 2)) (primeRoot p (shifts 3)) (eulerParameter p (u p) s) (h p)

@[simp] theorem finiteCorrection_empty (shifts : Fin 4 → ℂ) (u : ℕ → ℂ) (h : ℕ → ℕ) (s : ℂ) :
    finiteCorrection ∅ shifts u h s = 1 := by simp [finiteCorrection]

theorem finiteCorrection_insert (P : Finset ℕ) (p : ℕ) (hp : p ∉ P)
    (shifts : Fin 4 → ℂ) (u : ℕ → ℂ) (h : ℕ → ℕ) (s : ℂ) :
    finiteCorrection (insert p P) shifts u h s =
      primeCorrection p shifts (u p) (h p) s*finiteCorrection P shifts u h s := by
  simp [finiteCorrection, hp]

theorem finiteCorrection_union (P Q : Finset ℕ) (hPQ : Disjoint P Q)
    (shifts : Fin 4 → ℂ) (u : ℕ → ℂ) (h : ℕ → ℕ) (s : ℂ) :
    finiteCorrection (P ∪ Q) shifts u h s = finiteCorrection P shifts u h s*finiteCorrection Q shifts u h s := by
  exact Finset.prod_union hPQ

@[simp] theorem primeCorrection_base (p : ℕ) (shifts : Fin 4 → ℂ) (u s : ℂ) :
    primeCorrection p shifts u 0 s = 1 := by simp [primeCorrection, numerator_base]

@[simp] theorem primeCorrection_ramified (p : ℕ) (shifts : Fin 4 → ℂ) (h : ℕ) (s : ℂ) :
    primeCorrection p shifts 0 h s = shiftedPrimeCoeff p shifts h := by
  simp [primeCorrection, eulerParameter, shiftedPrimeCoeff]

theorem finiteCorrection_zero_exponents (P : Finset ℕ) (shifts : Fin 4 → ℂ)
    (u : ℕ → ℂ) (h : ℕ → ℕ) (hh : ∀ p ∈ P, h p = 0) (s : ℂ) :
    finiteCorrection P shifts u h s = 1 := by
  unfold finiteCorrection
  apply Finset.prod_eq_one
  intro p hp
  rw [hh p hp, primeCorrection_base]

theorem finiteCorrection_ramified (P : Finset ℕ) (shifts : Fin 4 → ℂ)
    (u : ℕ → ℂ) (hu : ∀ p ∈ P, u p = 0) (h : ℕ → ℕ) (s : ℂ) :
    finiteCorrection P shifts u h s = ∏ p ∈ P, shiftedPrimeCoeff p shifts (h p) := by
  unfold finiteCorrection
  apply Finset.prod_congr rfl
  intro p hp
  rw [hu p hp, primeCorrection_ramified]

theorem finiteCorrection_congr (P : Finset ℕ) (shifts : Fin 4 → ℂ)
    (u v : ℕ → ℂ) (h k : ℕ → ℕ) (hu : ∀ p ∈ P, u p = v p)
    (hh : ∀ p ∈ P, h p = k p) (s : ℂ) :
    finiteCorrection P shifts u h s = finiteCorrection P shifts v k s := by
  unfold finiteCorrection
  apply Finset.prod_congr rfl
  intro p hp
  rw [hu p hp, hh p hp]

theorem finiteCorrection_entire (P : Finset ℕ) (hP : ∀ p ∈ P, p ≠ 0)
    (shifts : Fin 4 → ℂ) (u : ℕ → ℂ) (h : ℕ → ℕ) :
    Differentiable ℂ (finiteCorrection P shifts u h) := by
  apply Differentiable.fun_finsetProd
  intro p hp
  exact primeCorrection_entire p (hP p hp) shifts (u p) (h p)

theorem finiteCorrection_continuous (P : Finset ℕ) (hP : ∀ p ∈ P, p ≠ 0)
    (shifts : Fin 4 → ℂ) (u : ℕ → ℂ) (h : ℕ → ℕ) :
    Continuous (finiteCorrection P shifts u h) := (finiteCorrection_entire P hP shifts u h).continuous

theorem finiteCorrection_norm (P : Finset ℕ) (shifts : Fin 4 → ℂ)
    (u : ℕ → ℂ) (h : ℕ → ℕ) (s : ℂ) :
    ‖finiteCorrection P shifts u h s‖ = ∏ p ∈ P, ‖primeCorrection p shifts (u p) (h p) s‖ := by
  simp [finiteCorrection, norm_prod]

section Region
variable (P : Finset ℕ) (shifts : Fin 4 → ℂ) (u : ℕ → ℂ) (h : ℕ → ℕ) (s : ℂ)
  (r : ℕ → ℝ) (hr : ∀ p ∈ P, 0 ≤ r p)
  (ha : ∀ p ∈ P, ‖primeRoot p (shifts 0)‖ ≤ r p)
  (hb : ∀ p ∈ P, ‖primeRoot p (shifts 1)‖ ≤ r p)
  (hc : ∀ p ∈ P, ‖primeRoot p (shifts 2)‖ ≤ r p)
  (hd : ∀ p ∈ P, ‖primeRoot p (shifts 3)‖ ≤ r p)
include hr ha hb hc hd

theorem finiteCorrection_bound (ht : ∀ p ∈ P, r p*‖eulerParameter p (u p) s‖ ≤ 1) :
    ‖finiteCorrection P shifts u h s‖ ≤ ∏ p ∈ P, 32*cubicHeight (h p)*(r p)^(h p) := by
  rw [finiteCorrection_norm]
  apply Finset.prod_le_prod₀ (fun p _ => norm_nonneg _)
  intro p hp
  exact numerator_unit_bound _ _ _ _ _ _ (hr p hp) (ha p hp) (hb p hp) (hc p hp) (hd p hp) (ht p hp) (h p)

theorem finiteDenominator_ne_zero (ht : ∀ p ∈ P, r p*‖eulerParameter p (u p) s‖ < 1) :
    finiteDenominator P shifts u s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact denom_norm_region_ne_zero _ _ _ _ _ _ (ha p hp) (hb p hp) (hc p hp) (hd p hp) (ht p hp)

theorem finiteEuler_factorization (ht : ∀ p ∈ P, r p*‖eulerParameter p (u p) s‖ < 1) :
    finiteDenominator P shifts u s*finiteSeries P shifts u h s = finiteCorrection P shifts u h s := by
  unfold finiteDenominator finiteSeries finiteCorrection primeCorrection
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  exact local_series_factorization _ _ _ _ _ _ (hr p hp) (ha p hp) (hb p hp) (hc p hp) (hd p hp) (ht p hp) (h p)

theorem finiteEuler_rational (ht : ∀ p ∈ P, r p*‖eulerParameter p (u p) s‖ < 1) :
    finiteSeries P shifts u h s = finiteCorrection P shifts u h s/finiteDenominator P shifts u s := by
  apply (eq_div_iff (finiteDenominator_ne_zero P shifts u s r hr ha hb hc hd ht)).2
  simpa only [mul_comm] using finiteEuler_factorization P shifts u h s r hr ha hb hc hd ht

end Region

theorem finiteDenominator_entire (P : Finset ℕ) (hP : ∀ p ∈ P, p ≠ 0)
    (shifts : Fin 4 → ℂ) (u : ℕ → ℂ) : Differentiable ℂ (finiteDenominator P shifts u) := by
  apply Differentiable.fun_finsetProd
  intro p hp
  have ht := eulerParameter_entire p (hP p hp) (u p)
  unfold denom
  fun_prop

end Sechstmoment.Source.NoDPResidues
