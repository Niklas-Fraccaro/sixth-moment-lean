import Sechstmoment.Arithmetic.Euler.FourL.CoefficientFactorization

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace Sechstmoment.Source.NoDPGlobalLFactorization
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest NoDPGlobalConvolution
open scoped BigOperators
noncomputable section
open Classical

abbrev CubicBox (D : Finset Nat.Primes) := D → Fin 4
def cubicValue (D : Finset Nat.Primes) (f : CubicBox D) : ℕ := primeProduct D (fun p => (f p).val)

theorem cubicValue_injective (D : Finset Nat.Primes) : Function.Injective (cubicValue D) := by
  intro f g h
  have H := primeProduct_injective D h
  funext p
  exact Fin.ext (congrFun H p)

theorem fixedEuler_cubic_value (A : Nat.Primes → ℕ → ℂ) (D : Finset Nat.Primes)
    (hA : ∀ p ∉ D, A p 0 = 1) (f : CubicBox D) :
    fixedEuler A D (cubicValue D f) = ∏ p : D, A p.val (f p).val := by
  rw [fixedEuler_ambient A D hA _ (show cubicValue D f ≠ 0 from (primeProduct_pos _ _).ne')
    D (fun _ h => h) (primeProduct_support _ _),← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro p _
  exact congrArg (A p.val) (primeProduct_factor_mem D (fun p => (f p).val) p.val p.property)

theorem fixedEuler_outside_cubic (A : Nat.Primes → ℕ → ℂ) (D : Finset Nat.Primes)
    (hA : ∀ p ∉ D, ∀ k, A p k = if k = 0 then 1 else 0)
    (hH : ∀ p ∈ D, ∀ k, 4 ≤ k → A p k = 0) (n : ℕ)
    (hN : n ∉ Set.range (cubicValue D)) : fixedEuler A D n = 0 := by
  by_cases hn : n = 0
  · simp [hn]
  by_contra hF
  have hprod : (∏ p ∈ D ∪ primeSupport n, A p (n.factorization p.val)) ≠ 0 := by
    simpa only [fixedEuler,ite_eq_right hn] using hF
  have hterm (p : Nat.Primes) (hp : p ∈ D ∪ primeSupport n) : A p (n.factorization p.val) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hprod p hp
  have hS : primeSupport n ⊆ D := by
    intro p hp
    by_contra hpD
    have H := hterm p (Finset.mem_union_right _ hp)
    have hf : n.factorization p.val ≠ 0 := Finsupp.mem_support_iff.mp ((mem_primeSupport n p).mp hp)
    rw [hA p hpD,ite_eq_right hf] at H
    exact H rfl
  have hsmall (p : D) : n.factorization p.val.val < 4 := by
    by_contra H
    exact hterm p.val (Finset.mem_union_left _ p.property)
      (hH p.val p.property _ (by omega))
  let f : CubicBox D := fun p => ⟨n.factorization p.val.val,hsmall p⟩
  apply hN
  exact ⟨f,primeProduct_factorization n hn D hS⟩

theorem cubicValue_cpow (D : Finset Nat.Primes) (f : CubicBox D) (z : ℂ) :
    (cubicValue D f : ℂ)^z = ∏ p : D, ((p.val.val:ℂ)^z)^(f p).val := by
  rw [cubicValue,primeProduct,nat_prod_cpow]
  apply Finset.prod_congr rfl
  intro p _
  rw [Nat.cast_pow,← Complex.natCast_cpow_natCast_mul,mul_comm,Complex.cpow_mul_nat]

theorem fixedEuler_dirichlet_hasSum (A : Nat.Primes → ℕ → ℂ) (D : Finset Nat.Primes)
    (hA : ∀ p ∉ D, ∀ k, A p k = if k = 0 then 1 else 0)
    (hH : ∀ p ∈ D, ∀ k, 4 ≤ k → A p k = 0) (z : ℂ) :
    HasSum (fun n => fixedEuler A D n * (n:ℂ)^(-z))
      (∏ p ∈ D, ∑ k : Fin 4, A p k.val * ((p.val:ℂ)^(-z))^k.val) := by
  have hout (n : ℕ) (hn : n ∉ Set.range (cubicValue D)) : fixedEuler A D n * (n:ℂ)^(-z) = 0 := by
    rw [fixedEuler_outside_cubic A D hA hH n hn,zero_mul]
  have Hsum : Summable (fun n => fixedEuler A D n * (n:ℂ)^(-z)) :=
    (cubicValue_injective D).summable_iff hout |>.mp Summable.of_finite
  convert Hsum.hasSum using 1
  have H := (cubicValue_injective D).tsum_eq (Function.support_subset_iff'.mpr hout)
  rw [← H,tsum_fintype]
  simp_rw [fixedEuler_cubic_value A D (fun p hp => by simpa using hA p hp 0),cubicValue_cpow,
    ← Finset.prod_mul_distrib]
  exact ((Fintype.prod_sum (fun p : D => fun k : Fin 4 => A p.val k.val *
    ((p.val.val:ℂ)^(-z))^k.val)).symm.trans
      (Finset.prod_coe_sort D (fun p => ∑ k : Fin 4, A p k.val * ((p.val:ℂ)^(-z))^k.val))).symm

theorem localNumerator_high (d : ℕ) (s : Fin 4 → ℂ) (u : ℕ →* ℂ)
    (p : Nat.Primes) (k : ℕ) (hk : 4 ≤ k) : localNumerator d s u p k = 0 := by
  obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hk
  rw [localNumerator,hm,Nat.add_comm 4 m,numeratorCoeff_high,zero_mul]

theorem correctionAF_hasSum (d : ℕ) (hd : d ≠ 0) (s : Fin 4 → ℂ) (u : ℕ →* ℂ) (z : ℂ) :
    HasSum (fun n => correctionAF d s u n * (n:ℂ)^(-z)) (arithmeticCorrection d s u z) := by
  have H := fixedEuler_dirichlet_hasSum (localNumerator d s u) (primeSupport d)
    (localNumerator_outside d s u) (fun p _ k hk => localNumerator_high d s u p k hk) z
  convert H using 1
  · rfl
  · rw [arithmeticCorrection_eq_finite d hd]
    unfold finiteCorrection primeCorrection eulerParameter
    rw [← Finset.prod_subtype_of_mem _ (fun p hp => Nat.prime_of_mem_primeFactors hp)]
    apply Finset.prod_congr rfl
    intro p _
    rw [← numeratorCoeff_evaluate]
    apply Finset.sum_congr rfl
    intro k _
    simp only [localNumerator,mul_pow]
    ring

end
end Sechstmoment.Source.NoDPGlobalLFactorization
