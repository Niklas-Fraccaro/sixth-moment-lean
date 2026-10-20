import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import SixthMoment.Numerator.U.ZeroModes.Arithmetic.GCDDirichlet


namespace SixthMoment
open ArithmeticFunction Nat Complex
open scoped BigOperators
open Classical
noncomputable section
set_option maxHeartbeats 0

def a03CoprimePowerArithmetic (q : ℕ) (t : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n.Coprime q then shiftedPowerArithmetic t n else 0,by simp⟩

def a03CoprimeZeta (q : ℕ) (t : ℂ) : ℂ :=
  ∑' n : ℕ, a03CoprimePowerArithmetic q t n

theorem a03CoprimePowerArithmetic_multiplicative (q : ℕ) (t : ℂ) :
    (a03CoprimePowerArithmetic q t).IsMultiplicative := by
  have hp := shiftedPowerArithmetic_multiplicative t
  constructor
  · simp [a03CoprimePowerArithmetic,hp.map_one]
  · intro m n hmn
    simp only [a03CoprimePowerArithmetic,ArithmeticFunction.coe_mk,
      Nat.coprime_mul_iff_left,hp.map_mul_of_coprime hmn]
    split_ifs <;> simp_all

theorem a03CoprimePowerArithmetic_norm_summable (q : ℕ) {t : ℂ} (ht : 1<t.re) :
    Summable (fun n : ℕ => ‖a03CoprimePowerArithmetic q t n‖) := by
  apply (shiftedPowerArithmetic_norm_summable ht).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  simp only [a03CoprimePowerArithmetic,ArithmeticFunction.coe_mk]
  split_ifs <;> simp

theorem a03CoprimePowerArithmetic_primePower {p : ℕ} (hp : p.Prime)
    (q : ℕ) (t : ℂ) (e : ℕ) :
    a03CoprimePowerArithmetic q t (p^e)=
      if p∣q then (if e=0 then 1 else 0) else ((p:ℂ)^(-t))^e := by
  by_cases he : e=0
  · subst e
    simp [a03CoprimePowerArithmetic,shiftedPowerArithmetic]
  have hcop : (p^e).Coprime q ↔ ¬p∣q :=
    (Nat.coprime_pow_left_iff (Nat.pos_of_ne_zero he) p q).trans hp.coprime_iff_not_dvd
  simp only [a03CoprimePowerArithmetic,ArithmeticFunction.coe_mk,hcop,
    shiftedPowerArithmetic_primePower hp]
  by_cases hpq : p∣q <;> simp [hpq,he]

theorem a03CoprimePowerArithmetic_primeSeries {p : ℕ} (hp : p.Prime)
    (q : ℕ) {t : ℂ} (ht : 1<t.re) :
    (∑' e : ℕ, a03CoprimePowerArithmetic q t (p^e))=
      if p∣q then 1 else (1-(p:ℂ)^(-t))⁻¹ := by
  simp_rw [a03CoprimePowerArithmetic_primePower hp]
  split_ifs
  · simp
  · exact tsum_geometric_of_norm_lt_one
      ((Complex.norm_prime_cpow_le_one_half ⟨p,hp⟩ ht).trans_lt (by norm_num))

theorem a03CoprimeZeta_euler_hasProd (q : ℕ) {t : ℂ} (ht : 1<t.re) :
    HasProd (fun p : Nat.Primes => if p.val∣q then 1 else (1-(p.val:ℂ)^(-t))⁻¹)
      (a03CoprimeZeta q t) := by
  have h := (a03CoprimePowerArithmetic_multiplicative q t).eulerProduct_hasProd
    (a03CoprimePowerArithmetic_norm_summable q ht)
  apply h.congr_fun
  intro p
  exact (a03CoprimePowerArithmetic_primeSeries p.property q ht).symm

theorem a03CoprimeZeta_eq_zeta_mul_primeProduct {q : ℕ} (hq : q≠0)
    {t : ℂ} (ht : 1<t.re) :
    a03CoprimeZeta q t=riemannZeta t*(∏ p∈q.primeFactors, (1-(p:ℂ)^(-t))) := by
  let S : Finset Nat.Primes := q.primeFactors.subtype (·∈{p : ℕ | Nat.Prime p})
  have hpq (p : Nat.Primes) : p∈S ↔ p.val∣q := by
    have hm := @Finset.mem_subtype ℕ (·∈{p : ℕ | Nat.Prime p}) inferInstance
      q.primeFactors ⟨p.val,p.property⟩
    have hdiv : p.val∈q.primeFactors ↔ p.val∣q := by
      rw [Nat.mem_primeFactors]
      exact ⟨fun h => h.2.1,fun h => ⟨p.property,h,hq⟩⟩
    exact hm.trans hdiv
  have h := (riemannZeta_eulerProduct_hasProd ht).congr_cofinite₀
    (s:=S) (g:=fun p : Nat.Primes => if p.val∣q then 1 else (1-(p.val:ℂ)^(-t))⁻¹)
    (fun p _ => inv_ne_zero (Complex.one_sub_prime_cpow_ne_zero p.property ht))
    (fun p hp => by rw [ite_eq_right (fun h => hp ((hpq p).mpr h))])
  have hnum : (∏ p∈S,if p.val∣q then (1:ℂ) else (1-(p.val:ℂ)^(-t))⁻¹)=1 := by
    apply Finset.prod_eq_one
    intro p hp
    rw [ite_eq_left ((hpq p).mp hp)]
  have hden : (∏ p∈S,(1-(p.val:ℂ)^(-t))⁻¹)⁻¹=
      ∏ p∈q.primeFactors, (1-(p:ℂ)^(-t)) := by
    rw [←Finset.prod_inv_distrib]
    simp only [inv_inv]
    exact Finset.prod_subtype_of_mem (s:=q.primeFactors)
      (fun p => (1-(p:ℂ)^(-t))) (fun p hp => Nat.prime_of_mem_primeFactors hp)
  rw [hnum,one_div,hden] at h
  exact (a03CoprimeZeta_euler_hasProd q ht).unique h

theorem a03CoprimeZeta_ne_zero {q : ℕ} (hq : q≠0) {t : ℂ} (ht : 1<t.re) :
    a03CoprimeZeta q t≠0 := by
  rw [a03CoprimeZeta_eq_zeta_mul_primeProduct hq ht]
  exact mul_ne_zero (riemannZeta_ne_zero_of_one_lt_re ht)
    (Finset.prod_ne_zero_iff.mpr (fun p hp =>
      Complex.one_sub_prime_cpow_ne_zero (Nat.prime_of_mem_primeFactors hp) ht))

end
end SixthMoment
