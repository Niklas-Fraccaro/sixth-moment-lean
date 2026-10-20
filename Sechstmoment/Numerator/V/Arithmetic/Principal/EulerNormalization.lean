import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Sechstmoment.Arithmetic.Euler.FourL.Continuation


namespace Sechstmoment.Source.NoDPGlobalLFactorization
open Complex Finset
open scoped BigOperators
noncomputable section

theorem principal_regularizedL_one_mul_modulus (q : ℕ) [NeZero q] :
    (q:ℂ)*DirichletCharacter.LFunctionTrivChar₁ q 1 = (q.totient:ℂ) := by
  classical
  let P : ℂ := ∏ p ∈ q.primeFactors, (p:ℂ)
  let B : ℂ := ∏ p ∈ q.primeFactors, ((p-1:ℕ):ℂ)
  have hP : P ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hEuler : (∏ p ∈ q.primeFactors, (1-(p:ℂ)⁻¹)) = B/P := by
    dsimp only [B,P]
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp1 := (Nat.prime_of_mem_primeFactors hp).one_le
    have hp0 : (p:ℂ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    rw [Nat.cast_sub hp1,Nat.cast_one]
    field_simp [hp0]
  have hNat : (q.totient:ℂ)*P = (q:ℂ)*B := by
    simpa only [P,B,Nat.cast_mul,Nat.cast_prod] using
      congrArg (fun n : ℕ => (n:ℂ)) (Nat.totient_mul_prod_primeFactors q)
  rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_self,hEuler]
  calc
    _ = ((q:ℂ)*B)/P := by ring
    _ = ((q.totient:ℂ)*P)/P := by rw [hNat]
    _ = _ := mul_div_cancel_right₀ _ hP

theorem principal_regularizedL_one_totient_normalization (q : ℕ) [NeZero q] :
    (q.totient:ℂ)⁻¹*DirichletCharacter.LFunctionTrivChar₁ q 1 = (q:ℂ)⁻¹ := by
  have hq : (q:ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hφ : (q.totient:ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  have hval : DirichletCharacter.LFunctionTrivChar₁ q 1 = (q.totient:ℂ)/(q:ℂ) := by
    apply (eq_div_iff hq).mpr
    simpa only [mul_comm] using principal_regularizedL_one_mul_modulus q
  rw [hval]
  field_simp [hq,hφ]

end
end Sechstmoment.Source.NoDPGlobalLFactorization
