import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Sechstmoment.Numerator.V.Arithmetic.Additive.GCD

/-! Finite evaluation of the actual principal Gauss sum, including modulus
one. The proof uses complete additive sums, gcd grouping and Mobius inversion. -/

namespace Sechstmoment.Source
open Complex Real ZMod Finset ArithmeticFunction
open scoped BigOperators Classical
noncomputable section

theorem sum_range_cast_zmod (q : ℕ) [NeZero q] (f : ZMod q → ℂ) :
    (∑ n ∈ Finset.range q, f (n:ZMod q)) = ∑ x : ZMod q, f x := by
  apply Finset.sum_bij (fun (n : ℕ) (_hn : n ∈ Finset.range q) => (n:ZMod q))
  · intro _ _
    exact Finset.mem_univ _
  · intro n hn m hm he
    have H := congrArg ZMod.val he
    simpa only [ZMod.val_natCast_of_lt (Finset.mem_range.mp hn),
      ZMod.val_natCast_of_lt (Finset.mem_range.mp hm)] using H
  · intro x _
    exact ⟨x.val,Finset.mem_range.mpr x.val_lt,by simp⟩
  · intro _ _
    rfl

theorem sum_Icc_cast_zmod (q : ℕ) [NeZero q] (f : ZMod q → ℂ) :
    (∑ n ∈ Finset.Icc 1 q, f (n:ZMod q)) = ∑ x : ZMod q, f x := by
  have he : (∑ n ∈ Finset.Icc 1 q, f (n:ZMod q)) =
      ∑ k ∈ Finset.range q, f ((1+k:ℕ):ZMod q) := by
    apply Finset.sum_bij (fun n _ => n-1)
    · intro n hn
      simp only [Finset.mem_range]
      have H := Finset.mem_Icc.mp hn
      omega
    · intro n hn m hm he
      have Hn := Finset.mem_Icc.mp hn
      have Hm := Finset.mem_Icc.mp hm
      omega
    · intro k hk
      refine ⟨k+1,Finset.mem_Icc.mpr ⟨by omega,by have H := Finset.mem_range.mp hk; omega⟩,?_⟩
      omega
    · intro n hn
      have H := Finset.mem_Icc.mp hn
      have hn' : 1+(n-1) = n := by omega
      rw [hn']
  rw [he]
  simp only [Nat.cast_add,Nat.cast_one]
  rw [sum_range_cast_zmod q (fun x => f (1+x))]
  exact Equiv.sum_comp (Equiv.addLeft (1:ZMod q)) f

theorem complete_dirichlet_character_sum (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    (∑ n ∈ Finset.Icc 1 q, χ (n:ZMod q)) = if χ = 1 then (q.totient:ℂ) else 0 := by
  rw [sum_Icc_cast_zmod]
  by_cases hχ : χ = 1
  · subst χ
    rw [ite_eq_left rfl,MulChar.sum_one_eq_card_units,ZMod.card_units_eq_totient]
  · rw [ite_eq_right hχ]
    exact MulChar.sum_eq_zero_of_ne_one hχ

theorem complete_natural_additive_sum (N : ℕ) [NeZero N] :
    (∑ n ∈ Finset.Icc 1 N, naturalAdditivePhase N n) = if N = 1 then 1 else 0 := by
  simp_rw [naturalAdditivePhase_eq_std]
  rw [sum_Icc_cast_zmod N (fun x => stdAddChar (-x))]
  by_cases hN : N = 1
  · subst N
    have he (x : ZMod 1) : (stdAddChar (-x) : ℂ) = 1 := by
      rw [show -x = 0 from Subsingleton.elim _ _]
      simp
    simp_rw [he]
    norm_num
  · have hneg : (-1:ZMod N) ≠ 0 := by
      intro he
      have hdiv : N ∣ 1 := (CharP.cast_eq_zero_iff (ZMod N) N 1).mp (by
        simpa only [Nat.cast_one,neg_eq_zero] using he)
      exact hN (Nat.dvd_one.mp hdiv)
    have H := AddChar.sum_mulShift (-1:ZMod N) (isPrimitive_stdAddChar N)
    simpa only [mul_neg_one,ite_eq_right hneg,ite_eq_right hN,Nat.cast_zero] using H

def principalGaussAF : ArithmeticFunction ℂ :=
  ⟨fun n => if hn : n = 0 then 0 else
      letI : NeZero n := ⟨hn⟩
      gaussSum (1 : DirichletCharacter ℂ n) stdAddChar,
    by simp⟩

theorem principalGaussAF_apply (q : ℕ) [NeZero q] :
    principalGaussAF q = gaussSum (1 : DirichletCharacter ℂ q) stdAddChar := by
  simp only [principalGaussAF,ArithmeticFunction.coe_mk,dite_eq_right (NeZero.ne q)]

theorem principalGaussAF_divisor_sum (N : ℕ) [NeZero N] :
    (∑ q ∈ N.divisors, principalGaussAF q) = if N = 1 then 1 else 0 := by
  have H := additive_interval_character_decomposition N N (fun _ => (1:ℂ))
  simp only [one_mul,complete_natural_additive_sum] at H
  have hblock (d : ℕ) (hd : d ∈ N.divisors) :
      additiveDirichletBlock N d N (fun _ => (1:ℂ)) = principalGaussAF (N/d) := by
    have hdpos := Nat.pos_of_mem_divisors hd
    have hq : 0 < N/d := Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) (Nat.mem_divisors.mp hd).1) hdpos
    let : NeZero (N/d) := ⟨hq.ne'⟩
    have hφ : ((N/d).totient:ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq).ne'
    have hone : (1 : DirichletCharacter ℂ (N/d)) (-1) = 1 := by
      simpa using (MulChar.one_apply_coe (-1:(ZMod (N/d))ˣ) :
        (1 : DirichletCharacter ℂ (N/d)) ((-1:(ZMod (N/d))ˣ):ZMod (N/d)) = 1)
    rw [principalGaussAF_apply]
    simp only [additiveDirichletBlock,dite_eq_right hq.ne',one_mul]
    have hsum :
        (∑ χ : DirichletCharacter ℂ (N/d), gaussSum χ⁻¹ stdAddChar*χ (-1)*
          (∑ n ∈ Finset.Icc 1 (N/d), χ n)) =
        gaussSum (1 : DirichletCharacter ℂ (N/d)) stdAddChar*((N/d).totient:ℂ) := by
      calc
        _ = gaussSum (1 : DirichletCharacter ℂ (N/d))⁻¹ stdAddChar*
            (1 : DirichletCharacter ℂ (N/d)) (-1)*
              (∑ n ∈ Finset.Icc 1 (N/d), (1 : DirichletCharacter ℂ (N/d)) n) := by
          apply Finset.sum_eq_single (1 : DirichletCharacter ℂ (N/d))
          · intro χ _ hχ
            rw [complete_dirichlet_character_sum,ite_eq_right hχ,mul_zero]
          · simp
        _ = _ := by rw [complete_dirichlet_character_sum,ite_eq_left rfl,inv_one,hone,mul_one]
    rw [hsum]
    field_simp [hφ]
  have hquot : (∑ d ∈ N.divisors, principalGaussAF (N/d)) = if N = 1 then 1 else 0 := by
    rw [H]
    exact Finset.sum_congr rfl (fun d hd => (hblock d hd).symm)
  have hswap : (∑ d ∈ N.divisors, principalGaussAF (N/d)) =
      ∑ q ∈ N.divisors, principalGaussAF q := by
    rw [← Nat.sum_divisorsAntidiagonal (fun _ q => principalGaussAF q),
      Nat.sum_divisorsAntidiagonal' (fun _ q => principalGaussAF q)]
  exact hswap.symm.trans hquot

theorem principal_gaussSum_eq_moebius (q : ℕ) [NeZero q] :
    gaussSum (1 : DirichletCharacter ℂ q) stdAddChar = (ArithmeticFunction.moebius q:ℂ) := by
  have hconv : (ArithmeticFunction.zeta:ArithmeticFunction ℂ)*principalGaussAF = 1 := by
    ext n
    by_cases hn : n = 0
    · subst n
      simp
    · let : NeZero n := ⟨hn⟩
      rw [ArithmeticFunction.coe_zeta_mul_apply,principalGaussAF_divisor_sum]
      simp only [ArithmeticFunction.one_apply]
  have hAF : principalGaussAF = (ArithmeticFunction.moebius:ArithmeticFunction ℂ) := by
    calc
      _ = (ArithmeticFunction.moebius:ArithmeticFunction ℂ)*
          ((ArithmeticFunction.zeta:ArithmeticFunction ℂ)*principalGaussAF) := by
        rw [← mul_assoc,ArithmeticFunction.coe_moebius_mul_coe_zeta,one_mul]
      _ = _ := by rw [hconv,mul_one]
  rw [← principalGaussAF_apply,hAF]
  rfl

end
end Sechstmoment.Source
