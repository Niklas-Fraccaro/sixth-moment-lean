import Sechstmoment.Arithmetic.Watt.Statement

/-! The zero frequency in Poisson completion is bounded arithmetically.
The proof uses prime-power descent and CRT, not an unproved Weil estimate. -/

namespace DivisorProof
namespace Watt41
open Real Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

theorem ramanujan_prime_power {p : ℕ} [Fact p.Prime] :
    ∀ e : ℕ, 1 ≤ e → ∀ A : ℕ,
      ‖Salt.Weil.kloosterman (A : ZMod (p^e)) 0‖ ≤ (Nat.gcd (p^e) A : ℝ) := by
  have hp : p.Prime := Fact.out
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro he A
    have : NeZero (p^e) := ⟨pow_ne_zero _ hp.ne_zero⟩
    by_cases hA : p ∣ A
    · cases e with
      | zero => omega
      | succ f =>
        by_cases hf : f = 0
        · subst f
          have hg : Nat.gcd (p^1) A = p := by simpa using Nat.gcd_eq_left hA
          rw [hg]
          have h := Salt.Weil.norm_kloosterman_le_modulus (A : ZMod (p^1)) 0
          simpa only [pow_one, Nat.cast_id] using h
        · obtain ⟨A', hA'⟩ := hA
          have hf' : 1 ≤ f := by omega
          have hpow : p^(f+1) = p*p^f := by rw [pow_succ]; ring
          have hg : Nat.gcd (p^(f+1)) A = p*Nat.gcd (p^f) A' := by
            rw [hpow, hA', Nat.gcd_mul_left]
          have hdesc := Salt.Weil.kloosterman_descent (p := p) (f := f) hf' A' 0
          have hbound := ih f (by omega) hf' A'
          have hdesc' : Salt.Weil.kloosterman (A : ZMod (p^(f+1))) 0 =
              (p : ℂ)*Salt.Weil.kloosterman (A' : ZMod (p^f)) 0 := by
            simpa only [hA',mul_zero,Nat.cast_zero] using hdesc
          rw [hdesc', norm_mul, Complex.norm_natCast, hg, Nat.cast_mul]
          exact mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg p)
    · have hunit : IsUnit (A : ZMod (p^e)) :=
        (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega)).mpr hA
      have hbound := Salt.Weil.norm_kloosterman_zero_right_prime_pow he hunit
      have hg : (1 : ℝ) ≤ (Nat.gcd (p^e) A : ℝ) := by
        exact_mod_cast Nat.gcd_pos_of_pos_left A (pow_pos hp.pos e)
      exact hbound.trans hg

theorem gcd_unit_multiple {n : ℕ} [NeZero n] {l : ZMod n} (hl : IsUnit l) (A : ℕ) :
    Nat.gcd n (l.val*A) = Nat.gcd n A := by
  obtain ⟨u, rfl⟩ := hl
  have hcop : ((u : ZMod n).val).Coprime n := ZMod.val_coe_unit_coprime u
  rw [Nat.gcd_comm n, Nat.mul_comm, hcop.gcd_mul_right_cancel, Nat.gcd_comm A]

/-- The global Ramanujan bound for arbitrary positive moduli, in SALT's convention. -/
theorem ramanujan_nat (c : ℕ) [NeZero c] (A : ℕ) :
    ‖Salt.Weil.kloosterman (A : ZMod c) 0‖ ≤ (Nat.gcd c A : ℝ) := by
  have key : ∀ c : ℕ, ∀ [NeZero c], ∀ A : ℕ,
      ‖Salt.Weil.kloosterman (A : ZMod c) 0‖ ≤ (Nat.gcd c A : ℝ) := by
    intro c
    refine Nat.recOnPosPrimePosCoprime
      (motive := fun c => ∀ [NeZero c], ∀ A : ℕ,
        ‖Salt.Weil.kloosterman (A : ZMod c) 0‖ ≤ (Nat.gcd c A : ℝ)) ?_ ?_ ?_ ?_ c
    · intro p e hp he _ A
      have : Fact p.Prime := ⟨hp⟩
      exact ramanujan_prime_power e he A
    · intro hz A
      exact absurd rfl hz.out
    · intro _ A
      exact (Salt.Weil.norm_kloosterman_le_modulus (A : ZMod 1) 0).trans (by simp)
    · intro c₁ c₂ hc₁ hc₂ hcop ih₁ ih₂ _ A
      have : NeZero c₁ := ⟨by omega⟩
      have : NeZero c₂ := ⟨by omega⟩
      obtain ⟨l₁,l₂,hl₁,hl₂,hmul⟩ := Salt.Weil.kloosterman_mul_of_coprime_unit_twist
        hcop (A : ZMod (c₁*c₂)) 0
      have hnat₁ : l₁*(A : ZMod c₁) = ((l₁.val*A : ℕ) : ZMod c₁) := by
        simp only [Nat.cast_mul, ZMod.natCast_zmod_val]
      have hnat₂ : l₂*(A : ZMod c₂) = ((l₂.val*A : ℕ) : ZMod c₂) := by
        simp only [Nat.cast_mul, ZMod.natCast_zmod_val]
      rw [hmul, Salt.Weil.natCast_chineseRemainder_fst,
        Salt.Weil.natCast_chineseRemainder_snd]
      simp only [map_zero, Prod.fst_zero, Prod.snd_zero, mul_zero]
      rw [hnat₁,hnat₂,norm_mul]
      have h₁ : ‖Salt.Weil.kloosterman ((l₁.val*A : ℕ) : ZMod c₁) 0‖ ≤
          (Nat.gcd c₁ A : ℝ) := by
        simpa only [gcd_unit_multiple hl₁ A] using ih₁ (l₁.val*A)
      have h₂ : ‖Salt.Weil.kloosterman ((l₂.val*A : ℕ) : ZMod c₂) 0‖ ≤
          (Nat.gcd c₂ A : ℝ) := by
        simpa only [gcd_unit_multiple hl₂ A] using ih₂ (l₂.val*A)
      apply (mul_le_mul h₁ h₂ (norm_nonneg _) (Nat.cast_nonneg _)).trans
      have hgd : Nat.gcd c₁ A*Nat.gcd c₂ A ∣ Nat.gcd (c₁*c₂) A := by
        refine Nat.dvd_gcd
          (Nat.mul_dvd_mul (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)) ?_
        refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_
          (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _)
        exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _)
          (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left _ _) hcop)
      have hle := Nat.le_of_dvd (Nat.gcd_pos_of_pos_left A (by positivity : 0 < c₁*c₂)) hgd
      exact_mod_cast hle
  exact key c A

/-- The zero-frequency bound in the original integer-parameter convention. -/
theorem ramanujan_bound {c : ℕ} (hc : 0 < c) (m : ℤ) :
    ‖classicalKloostermanSum m 0 c‖ ≤ (Nat.gcd m.natAbs c : ℝ) := by
  let : NeZero c := ⟨hc.ne'⟩
  unfold classicalKloostermanSum
  rw [kloostermanSum_eq_salt hc, Salt.Weil.kloosterman_comm]
  have h := ramanujan_nat c (m : ZMod c).val
  simpa only [ZMod.natCast_zmod_val, Nat.cast_zero, Nat.gcd_comm c,
    gcd_zmod_intCast_val, Int.cast_zero] using h

end
end Watt41
end DivisorProof
