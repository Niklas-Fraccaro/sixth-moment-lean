import Sechstmoment.Numerator.U.Separation.PairCoefficientBounds


namespace Sechstmoment
open ArithmeticFunction Nat Complex
open scoped BigOperators
open Classical

set_option maxHeartbeats 0
noncomputable section

def bblrBPrimeFactorAt (p : ℕ) (α β γ δ s : ℂ) (ν : ℕ) : ℂ :=
  (∑' j : ℕ, shiftedPairArithmetic α β (p^j)*
    shiftedPairArithmetic γ δ (p^(j+ν))*((p:ℂ)^(-(1+2*s)))^j) /
  (∑' j : ℕ, shiftedPairArithmetic α β (p^j)*
    shiftedPairArithmetic γ δ (p^j)*((p:ℂ)^(-(1+2*s)))^j)

def bblrBFactorAt (α β γ δ s : ℂ) (a : ℕ) : ℂ :=
  a.factorization.prod fun p ν => bblrBPrimeFactorAt p α β γ δ s ν

theorem bblrBPrimeFactorAt_zero (p : ℕ) (α β γ δ : ℂ) (ν : ℕ) :
    bblrBPrimeFactorAt p α β γ δ 0 ν = bblrBPrimeFactor p α β γ δ ν := by
  simp only [bblrBPrimeFactorAt, bblrBPrimeFactor, mul_zero, add_zero,
    Complex.cpow_neg_one, one_div]

theorem bblrBPrimeFactor_add_shifts {p : ℕ} (hp : p.Prime)
    (α β γ δ s : ℂ) (ν : ℕ) :
    bblrBPrimeFactor p (α+s) (β+s) (γ+s) (δ+s) ν =
      ((p:ℂ)^(-s))^ν*bblrBPrimeFactorAt p α β γ δ s ν := by
  have hp0 : (p:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hweight : (p:ℂ)^(-s)*(p:ℂ)^(-s)*(1/(p:ℂ))=(p:ℂ)^(-(1+2*s)) := by
    rw [one_div, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hp0,
      ← Complex.cpow_add _ _ hp0]
    congr 1
    ring
  have hterm (j k : ℕ) :
      shiftedPairArithmetic (α+s) (β+s) (p^j)*
        shiftedPairArithmetic (γ+s) (δ+s) (p^(j+k))*(1/(p:ℂ))^j =
      ((p:ℂ)^(-s))^k*(shiftedPairArithmetic α β (p^j)*
        shiftedPairArithmetic γ δ (p^(j+k))*((p:ℂ)^(-(1+2*s)))^j) := by
    rw [shiftedPairArithmetic_add_shifts, shiftedPairArithmetic_add_shifts,
      ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply,
      shiftedPowerArithmetic_primePower hp, shiftedPowerArithmetic_primePower hp,
      ← hweight, pow_add, mul_pow, mul_pow]
    ring
  unfold bblrBPrimeFactor bblrBPrimeFactorAt
  simp_rw [hterm]
  rw [tsum_mul_left]
  have hterm₀ (j : ℕ) : shiftedPairArithmetic (α+s) (β+s) (p^j)*
      shiftedPairArithmetic (γ+s) (δ+s) (p^j)*(1/(p:ℂ))^j =
      shiftedPairArithmetic α β (p^j)*shiftedPairArithmetic γ δ (p^j)*
        ((p:ℂ)^(-(1+2*s)))^j := by
    simpa only [Nat.add_zero, pow_zero, one_mul] using hterm j 0
  simp_rw [hterm₀]
  ring

theorem bblrBFactor_add_shifts (α β γ δ s : ℂ) {a : ℕ} (ha : a ≠ 0) :
    bblrBFactor (α+s) (β+s) (γ+s) (δ+s) a =
      (a:ℂ)^(-s)*bblrBFactorAt α β γ δ s a := by
  have hp := (shiftedPowerArithmetic_multiplicative s).multiplicative_factorization
    (shiftedPowerArithmetic s) ha
  rw [shiftedPowerArithmetic_apply s ha] at hp
  rw [hp]
  unfold bblrBFactor bblrBFactorAt Finsupp.prod
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  dsimp only
  have hprime := Nat.prime_of_mem_primeFactors hp
  rw [bblrBPrimeFactor_add_shifts hprime, shiftedPowerArithmetic_primePower hprime]

theorem shiftedPairCorrelation_add_shifts (α β γ δ s : ℂ) {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    (∑' n : ℕ, shiftedPairArithmetic (α+s) (β+s) (b*n)*
      shiftedPairArithmetic (γ+s) (δ+s) (a*n)*shiftedPowerArithmetic 1 n) =
    (a*b:ℕ)^(-s)*∑' n : ℕ, shiftedPairArithmetic α β (b*n)*
      shiftedPairArithmetic γ δ (a*n)*shiftedPowerArithmetic (1+2*s) n := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · simp [hn]
  rw [shiftedPairArithmetic_add_shifts, shiftedPairArithmetic_add_shifts,
    ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply]
  rw [shiftedPowerArithmetic_apply _ hn,
    shiftedPowerArithmetic_apply _ (mul_ne_zero ha hn),
    shiftedPowerArithmetic_apply _ (mul_ne_zero hb hn), shiftedPowerArithmetic_apply _ hn]
  simp only [Nat.cast_mul]
  rw [Complex.natCast_mul_natCast_cpow, Complex.natCast_mul_natCast_cpow,
    Complex.natCast_mul_natCast_cpow]
  have hn0 : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have he : (n:ℂ)^(-s)*(n:ℂ)^(-s)*(n:ℂ)^(-1:ℂ)=(n:ℂ)^(-(1+2*s)) := by
    rw [← Complex.cpow_add _ _ hn0, ← Complex.cpow_add _ _ hn0]
    congr 1
    ring
  calc
    _ = (a:ℂ)^(-s)*(b:ℂ)^(-s)*shiftedPairArithmetic α β (b*n)*
      shiftedPairArithmetic γ δ (a*n)*((n:ℂ)^(-s)*(n:ℂ)^(-s)*(n:ℂ)^(-1:ℂ)) := by ring
    _ = _ := by rw [he]; ring

end
end Sechstmoment
