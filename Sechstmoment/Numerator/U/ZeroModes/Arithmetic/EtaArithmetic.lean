import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Sechstmoment.Numerator.U.Diagonal.DiagonalEulerCoefficients

/-! The finite arithmetic function in BBLR (23), defined by its divisor sum.
Its multiplicativity and prime-power evaluation are proved, rather than assumed
as a reconstruction contract. -/

namespace Sechstmoment
open ArithmeticFunction Nat
open scoped BigOperators

set_option maxHeartbeats 0

noncomputable def bblrEtaCorrection (p : ℕ) (x y z : ℂ) : ℂ :=
  (1-(p:ℂ)^(-(1+x)))*(1-(p:ℂ)^(-(1+y)))/(1-(p:ℂ)^(-(2+z)))

noncomputable def bblrEtaArithmetic (α β γ δ u v s : ℂ) : ArithmeticFunction ℂ :=
  shiftedPowerArithmetic (γ-δ+2*v+s) *
    ArithmeticFunction.prodPrimeFactors (fun p =>
      bblrEtaCorrection p (α-β+γ-δ+2*u+2*v+s)
        (γ-δ+2*v) (α-β+γ-δ+2*u+2*v))

theorem bblrEtaArithmetic_multiplicative (α β γ δ u v s : ℂ) :
    (bblrEtaArithmetic α β γ δ u v s).IsMultiplicative :=
  (shiftedPowerArithmetic_multiplicative _).mul
    (ArithmeticFunction.IsMultiplicative.prodPrimeFactors _)

/-- Literal divisor-sum definition (23), including the primes dividing `a / l`. -/
theorem bblrEtaArithmetic_apply (α β γ δ u v s : ℂ) {a : ℕ} (ha : a ≠ 0) :
    bblrEtaArithmetic α β γ δ u v s a =
      ∑ l ∈ a.divisors, (l:ℂ)^(-(γ-δ+2*v+s))*
        ∏ p ∈ (a/l).primeFactors,
          bblrEtaCorrection p (α-β+γ-δ+2*u+2*v+s)
            (γ-δ+2*v) (α-β+γ-δ+2*u+2*v) := by
  rw [bblrEtaArithmetic, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun l k => shiftedPowerArithmetic (γ-δ+2*v+s) l *
      ArithmeticFunction.prodPrimeFactors (fun p =>
        bblrEtaCorrection p (α-β+γ-δ+2*u+2*v+s)
          (γ-δ+2*v) (α-β+γ-δ+2*u+2*v)) k)]
  apply Finset.sum_congr rfl
  intro l hl
  have hl0 : l ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hl)
  have hq0 : a/l ≠ 0 := by
    have hdiv := Nat.dvd_of_mem_divisors hl
    exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ha) hdiv)
      (Nat.pos_of_ne_zero hl0))
  rw [shiftedPowerArithmetic_apply _ hl0, ArithmeticFunction.prodPrimeFactors_apply hq0]

theorem prodPrimeFactors_primePower {p : ℕ} (hp : p.Prime) (c : ℕ → ℂ) (k : ℕ) :
    ArithmeticFunction.prodPrimeFactors c (p^k) = if k=0 then 1 else c p := by
  by_cases hk : k=0
  · simp [hk, ArithmeticFunction.prodPrimeFactors]
  · rw [ArithmeticFunction.prodPrimeFactors_apply (pow_ne_zero _ hp.ne_zero),
      Nat.primeFactors_prime_pow hk hp]
    simp [hk]

/-- The geometric polynomial appearing in the prime-power specialization of (23). -/
def bblrEtaPrimePolynomial (r c : ℂ) (ν : ℕ) : ℂ :=
  r^ν + (∑ j ∈ Finset.range ν, r^j)*c

theorem bblrEtaArithmetic_primePower {p : ℕ} (hp : p.Prime)
    (α β γ δ u v s : ℂ) (ν : ℕ) :
    bblrEtaArithmetic α β γ δ u v s (p^ν) =
      bblrEtaPrimePolynomial ((p:ℂ)^(-(γ-δ+2*v+s)))
        (bblrEtaCorrection p (α-β+γ-δ+2*u+2*v+s)
          (γ-δ+2*v) (α-β+γ-δ+2*u+2*v)) ν := by
  rw [bblrEtaArithmetic, arithmeticConvolution_primePower hp]
  simp_rw [shiftedPowerArithmetic_primePower hp, prodPrimeFactors_primePower hp]
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self, ↓reduceIte, mul_one]
  unfold bblrEtaPrimePolynomial
  rw [Finset.sum_mul]
  rw [add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hlt := Finset.mem_range.mp hj
    rw [ite_eq_right (by omega)]

theorem bblrEtaPrimePolynomial_reflection (r c c' : ℂ) (hr : r ≠ 0)
    (hc : c-r*c'=1-r) (ν : ℕ) :
    bblrEtaPrimePolynomial r c ν = r^ν*bblrEtaPrimePolynomial r⁻¹ c' ν := by
  have hgeom : r^ν*(∑ j ∈ Finset.range ν, r⁻¹^j) =
      r*(∑ j ∈ Finset.range ν, r^j) := by
    induction ν with
    | zero => simp
    | succ ν ih =>
      rw [Finset.sum_range_succ, pow_succ, mul_add]
      rw [show r^ν*r*(r⁻¹)^ν=r by
        rw [inv_pow]; field_simp]
      rw [show r^ν*r*(∑ j ∈ Finset.range ν, r⁻¹^j)=
        r*(r^ν*(∑ j ∈ Finset.range ν, r⁻¹^j)) by ring, ih, geom_sum_succ]
      ring
  unfold bblrEtaPrimePolynomial
  rw [mul_add, inv_pow, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero ν hr), hgeom]
  have h := geom_sum_mul r ν
  linear_combination -h + (∑ j ∈ Finset.range ν, r^j)*hc

/-- A polynomial verification of the local reflection, with the common Euler
denominator explicit.  No equality of main terms appears among its premises. -/
theorem bblrEtaCorrection_reflection_algebra (r X Y Z X' Y' : ℂ)
    (hZ : 1-Z ≠ 0) (hX : r*X'=Y) (hY : r*Y'=X)
    (hXY : X*Y=r*Z) (hZ' : r*X'*Y'=Z) :
    (1-X)*(1-Y)/(1-Z)-r*((1-X')*(1-Y')/(1-Z))=1-r := by
  rw [← mul_div_assoc, ← sub_div]
  apply (div_eq_iff hZ).mpr
  linear_combination hXY - hZ' + hX + hY

theorem bblrEtaCorrection_reflection {p : ℕ} (hp : p.Prime)
    (α β γ δ s : ℂ) (hden : 1-(p:ℂ)^(-(2+(α-β+γ-δ))) ≠ 0) :
    bblrEtaCorrection p (α+γ+2*s) (γ-δ) (α-β+γ-δ) -
      (p:ℂ)^(-(β+γ+2*s))*
        bblrEtaCorrection p (-δ-β-2*s) (-β+α) (α-β+γ-δ) =
      1-(p:ℂ)^(-(β+γ+2*s)) := by
  have hp0 : (p:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  unfold bblrEtaCorrection
  apply bblrEtaCorrection_reflection_algebra _ _ _ _ _ _ hden
  · rw [← Complex.cpow_add _ _ hp0]
    congr 1
    ring
  · rw [← Complex.cpow_add _ _ hp0]
    congr 1
    ring
  · rw [← Complex.cpow_add _ _ hp0, ← Complex.cpow_add _ _ hp0]
    congr 1
    ring
  · rw [← Complex.cpow_add _ _ hp0, ← Complex.cpow_add _ _ hp0]
    congr 1
    ring

noncomputable def bblrNormalizedEtaArithmetic (α β γ δ s : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => shiftedPowerArithmetic (-(β+s)) n*
    bblrEtaArithmetic α β γ δ 0 0 (β+δ+2*s) n, by simp⟩

theorem bblrNormalizedEtaArithmetic_multiplicative (α β γ δ s : ℂ) :
    (bblrNormalizedEtaArithmetic α β γ δ s).IsMultiplicative := by
  have hp := shiftedPowerArithmetic_multiplicative (-(β+s))
  have he := bblrEtaArithmetic_multiplicative α β γ δ 0 0 (β+δ+2*s)
  constructor
  · simp only [bblrNormalizedEtaArithmetic, ArithmeticFunction.coe_mk]
    rw [hp.map_one, he.map_one, mul_one]
  · intro m n hmn
    simp only [bblrNormalizedEtaArithmetic, ArithmeticFunction.coe_mk]
    rw [hp.map_mul_of_coprime hmn, he.map_mul_of_coprime hmn]
    ring

theorem bblrNormalizedEtaArithmetic_apply (α β γ δ s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    bblrNormalizedEtaArithmetic α β γ δ s n =
      (n:ℂ)^(β+s)*bblrEtaArithmetic α β γ δ 0 0 (β+δ+2*s) n := by
  simp only [bblrNormalizedEtaArithmetic, ArithmeticFunction.coe_mk,
    shiftedPowerArithmetic_apply _ hn, neg_neg]

/-- Normalization of the finite prime polynomial in exactly the form (9) uses. -/
theorem bblrEtaPrimePolynomial_normalized (B C c : ℂ) (hB : B ≠ 0) (ν : ℕ) :
    B^ν*bblrEtaPrimePolynomial (C/B) c ν =
      C^ν+B*(∑ j ∈ Finset.range ν, C^j*B^(ν-1-j))*c := by
  unfold bblrEtaPrimePolynomial
  rw [mul_add, div_pow, mul_div_cancel₀ _ (pow_ne_zero ν hB)]
  rw [← mul_assoc, Finset.mul_sum, Finset.mul_sum]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjν : j<ν := Finset.mem_range.mp hj
  have he : ν=(ν-1-j)+j+1 := by omega
  rw [div_pow]
  nth_rw 1 [he]
  rw [pow_add, pow_add]
  field_simp

theorem bblrNormalizedEtaArithmetic_primePower {p : ℕ} (hp : p.Prime)
    (α β γ δ s : ℂ) (ν : ℕ) :
    bblrNormalizedEtaArithmetic α β γ δ s (p^ν) =
      ((p:ℂ)^(β+s))^ν*bblrEtaPrimePolynomial ((p:ℂ)^(-(β+γ+2*s)))
        (bblrEtaCorrection p (α+γ+2*s) (γ-δ) (α-β+γ-δ)) ν := by
  simp only [bblrNormalizedEtaArithmetic, ArithmeticFunction.coe_mk,
    shiftedPowerArithmetic_primePower hp, neg_neg, bblrEtaArithmetic_primePower hp,
    mul_zero, add_zero]
  have h₁ : γ-δ+(β+δ+2*s)=β+γ+2*s := by ring
  have h₂ : α-β+γ-δ+(β+δ+2*s)=α+γ+2*s := by ring
  rw [h₁,h₂]

/-- The all-`s` finite arithmetic reflection required for the main-term involution. -/
theorem bblrNormalizedEtaArithmetic_reflection (α β γ δ s : ℂ)
    (hden : ∀ p : ℕ, p.Prime → 1-(p:ℂ)^(-(2+(α-β+γ-δ))) ≠ 0) :
    bblrNormalizedEtaArithmetic α β γ δ s =
      bblrNormalizedEtaArithmetic (-δ) (-γ) (-β) (-α) (-s) := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (bblrNormalizedEtaArithmetic_multiplicative _ _ _ _ _) _
    (bblrNormalizedEtaArithmetic_multiplicative _ _ _ _ _)).mpr
  intro p ν hp
  rw [bblrNormalizedEtaArithmetic_primePower hp, bblrNormalizedEtaArithmetic_primePower hp]
  have hp0 : (p:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have he := bblrEtaPrimePolynomial_reflection ((p:ℂ)^(-(β+γ+2*s)))
    (bblrEtaCorrection p (α+γ+2*s) (γ-δ) (α-β+γ-δ))
    (bblrEtaCorrection p (-δ-β-2*s) (-β+α) (α-β+γ-δ))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl hp0))
    (bblrEtaCorrection_reflection hp α β γ δ s (hden p hp)) ν
  rw [he, ← mul_assoc, ← mul_pow, ← Complex.cpow_add _ _ hp0]
  have hpow : β+s + -(β+γ+2*s)= -γ + -s := by ring
  rw [hpow]
  congr 1
  congr 1
  · rw [← Complex.cpow_neg]
    congr 1
    ring
  · have h₁ : -δ+-β+2*(-s)=-δ-β-2*s := by ring
    have h₂ : -β- -α=-β+α := by ring
    have h₃ : -δ- -γ+-β- -α=α-β+γ-δ := by ring
    rw [h₁,h₂,h₃]

end Sechstmoment
