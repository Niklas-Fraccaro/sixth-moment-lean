import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.LSeries.Convolution
import Sechstmoment.Arithmetic.Euler.Shifted.Rest

/-! The actual shifted triple Dirichlet coefficients, as multiplicative arithmetic functions. -/

namespace Sechstmoment
open ArithmeticFunction Nat
open scoped BigOperators

set_option maxHeartbeats 0

noncomputable def shiftedPowerArithmetic (a : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n=0 then 0 else (n:ℂ)^(-a), by simp⟩

theorem shiftedPowerArithmetic_apply (a : ℂ) {n : ℕ} (hn : n ≠ 0) :
    shiftedPowerArithmetic a n = (n:ℂ)^(-a) := by
  simp [shiftedPowerArithmetic, hn]

theorem shiftedPowerArithmetic_multiplicative (a : ℂ) :
    (shiftedPowerArithmetic a).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  constructor
  · simp [shiftedPowerArithmetic]
  · intro m n hm hn _
    rw [shiftedPowerArithmetic_apply a (mul_ne_zero hm hn),
      shiftedPowerArithmetic_apply a hm, shiftedPowerArithmetic_apply a hn]
    simpa only [Nat.cast_mul] using Complex.natCast_mul_natCast_cpow m n (-a)

noncomputable def shiftedTripleArithmetic (a : Fin 3 → ℂ) : ArithmeticFunction ℂ :=
  shiftedPowerArithmetic (a 0)*(shiftedPowerArithmetic (a 1)*shiftedPowerArithmetic (a 2))

theorem shiftedTripleArithmetic_multiplicative (a : Fin 3 → ℂ) :
    (shiftedTripleArithmetic a).IsMultiplicative :=
  (shiftedPowerArithmetic_multiplicative (a 0)).mul
    ((shiftedPowerArithmetic_multiplicative (a 1)).mul
      (shiftedPowerArithmetic_multiplicative (a 2)))

/-- The actual triple coefficient is precisely a finite sum over positive factorizations. -/
theorem shiftedTripleArithmetic_apply (a : Fin 3 → ℂ) (n : ℕ) :
    shiftedTripleArithmetic a n =
      ∑ d ∈ n.divisorsAntidiagonal, ∑ e ∈ d.2.divisorsAntidiagonal,
        shiftedPowerArithmetic (a 0) d.1*shiftedPowerArithmetic (a 1) e.1*
          shiftedPowerArithmetic (a 2) e.2 := by
  simp only [shiftedTripleArithmetic, ArithmeticFunction.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  ring

noncomputable def shiftedDiagonalArithmetic (a b : Fin 3 → ℂ) (s : ℂ) :
    ArithmeticFunction ℂ :=
  ⟨fun n => shiftedTripleArithmetic a n*shiftedTripleArithmetic b n*
    shiftedPowerArithmetic s n, by simp⟩

theorem shiftedDiagonalArithmetic_multiplicative (a b : Fin 3 → ℂ) (s : ℂ) :
    (shiftedDiagonalArithmetic a b s).IsMultiplicative := by
  have ha := shiftedTripleArithmetic_multiplicative a
  have hb := shiftedTripleArithmetic_multiplicative b
  have hs := shiftedPowerArithmetic_multiplicative s
  constructor
  · simp [shiftedDiagonalArithmetic, ha.map_one, hb.map_one, hs.map_one]
  · intro m n hmn
    simp only [shiftedDiagonalArithmetic, ArithmeticFunction.coe_mk]
    rw [ha.map_mul_of_coprime hmn, hb.map_mul_of_coprime hmn, hs.map_mul_of_coprime hmn]
    ring

theorem arithmeticConvolution_primePower {R : Type*} [Semiring R]
    {p : ℕ} (hp : Nat.Prime p) (f g : ArithmeticFunction R) (m : ℕ) :
    (f*g) (p^m) = ∑ i ∈ Finset.range (m+1), f (p^i)*g (p^(m-i)) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun i j => f i*g j),
    Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro i hi
  have him : i ≤ m := by have h := Finset.mem_range.mp hi; omega
  have he : p^m = p^i*p^(m-i) := by
    rw [← pow_add, Nat.add_sub_of_le him]
  rw [he, Nat.mul_div_cancel_left _ (pow_pos hp.pos i)]

theorem shiftedPowerArithmetic_primePower {p : ℕ} (hp : Nat.Prime p)
    (a : ℂ) (m : ℕ) :
    shiftedPowerArithmetic a (p^m) = ((p:ℂ)^(-a))^m := by
  rw [shiftedPowerArithmetic_apply a (pow_ne_zero _ hp.ne_zero)]
  rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul p m (-a), Complex.cpow_nat_mul]

theorem shiftedTripleArithmetic_primePower (p : {n : ℕ // Nat.Prime n})
    (a : Fin 3 → ℂ) (m : ℕ) :
    shiftedTripleArithmetic a (p.val^m) =
      triplePrimePowerCoefficient (primePolarWeights p a) m := by
  unfold shiftedTripleArithmetic
  rw [arithmeticConvolution_primePower p.property]
  simp_rw [arithmeticConvolution_primePower p.property,
    shiftedPowerArithmetic_primePower p.property, Finset.mul_sum]
  unfold triplePrimePowerCoefficient primePolarWeights
  apply Finset.sum_congr rfl
  intro i hi
  have him : i ≤ m := by have h := Finset.mem_range.mp hi; omega
  have hb : m-i+1 = m+1-i := by omega
  rw [hb]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem shiftedDiagonalArithmetic_primePower (p : {n : ℕ // Nat.Prime n})
    (a b : Fin 3 → ℂ) (m : ℕ) :
    shiftedDiagonalArithmetic a b 1 (p.val^m) =
      triplePrimePowerCoefficient (primePolarWeights p a) m*
        triplePrimePowerCoefficient (primePolarWeights p b) m*(1/(p.val:ℂ))^m := by
  simp only [shiftedDiagonalArithmetic, ArithmeticFunction.coe_mk,
    shiftedTripleArithmetic_primePower, shiftedPowerArithmetic_primePower p.property,
    Complex.cpow_neg_one, one_div]

end Sechstmoment
