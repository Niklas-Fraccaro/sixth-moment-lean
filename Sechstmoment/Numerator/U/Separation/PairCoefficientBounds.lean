import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Sechstmoment.Numerator.U.ZeroModes.Arithmetic.PairDiagonalEuler

/-! Absolute convergence of the genuinely translated fixed-amplifier
correlation, without normalizing its possibly zero value at one. -/

namespace Sechstmoment
open ArithmeticFunction Nat Complex
open scoped BigOperators ArithmeticFunction.sigma

set_option maxHeartbeats 0
noncomputable section

theorem cardDivisors_eq_prod_factorization_on {n : ℕ} (hn : n ≠ 0) (S : Finset ℕ)
    (hS : n.primeFactors ⊆ S) :
    n.divisors.card = ∏ p ∈ S, (n.factorization p+1) := by
  rw [Nat.card_divisors hn]
  apply Finset.prod_subset hS
  intro p _ hp
  have he : n.factorization p=0 := by
    exact Finsupp.notMem_support_iff.mp (by simpa only [Nat.support_factorization] using hp)
  simp [he]

theorem cardDivisors_mul_le {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    (m*n).divisors.card ≤ m.divisors.card*n.divisors.card := by
  let S := m.primeFactors ∪ n.primeFactors
  rw [cardDivisors_eq_prod_factorization_on (mul_ne_zero hm hn) S
      (by simpa only [Nat.primeFactors_mul hm hn] using (Finset.Subset.refl S)),
    cardDivisors_eq_prod_factorization_on hm S Finset.subset_union_left,
    cardDivisors_eq_prod_factorization_on hn S Finset.subset_union_right,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  intro p _
  rw [Nat.factorization_mul hm hn, Finsupp.add_apply]
  nlinarith [Nat.zero_le (m.factorization p*n.factorization p)]

def shiftedPairDivisorMajorant (e : ℝ) : ArithmeticFunction ℂ :=
  (↑(σ 0) : ArithmeticFunction ℂ).pmul (shiftedPowerArithmetic e)

theorem shiftedPairDivisorMajorant_multiplicative (e : ℝ) :
    (shiftedPairDivisorMajorant e).IsMultiplicative :=
  (isMultiplicative_sigma.natCast).pmul (shiftedPowerArithmetic_multiplicative _)

theorem shiftedPairDivisorMajorant_primePower_norm (e : ℝ) (p : Nat.Primes) (m : ℕ) :
    ‖shiftedPairDivisorMajorant e (p.val^m)‖ =
      (m+1:ℝ)*((p.val:ℝ)^(-e))^m := by
  rw [shiftedPairDivisorMajorant, ArithmeticFunction.pmul_apply, ArithmeticFunction.natCoe_apply,
    sigma_zero_apply_prime_pow p.property, shiftedPowerArithmetic_primePower p.property,
    norm_mul, Complex.norm_natCast, Complex.norm_pow, Complex.norm_natCast_cpow_of_pos p.property.pos]
  simp

theorem shiftedPairArithmetic_norm_le_divisorMajorant {e : ℝ}
    (a b : ℂ) (ha : e ≤ a.re) (hb : e ≤ b.re) (n : ℕ) :
    ‖shiftedPairArithmetic a b n‖ ≤ ‖shiftedPairDivisorMajorant e n‖ := by
  apply multiplicative_norm_le_of_primePower (shiftedPairArithmetic_multiplicative _ _)
    (shiftedPairDivisorMajorant_multiplicative _) (n := n)
  intro p m
  have hweight (z : ℂ) (hz : e ≤ z.re) : ‖(p.val:ℂ)^(-z)‖ ≤ (p.val:ℝ)^(-e) := by
    apply bblrPrimePowerNorm_le p.property
    simp only [Complex.neg_re]
    linarith
  rw [shiftedPairArithmetic_primePower p.property, shiftedPairDivisorMajorant_primePower_norm]
  exact pairPrimePowerCoefficient_norm_le (Real.rpow_nonneg (by positivity) _)
    (hweight a ha) (hweight b hb) m

theorem shiftedPairArithmetic_norm_le {e : ℝ}
    (a b : ℂ) (ha : e ≤ a.re) (hb : e ≤ b.re) {n : ℕ} (hn : n ≠ 0) :
    ‖shiftedPairArithmetic a b n‖ ≤ (n.divisors.card:ℝ)*(n:ℝ)^(-e) := by
  convert shiftedPairArithmetic_norm_le_divisorMajorant a b ha hb n using 1
  rw [shiftedPairDivisorMajorant, ArithmeticFunction.pmul_apply, ArithmeticFunction.natCoe_apply,
    sigma_zero_apply, shiftedPowerArithmetic_apply _ hn, norm_mul, Complex.norm_natCast,
    Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  simp

def pairSquareDivisorMajorant (e : ℝ) : ArithmeticFunction ℂ :=
  (↑(σ 0) : ArithmeticFunction ℂ).pmul
    ((↑(σ 0) : ArithmeticFunction ℂ).pmul (shiftedPowerArithmetic (1+2*e)))

theorem pairSquareDivisorMajorant_multiplicative (e : ℝ) :
    (pairSquareDivisorMajorant e).IsMultiplicative :=
  isMultiplicative_sigma.natCast.pmul
    (isMultiplicative_sigma.natCast.pmul (shiftedPowerArithmetic_multiplicative _))

theorem pairSquareDivisorMajorant_norm_le (e : ℝ) (n : ℕ) :
    ‖pairSquareDivisorMajorant e n‖ ≤ ‖diagonalNinthDivisorMajorant e n‖ := by
  apply multiplicative_norm_le_of_primePower (pairSquareDivisorMajorant_multiplicative _)
    (diagonalNinthDivisorMajorant_multiplicative _) (n := n)
  intro p m
  rw [pairSquareDivisorMajorant, ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply,
    ArithmeticFunction.natCoe_apply, sigma_zero_apply_prime_pow p.property,
    shiftedPowerArithmetic_primePower p.property, norm_mul, norm_mul, Complex.norm_natCast,
    Complex.norm_pow, Complex.norm_natCast_cpow_of_pos p.property.pos,
    diagonalNinthDivisorMajorant_primePower_norm]
  norm_num
  convert mul_le_mul_of_nonneg_right (pairDivisorCoefficient_sq_le_ninth m)
    (pow_nonneg (Real.rpow_nonneg (show (0:ℝ)≤p.val by exact_mod_cast p.property.pos.le) _) m)
    using 1
  ring

theorem pairSquareDivisorMajorant_norm (e : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ‖pairSquareDivisorMajorant e n‖ = (n.divisors.card:ℝ)^2*(n:ℝ)^(-(1+2*e)) := by
  rw [pairSquareDivisorMajorant, ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply,
    ArithmeticFunction.natCoe_apply, sigma_zero_apply, shiftedPowerArithmetic_apply _ hn,
    norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  simp
  ring

theorem shiftedPairCorrelation_norm_summable {e : ℝ} (he : 0 < e)
    (α β γ δ : ℂ) (hα : e ≤ α.re) (hβ : e ≤ β.re) (hγ : e ≤ γ.re) (hδ : e ≤ δ.re)
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Summable (fun n : ℕ => ‖shiftedPairArithmetic α β (b*n)*
      shiftedPairArithmetic γ δ (a*n)*shiftedPowerArithmetic 1 n‖) := by
  let C : ℝ := (b.divisors.card:ℝ)*(a.divisors.card:ℝ)*(b:ℝ)^(-e)*(a:ℝ)^(-e)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply ((diagonalNinthDivisorMajorant_norm_summable he).mul_left C).of_norm_bounded
  intro n
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  by_cases hn : n=0
  · simp [hn]
  have hnpos : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hap : (0:ℝ)<a := by exact_mod_cast Nat.pos_of_ne_zero ha
  have hbp : (0:ℝ)<b := by exact_mod_cast Nat.pos_of_ne_zero hb
  have hdiva : ((a*n).divisors.card:ℝ) ≤ (a.divisors.card:ℝ)*(n.divisors.card:ℝ) := by
    exact_mod_cast cardDivisors_mul_le ha hn
  have hdivb : ((b*n).divisors.card:ℝ) ≤ (b.divisors.card:ℝ)*(n.divisors.card:ℝ) := by
    exact_mod_cast cardDivisors_mul_le hb hn
  rw [norm_mul, norm_mul, shiftedPowerArithmetic_apply _ hn,
    Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  simp only [Complex.neg_re, Complex.one_re]
  calc
    _ ≤ (((b*n).divisors.card:ℝ)*((b*n:ℕ):ℝ)^(-e))*
      (((a*n).divisors.card:ℝ)*((a*n:ℕ):ℝ)^(-e))*(n:ℝ)^(-1:ℝ) := by
      gcongr
      · exact shiftedPairArithmetic_norm_le α β hα hβ (mul_ne_zero hb hn)
      · exact shiftedPairArithmetic_norm_le γ δ hγ hδ (mul_ne_zero ha hn)
    _ ≤ ((b.divisors.card:ℝ)*(n.divisors.card:ℝ)*(b:ℝ)^(-e)*(n:ℝ)^(-e))*
      ((a.divisors.card:ℝ)*(n.divisors.card:ℝ)*(a:ℝ)^(-e)*(n:ℝ)^(-e))*(n:ℝ)^(-1:ℝ) := by
      rw [Nat.cast_mul, Nat.cast_mul, Real.mul_rpow hbp.le hnpos.le, Real.mul_rpow hap.le hnpos.le]
      calc
        _ ≤ ((b.divisors.card:ℝ)*(n.divisors.card:ℝ)*((b:ℝ)^(-e)*(n:ℝ)^(-e)))*
          ((a.divisors.card:ℝ)*(n.divisors.card:ℝ)*((a:ℝ)^(-e)*(n:ℝ)^(-e)))*(n:ℝ)^(-1:ℝ) := by
          gcongr
        _ = _ := by ring
    _ = C*‖pairSquareDivisorMajorant e n‖ := by
      rw [pairSquareDivisorMajorant_norm e hn]
      have hpow : (n:ℝ)^(-e)*(n:ℝ)^(-e)*(n:ℝ)^(-1:ℝ)=(n:ℝ)^(-(1+2*e)) := by
        rw [← Real.rpow_add hnpos, ← Real.rpow_add hnpos]
        congr 1
        ring
      dsimp [C]
      linear_combination ((b.divisors.card:ℝ)*(a.divisors.card:ℝ)*(n.divisors.card:ℝ)^2*
        (b:ℝ)^(-e)*(a:ℝ)^(-e))*hpow
    _ ≤ _ := mul_le_mul_of_nonneg_left (pairSquareDivisorMajorant_norm_le e n) hC

end
end Sechstmoment
