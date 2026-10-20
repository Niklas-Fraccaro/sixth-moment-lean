import Mathlib.NumberTheory.LSeries.Dirichlet
import Sechstmoment.Numerator.U.Diagonal.DiagonalEulerCoefficients
import Sechstmoment.Numerator.U.Diagonal.DiagonalEulerMajorant


namespace Sechstmoment
open ArithmeticFunction Nat
open scoped BigOperators ArithmeticFunction.zeta

set_option maxHeartbeats 0

theorem zetaPower_primePower {p : ℕ} (hp : Nat.Prime p) (k m : ℕ) :
    (ζ^(k+1)) (p^m) = (m+k).choose k := by
  induction k generalizing m with
  | zero => simp [zeta_apply_ne (pow_ne_zero _ hp.ne_zero)]
  | succ k ih =>
    rw [show k+1+1 = (k+1)+1 by omega, pow_succ,
      arithmeticConvolution_primePower hp]
    simp only [ih, zeta_apply_ne (pow_ne_zero _ hp.ne_zero), mul_one]
    simpa only [Nat.add_assoc] using Nat.sum_range_add_choose m k

theorem zetaPower_natCast (k : ℕ) :
    (↑(ζ^k) : ArithmeticFunction ℂ) = (ζ:ArithmeticFunction ℂ)^k := by
  induction k with
  | zero => simp [natCoe_one]
  | succ k ih => rw [pow_succ, natCoe_mul, ih, pow_succ]

theorem zetaPower_LSeriesSummable (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (↑(ζ^(k+1)) : ArithmeticFunction ℂ) n) s := by
  rw [zetaPower_natCast]
  induction k with
  | zero => simpa using LSeriesSummable_zeta_iff.mpr hs
  | succ k ih =>
    rw [show k+1+1 = (k+1)+1 by omega, pow_succ]
    exact ArithmeticFunction.LSeriesSummable_mul ih (LSeriesSummable_zeta_iff.mpr hs)

theorem multiplicative_norm_le_of_primePower {f g : ArithmeticFunction ℂ}
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative)
    (h : ∀ p : Nat.Primes, ∀ m : ℕ, ‖f (p.val^m)‖ ≤ ‖g (p.val^m)‖) (n : ℕ) :
    ‖f n‖ ≤ ‖g n‖ := by
  by_cases hn : n = 0
  · simp [hn]
  rw [hf.multiplicative_factorization f hn, hg.multiplicative_factorization g hn]
  simp only [Finsupp.prod, norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro p hp
  exact h ⟨p, Nat.prime_of_mem_primeFactors hp⟩ (n.factorization p)

noncomputable def diagonalNinthDivisorMajorant (δ : ℝ) : ArithmeticFunction ℂ :=
  (↑(ζ^9) : ArithmeticFunction ℂ).pmul (shiftedPowerArithmetic (1+2*δ))

theorem diagonalNinthDivisorMajorant_multiplicative (δ : ℝ) :
    (diagonalNinthDivisorMajorant δ).IsMultiplicative :=
  (isMultiplicative_zeta.pow (k := 9)).natCast.pmul
    (shiftedPowerArithmetic_multiplicative (1+2*δ))

theorem diagonalNinthDivisorMajorant_norm_summable {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun n => ‖diagonalNinthDivisorMajorant δ n‖) := by
  have hs : 1 < (1+2*(δ:ℂ)).re := by simp; linarith
  have hz := zetaPower_LSeriesSummable 8 hs
  apply (summable_norm_iff.mpr hz).congr
  intro n
  rw [LSeries.term_def₀ (↑(ζ^9) : ArithmeticFunction ℂ).map_zero,
    diagonalNinthDivisorMajorant, pmul_apply]
  simp only [shiftedPowerArithmetic, ArithmeticFunction.coe_mk]
  split_ifs with hn
  · simp [hn]
  · rfl

theorem diagonalNinthDivisorMajorant_primePower_norm (δ : ℝ) (p : Nat.Primes) (m : ℕ) :
    ‖diagonalNinthDivisorMajorant δ (p.val^m)‖ =
      ((m+8).choose 8:ℝ)*((p.val:ℝ)^(-(1+2*δ)))^m := by
  rw [diagonalNinthDivisorMajorant, pmul_apply, natCoe_apply,
    show (ζ^9) (p.val^m) = (m+8).choose 8 from zetaPower_primePower p.property 8 m,
    shiftedPowerArithmetic_primePower p.property,
    norm_mul, Complex.norm_natCast, Complex.norm_pow,
    Complex.norm_natCast_cpow_of_pos p.property.pos]
  simp

theorem shiftedDiagonalArithmetic_primePower_norm_le {δ : ℝ}
    {a b : Fin 3 → ℂ} (ha : ∀ i, δ ≤ (a i).re) (hb : ∀ i, δ ≤ (b i).re)
    (p : Nat.Primes) (m : ℕ) :
    ‖shiftedDiagonalArithmetic a b 1 (p.val^m)‖ ≤
      ‖diagonalNinthDivisorMajorant δ (p.val^m)‖ := by
  have hp : (0:ℝ) < p.val := by exact_mod_cast p.property.pos
  have hpa := primePolarWeights_norm_le p a (δ := -δ) (by simpa using ha)
  have hpb := primePolarWeights_norm_le p b (δ := -δ) (by simpa using hb)
  rw [shiftedDiagonalArithmetic_primePower (show {n:ℕ // Nat.Prime n} from p) a b m,
    diagonalNinthDivisorMajorant_primePower_norm]
  have he : ((p.val:ℝ)^(-δ))^2*‖1/(p.val:ℂ)‖ = (p.val:ℝ)^(-(1+2*δ)) := by
    rw [pow_two, norm_div, norm_one, Complex.norm_natCast, one_div,
      ← Real.rpow_neg_one, ← Real.rpow_add hp, ← Real.rpow_add hp]
    congr 1
    ring
  calc
    _ ≤ (d3PrimePowerCoefficient m:ℝ)^2*
        (((p.val:ℝ)^(-δ))^2*‖1/(p.val:ℂ)‖)^m :=
      diagonalPrimeTerm_norm_le (Real.rpow_nonneg hp.le _) hpa hpb _ m
    _ = (d3PrimePowerCoefficient m:ℝ)^2*((p.val:ℝ)^(-(1+2*δ)))^m := by rw [he]
    _ ≤ _ := mul_le_mul_of_nonneg_right (d3PrimePowerCoefficient_sq_le_d9_real m)
      (pow_nonneg (Real.rpow_nonneg hp.le _) _)

theorem shiftedDiagonalArithmetic_norm_summable {δ : ℝ} (hδ : 0 < δ)
    {a b : Fin 3 → ℂ} (ha : ∀ i, δ ≤ (a i).re) (hb : ∀ i, δ ≤ (b i).re) :
    Summable (fun n => ‖shiftedDiagonalArithmetic a b 1 n‖) := by
  apply (diagonalNinthDivisorMajorant_norm_summable hδ).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro n
  exact multiplicative_norm_le_of_primePower
    (shiftedDiagonalArithmetic_multiplicative a b 1)
    (diagonalNinthDivisorMajorant_multiplicative δ)
    (shiftedDiagonalArithmetic_primePower_norm_le ha hb) n

theorem shiftedDiagonalArithmetic_summable {δ : ℝ} (hδ : 0 < δ)
    {a b : Fin 3 → ℂ} (ha : ∀ i, δ ≤ (a i).re) (hb : ∀ i, δ ≤ (b i).re) :
    Summable (fun n => shiftedDiagonalArithmetic a b 1 n) :=
  (shiftedDiagonalArithmetic_norm_summable hδ ha hb).of_norm

end Sechstmoment
