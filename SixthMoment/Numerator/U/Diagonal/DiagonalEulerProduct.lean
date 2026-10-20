import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import SixthMoment.Arithmetic.Euler.Shifted.Convergence
import SixthMoment.Numerator.U.Diagonal.DiagonalEulerSummability


namespace SixthMoment
open ArithmeticFunction Nat
open scoped BigOperators

set_option maxHeartbeats 0

theorem shiftedDiagonalArithmetic_euler_hasProd {δ : ℝ} (hδ : 0 < δ)
    {a b : Fin 3 → ℂ} (ha : ∀ i, δ ≤ (a i).re) (hb : ∀ i, δ ≤ (b i).re) :
    HasProd (fun p : Nat.Primes => shiftedDiagonalPrimeSeries p a b)
      (∑' n, shiftedDiagonalArithmetic a b 1 n) := by
  have h := (shiftedDiagonalArithmetic_multiplicative a b 1).eulerProduct_hasProd
    (shiftedDiagonalArithmetic_norm_summable hδ ha hb)
  apply h.congr_fun
  intro p
  unfold shiftedDiagonalPrimeSeries
  apply tsum_congr
  intro m
  exact (shiftedDiagonalArithmetic_primePower (show {n:ℕ // Nat.Prime n} from p) a b m).symm

theorem shiftedDiagonalArithmetic_euler_tprod {δ : ℝ} (hδ : 0 < δ)
    {a b : Fin 3 → ℂ} (ha : ∀ i, δ ≤ (a i).re) (hb : ∀ i, δ ≤ (b i).re) :
    ∏' p : Nat.Primes, shiftedDiagonalPrimeSeries p a b =
      ∑' n, shiftedDiagonalArithmetic a b 1 n :=
  (shiftedDiagonalArithmetic_euler_hasProd hδ ha hb).tprod_eq

theorem shiftedPolarPrimeDivisors_ne_zero {a b : Fin 3 → ℂ}
    (hab : ∀ i j, 0 < (a i).re+(b j).re) (p : Nat.Primes) :
    shiftedPolarPrimeDivisors p a b ≠ 0 := by
  unfold shiftedPolarPrimeDivisors
  apply Finset.prod_ne_zero_iff.mpr
  intro ij _
  apply Complex.one_sub_prime_cpow_ne_zero p.property
  simp only [Complex.add_re, Complex.one_re]
  linarith [hab ij.1 ij.2]

theorem shiftedPolarPrimeDivisors_inv_hasProd {a b : Fin 3 → ℂ}
    (hab : ∀ i j, 0 < (a i).re+(b j).re) :
    HasProd (fun p : Nat.Primes => (shiftedPolarPrimeDivisors p a b)⁻¹)
      (∏ ij : Fin 3 × Fin 3, riemannZeta (1+a ij.1+b ij.2)) := by
  have h := hasProd_prod (s := Finset.univ)
    (f := fun ij : Fin 3 × Fin 3 => fun p : Nat.Primes =>
      (1-(p.val:ℂ)^(-(1+a ij.1+b ij.2)))⁻¹)
    (a := fun ij => riemannZeta (1+a ij.1+b ij.2))
    (by
      intro ij _
      apply riemannZeta_eulerProduct_hasProd
      simp only [Complex.add_re, Complex.one_re]
      linarith [hab ij.1 ij.2])
  simpa only [shiftedPolarPrimeDivisors, Finset.prod_inv_distrib] using h

theorem shiftedDiagonalArithmetic_eq_zetaProduct_mul_rest {δ : ℝ} (hδ : 0 < δ)
    {a b : Fin 3 → ℂ} (ha : ∀ i, δ ≤ (a i).re) (hb : ∀ i, δ ≤ (b i).re) :
    (∑' n, shiftedDiagonalArithmetic a b 1 n) =
      (∏ ij : Fin 3 × Fin 3, riemannZeta (1+a ij.1+b ij.2))*shiftedPolarEulerRest a b := by
  have hab : ∀ i j, 0 < (a i).re+(b j).re := by
    intro i j
    linarith [ha i, hb j]
  have hrest := shiftedPolarEulerRest_multipliable a b (δ := 0) (by norm_num)
    (fun i => by linarith [ha i]) (fun i => by linarith [hb i])
  have h := (shiftedPolarPrimeDivisors_inv_hasProd hab).mul hrest.hasProd
  have he (p : Nat.Primes) :
      (shiftedPolarPrimeDivisors p a b)⁻¹*shiftedPolarPrimeRemainder p a b =
        shiftedDiagonalPrimeSeries p a b := by
    unfold shiftedPolarPrimeRemainder
    rw [← mul_assoc, inv_mul_cancel₀ (shiftedPolarPrimeDivisors_ne_zero hab p), one_mul]
  have hf : HasProd (fun p : Nat.Primes => shiftedDiagonalPrimeSeries p a b)
      ((∏ ij : Fin 3 × Fin 3, riemannZeta (1+a ij.1+b ij.2))*shiftedPolarEulerRest a b) := by
    exact h.congr_fun (fun p => (he p).symm)
  exact (shiftedDiagonalArithmetic_euler_hasProd hδ ha hb).unique hf

end SixthMoment
