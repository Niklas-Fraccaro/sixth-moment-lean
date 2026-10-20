import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Sechstmoment.Arithmetic.Euler.Bivariate.PrimeClosure

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Sechstmoment.Source.NoDPLocalClosure
open NoDPLocal NoDPResidues
open scoped BigOperators

noncomputable def primeMajorant (ρ : ℝ) (p : Nat.Primes) : ℝ := 35*(p.val:ℝ)^(-2+4*ρ)

theorem primeMajorant_nonneg (ρ : ℝ) (p : Nat.Primes) : 0 ≤ primeMajorant ρ p := by
  unfold primeMajorant
  positivity

theorem primeMajorant_summable (ρ : ℝ) (hρ : ρ < 1/4) : Summable (primeMajorant ρ) := by
  have H : Summable (fun n : ℕ => (n:ℝ)^(-2+4*ρ)) := Real.summable_nat_rpow.mpr (by linarith)
  exact (H.mul_left 35).subtype _

theorem primeErrorMass_nonneg (p : ℕ) (s : Fin 4 → ℂ) (ρ : ℝ) : 0 ≤ primeErrorMass p s ρ := by
  apply tsum_nonneg
  intro q
  apply mul_nonneg (norm_nonneg _)
  exact pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) ρ) _

theorem prime_error_mass_summable (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) :
    Summable (fun p : Nat.Primes => primeErrorMass p.val s ρ) :=
  (primeMajorant_summable ρ hρ).of_nonneg_of_le (fun p => primeErrorMass_nonneg p.val s ρ)
    (fun p => prime_error_mass_bound p.val p.property s ρ hρ0 hρ hs)

theorem prime_rest_errors_summable (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (U V : Nat.Primes → ℂ)
    (hU : ∀ p, ‖U p‖ ≤ primeScale p.val ρ) (hV : ∀ p, ‖V p‖ ≤ primeScale p.val ρ) :
    Summable (fun p : Nat.Primes => ‖primeRest p.val s (U p) (V p)-1‖) :=
  (primeMajorant_summable ρ hρ).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => prime_rest_error_bound p.val p.property s ρ hρ0 hρ hs (U p) (V p) (hU p) (hV p))

theorem prime_rest_product_converges (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (U V : Nat.Primes → ℂ)
    (hU : ∀ p, ‖U p‖ ≤ primeScale p.val ρ) (hV : ∀ p, ‖V p‖ ≤ primeScale p.val ρ) :
    Multipliable (fun p : Nat.Primes => primeRest p.val s (U p) (V p)) := by
  simpa only [add_sub_cancel] using multipliable_one_add_of_summable
    (prime_rest_errors_summable s ρ hρ0 hρ hs U V hU hV)

theorem prime_rest_product_hasProd (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (U V : Nat.Primes → ℂ)
    (hU : ∀ p, ‖U p‖ ≤ primeScale p.val ρ) (hV : ∀ p, ‖V p‖ ≤ primeScale p.val ρ) :
    HasProd (fun p : Nat.Primes => primeRest p.val s (U p) (V p))
      (∏' p : Nat.Primes, primeRest p.val s (U p) (V p)) :=
  (prime_rest_product_converges s ρ hρ0 hρ hs U V hU hV).hasProd

theorem prime_rest_finite_product_bound (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (U V : Nat.Primes → ℂ)
    (hU : ∀ p, ‖U p‖ ≤ primeScale p.val ρ) (hV : ∀ p, ‖V p‖ ≤ primeScale p.val ρ)
    (t : Finset Nat.Primes) :
    ‖∏ p ∈ t, primeRest p.val s (U p) (V p)‖ ≤ Real.exp (∑' p : Nat.Primes, primeMajorant ρ p) := by
  calc
    _ ≤ ∏ p ∈ t, ‖primeRest p.val s (U p) (V p)‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ p ∈ t, Real.exp (primeMajorant ρ p) := by
      apply Finset.prod_le_prod₀ (fun p _ => norm_nonneg _)
      intro p _
      calc
        _ ≤ ‖primeRest p.val s (U p) (V p)-1‖+1 := by simpa using norm_le_norm_sub_add (primeRest p.val s (U p) (V p)) 1
        _ ≤ primeMajorant ρ p+1 := add_le_add (prime_rest_error_bound p.val p.property s ρ hρ0 hρ hs (U p) (V p) (hU p) (hV p)) le_rfl
        _ ≤ Real.exp (primeMajorant ρ p) := Real.add_one_le_exp _
    _ = Real.exp (∑ p ∈ t, primeMajorant ρ p) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' p : Nat.Primes, primeMajorant ρ p) :=
      Real.exp_le_exp.mpr ((primeMajorant_summable ρ hρ).sum_le_tsum t (fun p _ => primeMajorant_nonneg ρ p))

end Sechstmoment.Source.NoDPLocalClosure
