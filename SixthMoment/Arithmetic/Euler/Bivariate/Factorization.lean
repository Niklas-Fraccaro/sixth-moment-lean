import SixthMoment.Arithmetic.Euler.Bivariate.EulerConvergence

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace SixthMoment.Source.NoDPLocalClosure
open NoDPLocal NoDPResidues
open scoped BigOperators

theorem prime_original_tail_absolute (p : ℕ) (hp : p.Prime) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (h : ℕ) :
    Summable (fun n => ‖coeff4 (primeRoot p (s 0)) (primeRoot p (s 1))
      (primeRoot p (s 2)) (primeRoot p (s 3)) (h+n)*((p:ℂ)^(-(1-s 0)))^(h+n)‖) := by
  rw [prime_pole_parameter p hp]
  exact original_tail_absolute _ _ _ _ _ (primeScale p ρ) (primeScale_one_le p hp ρ hρ0)
    (primeRoot_bound p hp (s 0) ρ (hs 0)) (primeRoot_inv_bound p hp (s 0) ρ (hs 0))
    (primeRoot_bound p hp (s 1) ρ (hs 1)) (primeRoot_bound p hp (s 2) ρ (hs 2))
    (primeRoot_bound p hp (s 3) ρ (hs 3)) (prime_uniform_region p hp ρ hρ) h

theorem primeWeight_growth (p : ℕ) (hp : p.Prime) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (h : ℕ) :
    ‖primeWeight p s h‖ ≤ 12*quadraticHeight h*((p:ℝ)^(-1+3*ρ))^h := by
  have hM := primeScale_one_le p hp ρ hρ0
  have H := weightedResidue_uniform_bound (primeRoot p (s 0)) (primeRoot p (s 1))
    (primeRoot p (s 2)) (primeRoot p (s 3)) (primeX p) (primeScale p ρ) hM
    (primeRoot_bound p hp (s 0) ρ (hs 0)) (primeRoot_inv_bound p hp (s 0) ρ (hs 0))
    (primeRoot_bound p hp (s 1) ρ (hs 1)) (primeRoot_bound p hp (s 2) ρ (hs 2))
    (primeRoot_bound p hp (s 3) ρ (hs 3))
    (quadratic_region_lt (primeX p) (primeScale p ρ) hM (prime_uniform_region p hp ρ hρ)).le h
  have HW := prime_weight_identity p hp ρ 1 3
  norm_num only [pow_one, Nat.cast_one, Nat.cast_ofNat] at HW
  simpa only [primeWeight, HW] using H

theorem prime_original_six_factors (p : ℕ) (hp : p.Prime) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (U V : ℂ)
    (hU : ‖U‖ ≤ primeScale p ρ) (hV : ‖V‖ ≤ primeScale p ρ) :
    primeRest p s U V = primeDen p s U*primeDen p s V*
      doubleSeries (primeOriginalWeight p s) U V := by
  have H : primeOriginalWeight p s = primeWeight p s := funext (prime_residue_cancellation p hp s ρ hρ0 hρ hs)
  rw [H]
  exact prime_six_factors p hp s ρ hρ0 hρ hs U V hU hV

theorem local_prime_closure (p : ℕ) (hp : p.Prime) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (U V : ℂ)
    (hU : ‖U‖ ≤ primeScale p ρ) (hV : ‖V‖ ≤ primeScale p ρ) :
    (∀ h, primeOriginalWeight p s h = primeWeight p s h) ∧
    Summable (fun q : ℕ × ℕ => ‖diagonalTerm (primeOriginalWeight p s) U V q‖) ∧
    primeRest p s U V = primeDen p s U*primeDen p s V*doubleSeries (primeOriginalWeight p s) U V ∧
    primeDen p s U ≠ 0 ∧ primeDen p s V ≠ 0 ∧
    (∀ m n, 3 ≤ m ∨ 3 ≤ n →
      residueRest (primeRoot p (s 0)) (primeRoot p (s 1)) (primeRoot p (s 2))
        (primeRoot p (s 3)) (primeX p) m n = 0) ∧
    primeErrorMass p s ρ ≤ 35*(p:ℝ)^(-2+4*ρ) :=
  ⟨prime_residue_cancellation p hp s ρ hρ0 hρ hs,
    prime_original_double_absolute p hp s ρ hρ0 hρ hs U V hU hV,
    prime_original_six_factors p hp s ρ hρ0 hρ hs U V hU hV,
    prime_denominator_ne_zero p hp s ρ hρ0 hρ hs U hU,
    prime_denominator_ne_zero p hp s ρ hρ0 hρ hs V hV,
    prime_rest_support p hp s, prime_error_mass_bound p hp s ρ hρ0 hρ hs⟩

theorem zero_shift_local_factor (p : ℕ) (hp : p.Prime) :
    (1-primeX p)^6*doubleSeries (primeOriginalWeight p (fun _ => 0)) 1 1 =
      (1-primeX p)^4*(1+4*primeX p+(primeX p)^2) := by
  have H := prime_original_six_factors p hp (fun _ => 0) 0 (by norm_num) (by norm_num)
    (by intro j; simp) 1 1 (by simp [primeScale]) (by simp [primeScale])
  rw [primeRest_zero_shifts] at H
  have HD : primeDen p (fun _ => 0) 1*primeDen p (fun _ => 0) 1 = (1-primeX p)^6 := by
    unfold primeDen den3 primeRoot
    simp only [neg_zero, Complex.cpow_zero, mul_one]
    ring
  rw [HD] at H
  exact H.symm

theorem local_completion_and_euler_convergence (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) :
    (∀ p : Nat.Primes, ∀ U V : ℂ, ‖U‖ ≤ primeScale p.val ρ → ‖V‖ ≤ primeScale p.val ρ →
      Summable (fun q : ℕ × ℕ => ‖diagonalTerm (primeOriginalWeight p.val s) U V q‖) ∧
      primeRest p.val s U V = primeDen p.val s U*primeDen p.val s V*
        doubleSeries (primeOriginalWeight p.val s) U V ∧
      ‖primeRest p.val s U V-1‖ ≤ 35*(p.val:ℝ)^(-2+4*ρ)) ∧
    Summable (fun p : Nat.Primes => primeErrorMass p.val s ρ) ∧
    (∀ U V : Nat.Primes → ℂ, (∀ p, ‖U p‖ ≤ primeScale p.val ρ) → (∀ p, ‖V p‖ ≤ primeScale p.val ρ) →
      Multipliable (fun p : Nat.Primes => primeRest p.val s (U p) (V p))) := by
  refine ⟨?_, prime_error_mass_summable s ρ hρ0 hρ hs, ?_⟩
  · intro p U V hU hV
    exact ⟨prime_original_double_absolute p.val p.property s ρ hρ0 hρ hs U V hU hV,
      prime_original_six_factors p.val p.property s ρ hρ0 hρ hs U V hU hV,
      prime_rest_error_bound p.val p.property s ρ hρ0 hρ hs U V hU hV⟩
  · intro U V hU hV
    exact prime_rest_product_converges s ρ hρ0 hρ hs U V hU hV

end SixthMoment.Source.NoDPLocalClosure
