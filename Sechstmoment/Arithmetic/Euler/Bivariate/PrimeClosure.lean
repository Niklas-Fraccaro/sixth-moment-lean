import Sechstmoment.Arithmetic.Euler.Bivariate.PrimeParameters

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Sechstmoment.Source.NoDPLocalClosure
open NoDPLocal NoDPResidues
open scoped BigOperators

noncomputable def primeWeight (p : ℕ) (s : Fin 4 → ℂ) (h : ℕ) : ℂ :=
  weightedResidue (primeRoot p (s 0)) (primeRoot p (s 1)) (primeRoot p (s 2))
    (primeRoot p (s 3)) (primeX p) h
noncomputable def primeRest (p : ℕ) (s : Fin 4 → ℂ) (U V : ℂ) : ℂ :=
  restPolynomial (primeRoot p (s 0)) (primeRoot p (s 1)) (primeRoot p (s 2))
    (primeRoot p (s 3)) (primeX p) U V
noncomputable def primeDen (p : ℕ) (s : Fin 4 → ℂ) (U : ℂ) : ℂ :=
  den3 (primeX p*primeRoot p (s 1)) (primeX p*primeRoot p (s 2))
    (primeX p*primeRoot p (s 3)) U
noncomputable def primeErrorMass (p : ℕ) (s : Fin 4 → ℂ) (ρ : ℝ) : ℝ :=
  errorMass (primeRoot p (s 0)) (primeRoot p (s 1)) (primeRoot p (s 2))
    (primeRoot p (s 3)) (primeX p) (primeScale p ρ)
noncomputable def primeOriginalWeight (p : ℕ) (s : Fin 4 → ℂ) (h : ℕ) : ℂ :=
  (primeRoot p (s 0))^h*originalPoleTail (primeRoot p (s 0)) (primeRoot p (s 1))
    (primeRoot p (s 2)) (primeRoot p (s 3)) ((p:ℂ)^(-(1-s 0))) (1/((p:ℂ)-1)) h

theorem prime_residue_cancellation (p : ℕ) (hp : p.Prime) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (h : ℕ) :
    primeOriginalWeight p s h = primeWeight p s h := by
  unfold primeOriginalWeight primeWeight
  rw [prime_pole_parameter p hp, ← prime_boundary_parameter p hp]
  exact originalPoleTail_uniform _ _ _ _ _ (primeRoot_ne_zero p hp.ne_zero (s 0))
    (primeScale p ρ) (primeScale_one_le p hp ρ hρ0)
    (primeRoot_inv_bound p hp (s 0) ρ (hs 0)) (primeRoot_bound p hp (s 1) ρ (hs 1))
    (primeRoot_bound p hp (s 2) ρ (hs 2)) (primeRoot_bound p hp (s 3) ρ (hs 3))
    (prime_uniform_region p hp ρ hρ) h

theorem prime_double_summable (p : ℕ) (hp : p.Prime) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (U V : ℂ)
    (hU : ‖U‖ ≤ primeScale p ρ) (hV : ‖V‖ ≤ primeScale p ρ) :
    Summable (diagonalTerm (primeWeight p s) U V) :=
  weightedResidue_double_uniform _ _ _ _ _ _ _ (primeScale p ρ) (primeScale_one_le p hp ρ hρ0)
    (primeRoot_bound p hp (s 0) ρ (hs 0)) (primeRoot_inv_bound p hp (s 0) ρ (hs 0))
    (primeRoot_bound p hp (s 1) ρ (hs 1)) (primeRoot_bound p hp (s 2) ρ (hs 2))
    (primeRoot_bound p hp (s 3) ρ (hs 3)) (prime_uniform_region p hp ρ hρ) hU hV

theorem prime_double_absolute (p : ℕ) (hp : p.Prime) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (U V : ℂ)
    (hU : ‖U‖ ≤ primeScale p ρ) (hV : ‖V‖ ≤ primeScale p ρ) :
    Summable (fun q : ℕ × ℕ => ‖diagonalTerm (primeWeight p s) U V q‖) :=
  (prime_double_summable p hp s ρ hρ0 hρ hs U V hU hV).norm

theorem prime_original_double_absolute (p : ℕ) (hp : p.Prime) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (U V : ℂ)
    (hU : ‖U‖ ≤ primeScale p ρ) (hV : ‖V‖ ≤ primeScale p ρ) :
    Summable (fun q : ℕ × ℕ => ‖diagonalTerm (primeOriginalWeight p s) U V q‖) := by
  have H : primeOriginalWeight p s = primeWeight p s := funext (prime_residue_cancellation p hp s ρ hρ0 hρ hs)
  rw [H]
  exact prime_double_absolute p hp s ρ hρ0 hρ hs U V hU hV

theorem prime_six_factors (p : ℕ) (hp : p.Prime) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (U V : ℂ)
    (hU : ‖U‖ ≤ primeScale p ρ) (hV : ‖V‖ ≤ primeScale p ρ) :
    primeRest p s U V = primeDen p s U*primeDen p s V*doubleSeries (primeWeight p s) U V :=
  restPolynomial_factorization_of_summable _ _ _ _ _ _ _ (primeRoot_ne_zero p hp.ne_zero (s 0))
    (prime_double_summable p hp s ρ hρ0 hρ hs U V hU hV)

theorem prime_denominator_ne_zero (p : ℕ) (hp : p.Prime) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (U : ℂ)
    (hU : ‖U‖ ≤ primeScale p ρ) : primeDen p s U ≠ 0 :=
  local_denominator_ne_zero _ _ _ _ _ (primeScale p ρ) (primeScale_one_le p hp ρ hρ0)
    (primeRoot_bound p hp (s 1) ρ (hs 1)) (primeRoot_bound p hp (s 2) ρ (hs 2))
    (primeRoot_bound p hp (s 3) ρ (hs 3)) (prime_uniform_region p hp ρ hρ) hU

theorem prime_double_rational (p : ℕ) (hp : p.Prime) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (U V : ℂ)
    (hU : ‖U‖ ≤ primeScale p ρ) (hV : ‖V‖ ≤ primeScale p ρ) :
    doubleSeries (primeWeight p s) U V = primeRest p s U V/(primeDen p s U*primeDen p s V) := by
  apply (eq_div_iff (mul_ne_zero (prime_denominator_ne_zero p hp s ρ hρ0 hρ hs U hU)
    (prime_denominator_ne_zero p hp s ρ hρ0 hρ hs V hV))).2
  simpa only [mul_comm] using (prime_six_factors p hp s ρ hρ0 hρ hs U V hU hV).symm

theorem prime_rest_support (p : ℕ) (hp : p.Prime) (s : Fin 4 → ℂ) (m n : ℕ)
    (h : 3 ≤ m ∨ 3 ≤ n) :
    residueRest (primeRoot p (s 0)) (primeRoot p (s 1)) (primeRoot p (s 2))
      (primeRoot p (s 3)) (primeX p) m n = 0 :=
  residueRest_support _ _ _ _ _ (primeRoot_ne_zero p hp.ne_zero (s 0)) m n h

theorem prime_error_mass_bound (p : ℕ) (hp : p.Prime) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) :
    primeErrorMass p s ρ ≤ 35*(p:ℝ)^(-2+4*ρ) := by
  have hM := primeScale_one_le p hp ρ hρ0
  have H := errorMass_bound (primeRoot p (s 0)) (primeRoot p (s 1)) (primeRoot p (s 2))
    (primeRoot p (s 3)) (primeX p) (primeScale p ρ) (le_trans zero_le_one hM)
    (primeRoot_inv_bound p hp (s 0) ρ (hs 0)) (primeRoot_bound p hp (s 1) ρ (hs 1))
    (primeRoot_bound p hp (s 2) ρ (hs 2)) (primeRoot_bound p hp (s 3) ρ (hs 3))
    (primeRoot_ne_zero p hp.ne_zero (s 0))
    (quadratic_region_lt (primeX p) (primeScale p ρ) hM (prime_uniform_region p hp ρ hρ)).le
  have HW := prime_weight_identity p hp ρ 2 4
  norm_num only [Nat.cast_ofNat] at HW
  calc
    _ ≤ 35*‖primeX p‖^2*(primeScale p ρ)^4 := H
    _ = _ := by rw [mul_assoc, HW]

theorem prime_error_mass_pdf_bound (p : ℕ) (hp : p.Prime) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) :
    primeErrorMass p s ρ ≤ 35*(p:ℝ)^(-2+8*ρ) := by
  apply (prime_error_mass_bound p hp s ρ hρ0 hρ hs).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 35)
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_lt.le)
  linarith

theorem prime_rest_error_bound (p : ℕ) (hp : p.Prime) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (U V : ℂ)
    (hU : ‖U‖ ≤ primeScale p ρ) (hV : ‖V‖ ≤ primeScale p ρ) :
    ‖primeRest p s U V-1‖ ≤ 35*(p:ℝ)^(-2+4*ρ) :=
  (restPolynomial_error_le_mass _ _ _ _ _ U V (primeRoot_ne_zero p hp.ne_zero (s 0))
    (primeScale p ρ) (le_trans zero_le_one (primeScale_one_le p hp ρ hρ0)) hU hV).trans
    (prime_error_mass_bound p hp s ρ hρ0 hρ hs)

@[fun_prop] theorem primeRest_entire_left (p : ℕ) (s : Fin 4 → ℂ) (V : ℂ) :
    Differentiable ℂ (fun U => primeRest p s U V) := restPolynomial_entire_left _ _ _ _ _ _

@[fun_prop] theorem primeRest_entire_right (p : ℕ) (s : Fin 4 → ℂ) (U : ℂ) :
    Differentiable ℂ (fun V => primeRest p s U V) := restPolynomial_entire_right _ _ _ _ _ _

@[simp] theorem primeRest_zero_shifts (p : ℕ) :
    primeRest p (fun _ => 0) 1 1 = (1-primeX p)^4*(1+4*primeX p+(primeX p)^2) := by
  simpa only [primeRest, primeRoot, neg_zero, Complex.cpow_zero] using restPolynomial_equal_shifts (primeX p)

end Sechstmoment.Source.NoDPLocalClosure
