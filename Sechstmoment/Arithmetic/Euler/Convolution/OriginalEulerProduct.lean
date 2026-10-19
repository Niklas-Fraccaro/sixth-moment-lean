import Sechstmoment.Arithmetic.Euler.Convolution.SixZeta

/-! The global identity also agrees with the Euler product of the original local double series. -/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Sechstmoment.Source.NoDPGlobalConvolution
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest
open scoped BigOperators
noncomputable section

theorem prime_zeta_term (p : ℕ) (hp : p ≠ 0) (z u : ℂ) :
    (p:ℂ)^(-(1+u+z)) = primeX p * primeRoot p z * (p:ℂ)^(-u) := by
  rw [← primeX_mul_root p hp, ← Complex.cpow_add _ _ (by exact_mod_cast hp)]
  congr 1
  ring

theorem tripleZeta_euler_hasProd (s : Fin 4 → ℂ) (ρ : ℝ) (hs : ∀ j, ‖s j‖ ≤ ρ)
    (u : ℂ) (hu : ρ < u.re) :
    HasProd (fun p : Nat.Primes => (primeDen p.val s ((p.val:ℂ)^(-u)))⁻¹) (tripleZeta s u) := by
  have H := (riemannZeta_eulerProduct_hasProd (shifted_zeta_region s ρ hs u hu 0)).mul
    ((riemannZeta_eulerProduct_hasProd (shifted_zeta_region s ρ hs u hu 1)).mul
      (riemannZeta_eulerProduct_hasProd (shifted_zeta_region s ρ hs u hu 2)))
  have H1 : (0 : Fin 3).succ = (1 : Fin 4) := by decide
  have H2 : (1 : Fin 3).succ = (2 : Fin 4) := by decide
  have H3 : (2 : Fin 3).succ = (3 : Fin 4) := by decide
  rw [H1,H2,H3] at H
  apply H.congr_fun
  intro p
  simp only [prime_zeta_term p.val p.property.ne_zero, primeDen, den3, mul_inv]
  ring

theorem prime_original_double_rational (p : Nat.Primes) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (u v : ℂ)
    (hu : -ρ ≤ u.re) (hv : -ρ ≤ v.re) :
    doubleSeries (primeOriginalWeight p.val s) ((p.val:ℂ)^(-u)) ((p.val:ℂ)^(-v)) =
      primeRest p.val s ((p.val:ℂ)^(-u)) ((p.val:ℂ)^(-v)) /
        (primeDen p.val s ((p.val:ℂ)^(-u)) * primeDen p.val s ((p.val:ℂ)^(-v))) := by
  rw [show primeOriginalWeight p.val s = primeWeight p.val s from
    funext (prime_residue_cancellation p.val p.property s ρ hρ0 hρ hs)]
  exact prime_double_rational p.val p.property s ρ hρ0 hρ hs _ _
    (prime_cpow_bound p u ρ hu) (prime_cpow_bound p v ρ hv)

/-- Genuine original Euler factors, not a definition of the global Dirichlet series. -/
theorem originalDirichlet_euler_hasProd (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (u v : ℂ)
    (hu : ρ < u.re) (hv : ρ < v.re) :
    HasProd (fun p : Nat.Primes => doubleSeries (primeOriginalWeight p.val s)
      ((p.val:ℂ)^(-u)) ((p.val:ℂ)^(-v))) (originalDirichlet s u v) := by
  have H := (restDirichlet_euler_hasProd s ρ hρ0 hρ hs u v (by linarith) (by linarith)).mul
    ((tripleZeta_euler_hasProd s ρ hs u hu).mul (tripleZeta_euler_hasProd s ρ hs v hv))
  rw [originalDirichlet_six_zeta s ρ hρ0 hρ hs u v hu hv]
  apply H.congr_fun
  intro p
  rw [prime_original_double_rational p s ρ hρ0 hρ hs u v (by linarith) (by linarith),
    div_eq_mul_inv,mul_inv]

theorem originalDirichlet_eq_euler (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (u v : ℂ)
    (hu : ρ < u.re) (hv : ρ < v.re) :
    originalDirichlet s u v = ∏' p : Nat.Primes,
      doubleSeries (primeOriginalWeight p.val s) ((p.val:ℂ)^(-u)) ((p.val:ℂ)^(-v)) :=
  (originalDirichlet_euler_hasProd s ρ hρ0 hρ hs u v hu hv).tprod_eq.symm

end
end Sechstmoment.Source.NoDPGlobalConvolution
