import Sechstmoment.Arithmetic.Euler.Convolution.DirichletCoefficients
import Sechstmoment.Arithmetic.Euler.Convolution.LocalInverse
import Sechstmoment.Arithmetic.Euler.Convolution.RemainderBridge

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Sechstmoment.Source.NoDPGlobalConvolution
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest
open scoped BigOperators
noncomputable section

def originalFactor (s : Fin 4 → ℂ) : ℕ → ℂ := eulerCoeff (fun p h =>
  originalPoleTail (primeRoot p (s 0)) (primeRoot p (s 1)) (primeRoot p (s 2))
    (primeRoot p (s 3)) ((p:ℂ)^(-(1-s 0))) (1/((p:ℂ)-1)) h)

def originalCoeff (s : Fin 4 → ℂ) (a b : ℕ) : ℂ :=
  eulerCoeff (fun p h => primeOriginalWeight p s h) (a*b)

theorem originalCoeff_factor (s : Fin 4 → ℂ) (a b : ℕ) :
    originalCoeff s a b = ((a*b:ℕ):ℂ)^(-s 0) * originalFactor s (a*b) := by
  unfold originalCoeff primeOriginalWeight
  rw [eulerCoeff_pointwise_product]
  change eulerCoeff (fun p h => ((p:ℂ)^(-s 0))^h) (a*b) * originalFactor s (a*b) = _
  rw [← powerAF_euler]
  by_cases h : a*b = 0
  · simp [h,originalFactor]
  · rw [powerAF_apply _ _ h]

theorem local_sixfold_inverse (s : Fin 4 → ℂ) (p : Nat.Primes) (h k : ℕ) :
    primeWeight p.val s (h+k) = localConvolution (restLocal s)
      (fun p i j => tripleLocal s p.val i * tripleLocal s p.val j) p h k := by
  simpa only [localConvolution, restLocal, tripleLocal, primeWeight, residueRest, mul_assoc]
    using regularizedCoeff_inverse (primeX p.val * primeRoot p.val (s 1))
      (primeX p.val * primeRoot p.val (s 2)) (primeX p.val * primeRoot p.val (s 3))
      (fun h k => primeWeight p.val s (h+k)) h k

theorem originalCoeff_weightEuler (s : Fin 4 → ℂ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4)
    (hs : ∀ j, ‖s j‖ ≤ ρ) (a b : ℕ) :
    originalCoeff s a b = eulerCoeff (fun p h => primeWeight p s h) (a*b) := by
  apply eulerCoeff_congr
  intro p hp h _
  exact prime_residue_cancellation p hp s ρ hρ0 hρ hs h

theorem originalCoeff_convolution (s : Fin 4 → ℂ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4)
    (hs : ∀ j, ‖s j‖ ≤ ρ) (a b : ℕ) :
    originalCoeff s a b = ∑ d ∈ a.divisors, ∑ e ∈ b.divisors,
      gamma s (d,e) * tripleCoeff s (a/d) * tripleCoeff s (b/e) := by
  rw [originalCoeff_weightEuler s ρ hρ0 hρ hs a b, ← pairEuler_total]
  have H : (fun p : Nat.Primes => fun h k => primeWeight p.val s (h+k)) =
      localConvolution (restLocal s) (fun p i j => tripleLocal s p.val i * tripleLocal s p.val j) := by
    funext p h k
    exact local_sixfold_inverse s p h k
  rw [H, pairEuler_convolution _ _ (restLocal_base s)
    (fun p => by simp [tripleLocal_base])]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  rw [← gamma_eq_pairEuler, pairEuler_separable _ _
    (fun p => tripleLocal_base s p.val) (fun p => tripleLocal_base s p.val), ← tripleCoeff_euler]
  ring

theorem originalFactor_convolution (s : Fin 4 → ℂ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4)
    (hs : ∀ j, ‖s j‖ ≤ ρ) (a b : ℕ) :
    ((a*b:ℕ):ℂ)^(-s 0) * originalFactor s (a*b) =
      ∑ d ∈ a.divisors, ∑ e ∈ b.divisors,
        gamma s (d,e) * tripleCoeff s (a/d) * tripleCoeff s (b/e) := by
  rw [← originalCoeff_factor]
  exact originalCoeff_convolution s ρ hρ0 hρ hs a b

end
end Sechstmoment.Source.NoDPGlobalConvolution
