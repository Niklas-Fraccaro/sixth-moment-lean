import Sechstmoment.Denominator.Gram.Algebra
import Sechstmoment.Denominator.Gram.ProfileCoordinates

namespace Sechstmoment
open MeasureTheory Polynomial
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0

def d06GramSwapProfiles (ρ : Fin 4 → ℝ → ℝ) : Fin 4 → ℝ → ℝ :=
  ![ρ 2,ρ 3,ρ 0,ρ 1]

def d06GramKernel (τ σ : TestType) (p q : ℝ[X]) (ρ : Fin 4 → ℝ → ℝ) : ℝ :=
  match τ,σ with
  | .U,.U => (d02BalancedProfileKernel (fun i => p.coeff i.val) (fun i => q.coeff i.val)
      (d06UUConjugateProfiles ρ) +
    d02BalancedProfileKernel (fun i => p.coeff i.val)
      (fun i => (reflectedTestPolynomial q).coeff i.val) (d06UUReflectedProfiles ρ))/2
  | .V,.V => d02BalancedProfileKernel (fun i => p.coeff i.val)
      (fun i => q.coeff i.val) ρ/2
  | .U,.V => (d04UnbalancedPlusProfileKernel (fun i => p.coeff i.val)
      (fun i => q.coeff i.val) ρ +
    d04UnbalancedProfileKernel (fun i => p.coeff i.val)
      (fun i => (reflectedTestPolynomial q).coeff i.val) (d06UVReflectedProfiles ρ))/2
  | .V,.U => (d04UnbalancedPlusProfileKernel (fun i => q.coeff i.val)
      (fun i => p.coeff i.val) (d06GramSwapProfiles ρ) +
    d04UnbalancedProfileKernel (fun i => q.coeff i.val)
      (fun i => (reflectedTestPolynomial p).coeff i.val)
        (d06UVReflectedProfiles (d06GramSwapProfiles ρ)))/2

def d06GramPerm0312 : Fin 4 ≃ Fin 4 :=
  Equiv.ofBijective (fun i => (![0,3,1,2] : Fin 4 → Fin 4) i) (by decide)

def d06GramPerm0213 : Fin 4 ≃ Fin 4 :=
  Equiv.ofBijective (fun i => (![0,2,1,3] : Fin 4 → Fin 4) i) (by decide)

def d06GramPerm0231 : Fin 4 ≃ Fin 4 :=
  Equiv.ofBijective (fun i => (![0,2,3,1] : Fin 4 → Fin 4) i) (by decide)

def d06GramPerm1230 : Fin 4 ≃ Fin 4 :=
  Equiv.ofBijective (fun i => (![1,2,3,0] : Fin 4 → Fin 4) i) (by decide)

def d06ProfileKernelIntegral (ρ : Fin 4 → ℝ → ℝ) (F : (Fin 4 → ℝ) → ℝ) : ℝ :=
  ∫ a : Fin 4 → ℝ, (∏ i,ρ i (a i))*F a

theorem d06BalancedKernel_permute (p q : Fin 5 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (e : Fin 4 ≃ Fin 4) :
    d02BalancedProfileKernel p q (fun i => ρ (e i)) =
      d06ProfileKernelIntegral ρ (fun a => denominatorZeroKernel p q
        (a (e 0)) (a (e 1)) (a (e 2)) (a (e 3))) :=
  d06ProfileIntegral_reindex e ρ _

theorem d06UnbalancedKernel_permute (p q : Fin 5 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (e : Fin 4 ≃ Fin 4) :
    d04UnbalancedProfileKernel p q (fun i => ρ (e i)) =
      d06ProfileKernelIntegral ρ (fun a => denominatorMinusKernel p q
        (a (e 0)) (a (e 1)) (a (e 2)) (a (e 3))) :=
  d06ProfileIntegral_reindex e ρ _

theorem d06BalancedKernel_UUConjugate (p q : Fin 5 → ℝ) (ρ : Fin 4 → ℝ → ℝ) :
    d02BalancedProfileKernel p q (d06UUConjugateProfiles ρ) =
      d06ProfileKernelIntegral ρ (fun a => denominatorZeroKernel p q (a 0) (a 3) (a 1) (a 2)) := by
  have he : (fun i => ρ (d06GramPerm0312 i)) = d06UUConjugateProfiles ρ := by
    funext i
    fin_cases i <;> rfl
  have h := d06BalancedKernel_permute p q ρ d06GramPerm0312
  rw [he] at h
  exact h

theorem d06BalancedKernel_UUReflected (p q : Fin 5 → ℝ) (ρ : Fin 4 → ℝ → ℝ) :
    d02BalancedProfileKernel p q (d06UUReflectedProfiles ρ) =
      d06ProfileKernelIntegral ρ (fun a => denominatorZeroKernel p q (a 0) (a 2) (a 1) (a 3)) := by
  have he : (fun i => ρ (d06GramPerm0213 i)) = d06UUReflectedProfiles ρ := by
    funext i
    fin_cases i <;> rfl
  have h := d06BalancedKernel_permute p q ρ d06GramPerm0213
  rw [he] at h
  exact h

theorem d06UnbalancedKernel_UVReflected (p q : Fin 5 → ℝ) (ρ : Fin 4 → ℝ → ℝ) :
    d04UnbalancedProfileKernel p q (d06UVReflectedProfiles ρ) =
      d06ProfileKernelIntegral ρ (fun a => denominatorMinusKernel p q (a 0) (a 2) (a 3) (a 1)) := by
  have he : (fun i => ρ (d06GramPerm0231 i)) = d06UVReflectedProfiles ρ := by
    funext i
    fin_cases i <;> rfl
  have h := d06UnbalancedKernel_permute p q ρ d06GramPerm0231
  rw [he] at h
  exact h

theorem d06UnbalancedPlusKernel_coordinates (p q : Fin 5 → ℝ) (ρ : Fin 4 → ℝ → ℝ) :
    d04UnbalancedPlusProfileKernel p q ρ =
      d06ProfileKernelIntegral ρ (fun a => denominatorMinusKernel q p (a 1) (a 2) (a 3) (a 0)) := by
  have he : (fun i => ρ (d06GramPerm1230 i)) = d04UnbalancedConjugateProfiles ρ := by
    funext i
    fin_cases i <;> rfl
  have h := d06UnbalancedKernel_permute q p ρ d06GramPerm1230
  rw [he] at h
  exact h

end
end Sechstmoment
