import Mathlib.MeasureTheory.Integral.Prod
import SixthMoment.Arithmetic.Factor.Definitions
import SixthMoment.Certificate.Kernels.Balanced.PolytopeDensityBridge
import SixthMoment.Zeta.Amplifiers
import SixthMoment.Zeta.Generators

namespace SixthMoment
open Complex Real Polynomial MeasureTheory Filter Set
open scoped BigOperators Topology ContDiff
noncomputable section

def d02BalancedAmplifier (T t : ℝ) (ρ : Fin 4 → ℝ → ℝ) : ℂ :=
  profileDirichletSum T (ρ 0) (criticalLinePoint t) *
    profileDirichletSum T (ρ 1) (criticalLinePoint t) *
    profileDirichletSum T (ρ 2) (1-criticalLinePoint t) *
    profileDirichletSum T (ρ 3) (1-criticalLinePoint t)

def d02BalancedShiftedMoment (T : ℝ) (σ : Fin 2 → ℂ)
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) : ℂ :=
  ∫ t : ℝ, (Φ (t/T) : ℂ) * zetaCPlus T t (σ 0) *
    zetaCMinus T t (σ 1) * d02BalancedAmplifier T t ρ

def d02BalancedPolynomialMoment (T : ℝ) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) : ℂ :=
  ∫ t : ℝ, (Φ (t/T) : ℂ) * zetaCp T t p *
    zetaPolynomialDerivative T q (1-criticalLinePoint t) *
      d02BalancedAmplifier T t ρ

def d02BalancedProfileKernel (p q : Fin 5 → ℝ) (ρ : Fin 4 → ℝ → ℝ) : ℝ :=
  ∫ a : Fin 4 → ℝ, (∏ i, ρ i (a i)) *
    denominatorZeroKernel p q (a 0) (a 1) (a 2) (a 3)

def D02BalancedDenominatorAsymptotic : Prop :=
  ∀ (a : Fin 4 → ℝ), (∀ i, 0 < a i) → (∑ i, a i) < 1 →
  ∀ (ρ : Fin 4 → ℝ → ℝ), (∀ i, Continuous (ρ i)) →
    (∀ i, tsupport (ρ i) ⊆ Icc 0 (a i)) →
  ∀ (Φ : ℝ → ℝ), ContDiff ℝ ∞ Φ → tsupport Φ ⊆ Icc 1 2 →
  ∀ (p q : ℝ[X]), p.natDegree ≤ 4 → q.natDegree ≤ 4 →
    Tendsto (fun T : ℝ => d02BalancedPolynomialMoment T p q ρ Φ /
      (T*(Real.log T)^9 : ℂ)) atTop
      (𝓝 ((arithmeticFactor * (∫ x : ℝ, Φ x) *
        d02BalancedProfileKernel (fun i => p.coeff i.val) (fun i => q.coeff i.val) ρ : ℝ) : ℂ))

end
end SixthMoment
