import Mathlib.MeasureTheory.Integral.Prod
import Sechstmoment.Certificate.Kernels.Unbalanced.Kernel
import Sechstmoment.Denominator.Measures.DiagonalMeasureLimit

/-! Literal unbalanced denominator moments, with the original chi phase,
three positive profiles, one negative profile and the original minus kernel.
These definitions introduce no analytic hypotheses. -/
namespace Sechstmoment
open Complex Real Polynomial MeasureTheory Filter Set
open scoped BigOperators Topology ContDiff
noncomputable section

def d04UnbalancedAmplifier (T t : ℝ) (ρ : Fin 4 → ℝ → ℝ) : ℂ :=
  profileDirichletSum T (ρ 0) (criticalLinePoint t) *
    profileDirichletSum T (ρ 1) (criticalLinePoint t) *
    profileDirichletSum T (ρ 2) (criticalLinePoint t) *
    profileDirichletSum T (ρ 3) (1-criticalLinePoint t)

def d04UnbalancedShiftedMoment (T : ℝ) (σ : Fin 2 → ℂ)
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) : ℂ :=
  ∫ t : ℝ, (Φ (t/T) : ℂ) * (criticalChi t)⁻¹ *
    zetaCPlus T t (σ 0) * zetaCMinus T t (σ 1) * d04UnbalancedAmplifier T t ρ

def d04UnbalancedPolynomialMoment (T : ℝ) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) : ℂ :=
  ∫ t : ℝ, (Φ (t/T) : ℂ) * (criticalChi t)⁻¹ * zetaCp T t p *
    zetaPolynomialDerivative T q (1-criticalLinePoint t) * d04UnbalancedAmplifier T t ρ

def d04UnbalancedProfileKernel (p q : Fin 5 → ℝ) (ρ : Fin 4 → ℝ → ℝ) : ℝ :=
  ∫ a : Fin 4 → ℝ, (∏ i, ρ i (a i)) *
    denominatorMinusKernel p q (a 0) (a 1) (a 2) (a 3)

def d04UnbalancedEdgeProfile (ρ : Fin 4 → ℝ → ℝ) (x : D01EdgeSpace) : ℝ :=
  ρ 0 ((d01RowColumnSums x).1 0) * ρ 1 ((d01RowColumnSums x).1 1) *
    ρ 2 ((d01RowColumnSums x).1 2) * ρ 3 ((d01RowColumnSums x).2 2)

def d04UnbalancedShiftedEdgeIntegral (ρ : Fin 4 → ℝ → ℝ) (σ : Fin 2 → ℂ) : ℂ :=
  ∫ x : D01EdgeSpace, (d04UnbalancedEdgeProfile ρ x : ℂ) *
    Complex.exp (σ 0*((d01RowColumnSums x).2 0-1/2 : ℂ) +
      σ 1*(1/2-(d01RowColumnSums x).2 1 : ℂ)) ∂d01EdgeMeasure

def d04NegativeZetaArguments (T t : ℝ) (σ : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![1-criticalLinePoint t-σ 0/(Real.log T : ℂ),
    1-criticalLinePoint t+σ 1/(Real.log T : ℂ)]

def d04OneSidedRawSummand (X : ℝ) (s r : ℂ) (n : ℕ × ℕ) : ℂ :=
  (n.1+1 : ℂ)^(-s) * (n.2+1 : ℂ)^(-r) *
    (Real.exp (-((n.1+1 : ℝ)*(n.2+1 : ℝ))/X) : ℂ)

def d04OneSidedRawSeries (X : ℝ) (s r : ℂ) : ℂ :=
  ∑' n : ℕ × ℕ, d04OneSidedRawSummand X s r n

def d04OneSidedCenteredPair (T t : ℝ) (σ : Fin 2 → ℂ) : ℂ :=
  Complex.exp ((-σ 0+σ 1)/2) * d04OneSidedRawSeries (T^3)
    (d04NegativeZetaArguments T t σ 0) (d04NegativeZetaArguments T t σ 1)

/-- The pure time power must remain in the leading moment until its
physical time mean is evaluated; the Gamma correction is estimated separately. -/
def d04CenteringPurePower (T t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (z*(1-(Real.log (t/(2*Real.pi)) : ℂ)/(Real.log T : ℂ)))

def d04OneSidedShiftedMoment (T : ℝ) (σ : Fin 2 → ℂ)
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) : ℂ :=
  ∫ t : ℝ, (Φ (t/T) : ℂ) * d04CenteringPurePower T t (σ 0) *
    d04OneSidedCenteredPair T t σ * d04UnbalancedAmplifier T t ρ

def D04UnbalancedMinusAsymptotic : Prop :=
  ∀ (a : Fin 4 → ℝ), (∀ i, 0 < a i) → (∑ i, a i) < 1 →
  ∀ (ρ : Fin 4 → ℝ → ℝ), (∀ i, Continuous (ρ i)) →
    (∀ i, tsupport (ρ i) ⊆ Icc 0 (a i)) →
  ∀ (Φ : ℝ → ℝ), ContDiff ℝ ∞ Φ → tsupport Φ ⊆ Icc 1 2 →
  ∀ (p q : ℝ[X]), p.natDegree ≤ 4 → q.natDegree ≤ 4 →
    Tendsto (fun T : ℝ => d04UnbalancedPolynomialMoment T p q ρ Φ /
      (T*(Real.log T)^9 : ℂ)) atTop
      (𝓝 ((arithmeticFactor * (∫ x : ℝ, Φ x) *
        d04UnbalancedProfileKernel (fun i => p.coeff i.val) (fun i => q.coeff i.val) ρ : ℝ) : ℂ))

end
end Sechstmoment
