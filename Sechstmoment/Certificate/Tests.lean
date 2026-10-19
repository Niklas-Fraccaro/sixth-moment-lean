import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Sechstmoment.Certificate.Data
import Sechstmoment.Certificate.TestPolynomials
import Sechstmoment.Zeta.Tests
import Std

/-!
# The manuscript's actual U/V tests

These definitions use the Riemann zeta function and its complex derivatives.
They instantiate the exact phase projection of §1.1, and also assemble the 250
rows of Appendix A with their unscaled integer coefficients. They introduce no
asymptotic moment formula. The profile sum is indexed by `n+1` to exclude zero;
for the supported profiles and `T > 1` it is proved to be a finite Dirichlet sum.
-/

namespace Sechstmoment

open Complex Polynomial
open scoped ComplexConjugate

noncomputable section

/-- The raw 250-row test behind (5.3). The profile selector can supply the
smooth U family and the zero-extended beta V family at a fixed stage `n`. -/
def certificateRawZetaTest (profiles : TestType → ℝ → ℝ → ℝ) (T t : ℝ) : ℂ :=
  (certificate.map fun d => (d.coefficient : ℂ) *
    rawZetaTest d.typ T t (manuscriptTestPolynomial d.degree)
      (profiles d.typ ((d.A : ℝ) / base)) (profiles d.typ ((d.B : ℝ) / base))).sum

/-- The actual complete test from the attached certificate. -/
def certificateZetaTest (profiles : TestType → ℝ → ℝ → ℝ) (T t : ℝ) : ℂ :=
  phaseProjection (criticalChi t) (certificateRawZetaTest profiles T t)

private theorem phaseProjection_list_sum (χ : ℂ) (l : List ℂ) :
    phaseProjection χ l.sum = (l.map (phaseProjection χ)).sum := by
  induction l with
  | nil => simp [phaseProjection]
  | cons a l ih => simp only [List.sum_cons, List.map_cons, phaseProjection_add, ih]

/-- Linearity identifies the projected raw certificate with the literal sum
of the 250 projected tests, with the exact Appendix A coefficients. -/
theorem certificateZetaTest_eq_sum (profiles : TestType → ℝ → ℝ → ℝ) (T t : ℝ) :
    certificateZetaTest profiles T t =
      (certificate.map fun d => (d.coefficient : ℂ) *
        projectedZetaTest d.typ T t (manuscriptTestPolynomial d.degree)
          (profiles d.typ ((d.A : ℝ) / base)) (profiles d.typ ((d.B : ℝ) / base))).sum := by
  unfold certificateZetaTest certificateRawZetaTest
  rw [phaseProjection_list_sum, List.map_map]
  congr 2
  funext d
  change phaseProjection (criticalChi t) ((d.coefficient : ℂ) * _) = _
  have hcast : (d.coefficient : ℂ) = ((d.coefficient : ℝ) : ℂ) := by norm_cast
  rw [hcast, phaseProjection_real_smul]
  rfl

theorem certificateZetaTest_real_structure (profiles : TestType → ℝ → ℝ → ℝ) (T t : ℝ) :
    certificateZetaTest profiles T t =
      criticalChi t ^ 3 * star (certificateZetaTest profiles T t) :=
  zeta_phaseProjection_real_structure t _

theorem certificateZetaTest_mixed_re (profiles : TestType → ℝ → ℝ → ℝ) (T t : ℝ) :
    riemannZeta (criticalLinePoint t) ^ 3 * star (certificateZetaTest profiles T t) =
      ((riemannZeta (criticalLinePoint t) ^ 3 * star (certificateRawZetaTest profiles T t)).re : ℂ) :=
  zeta_phaseProjection_mixed_re t _

theorem certificateZetaTest_gram (profiles profiles' : TestType → ℝ → ℝ → ℝ) (T t : ℝ) :
    certificateZetaTest profiles T t * star (certificateZetaTest profiles' T t) =
      (1 / 2 : ℂ) * ((certificateRawZetaTest profiles T t *
        star (certificateRawZetaTest profiles' T t) + (star (criticalChi t)) ^ 3 *
        certificateRawZetaTest profiles T t * certificateRawZetaTest profiles' T t).re : ℂ) :=
  zeta_phaseProjection_gram t _ _

end

end Sechstmoment
