import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Rat.Cast.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Sechstmoment.Arithmetic.QuadraticDivisor.Definitions
import Std

/-!
# Typed source boundaries

These are specifications, not axioms or proofs of the cited analytic inputs.
In particular the rectangular moment theorem and the manuscript's normalized
polar generator do not appear as hypotheses. All source integrands and source
main terms below are concrete functions.

BBLR: arXiv:1609.02539v1, Proposition 3.1 and the oriented calculation on p.17.
DP: arXiv:2606.27323v2, §5.2, k=1, the reversed-conjugation calculation and
its four displayed residues. It has the literal `χ(s) A(1-s)^2` orientation,
not the preceding theorem's orientation with an unchanged complex shift tuple.
The raw shifts,
the factor T/(2π), log(y)^6, and the two conjugated polynomial amplifiers are
retained. Own normalization, polarization and holomorphic pole removal remain
separate proof obligations.
-/

namespace Sechstmoment.Source
open Complex MeasureTheory Set Polynomial Filter Asymptotics
open Classical
open scoped BigOperators Topology

noncomputable section

/-- Oriented source input, restricted to precisely the nontrivial range in
the proof of Proposition 3.1. A swapped block is handled by swapping its data.
No rectangular twisted-moment conclusion occurs in this specification. -/
def BBLRv1OrientedInput : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∀ K : ℝ, 1 ≤ K →
  ∀ bounds : ℕ → ℝ, (∀ j, 0 ≤ bounds j) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : QuadraticScales) (α β : ℕ → ℂ)
      (W : Fin 5 → ℝ → ℝ), QuadraticAdmissible ε δ K bounds q α β W →
      ∀ positive : Bool, ‖signedQuadraticDiscrepancy positive q α β W‖ ≤
        C*((q.mass*q.H^2)^ε*orientedQuadraticMajorant q+q.mass^ε*q.H^2)

end
end Sechstmoment.Source
