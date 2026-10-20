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
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
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
import Sechstmoment.Analysis.Mellin.VerticalIntegral
import Sechstmoment.Arithmetic.QuadraticDivisor.Definitions
import Sechstmoment.Zeta.Moments.Definitions
import Sechstmoment.Zeta.Moments.SixTerms
import Std


namespace Sechstmoment.Source
open Complex MeasureTheory Set Filter
open scoped BigOperators
open Classical

noncomputable section

def bblrVStar (G : ℂ → ℂ) (x : ℝ) : ℂ :=
  verticalIntegral 1 fun z => G z/z *
    (2*Real.pi : ℂ)^(-2*z)*(x : ℂ)^(-z)

def positiveQuadProduct (n : Fin 4 → ℕ) : ℕ :=
  (n 0+1)*(n 1+1)*(n 2+1)*(n 3+1)

def diagonalQuadRelation (a b : ℕ) (n : Fin 4 → ℕ) : Prop :=
  a*(n 0+1)*(n 1+1) = b*(n 2+1)*(n 3+1)

def bblrDiagonalSummand (G : ℂ → ℂ) (α : MomentShifts)
    (a b : ℕ) (t : ℝ) (n : Fin 4 → ℕ) : ℂ :=
  bblrVStar G (positiveQuadProduct n/t^2) /
    ((a*b : ℕ) : ℂ)^(1/2 : ℂ) /
    ∏ j : Fin 4, (n j+1 : ℂ)^(1/2+α j)

def bblrDiagonalTerm (G : ℂ → ℂ) (α : MomentShifts)
    (a b : ℕ) (t : ℝ) : ℂ :=
  ∑' n : Fin 4 → ℕ,
    if diagonalQuadRelation a b n then bblrDiagonalSummand G α a b t n else 0

def bblrSixMainTerms (T a b : ℝ) (α : MomentShifts) (G : ℂ → ℂ)
    (f g Φ : ℝ → ℝ) : ℂ :=
  ∑ j : Fin 6, ∑ m ∈ Finset.Icc 1 ⌊T^a⌋₊, ∑ n ∈ Finset.Icc 1 ⌊T^b⌋₊,
    (f (Real.log m/Real.log T) : ℂ)*(g (Real.log n/Real.log T) : ℂ)*
      ∫ t : ℝ, (Φ (t/T) : ℂ)*
        (t/(2*Real.pi) : ℂ)^(bblrSixPhaseExponents α j)*
        bblrDiagonalTerm G (bblrSixShifts α j) m n t

def bblrMomentDiscrepancy (T a b : ℝ) (α : MomentShifts) (G : ℂ → ℂ)
    (f g Φ : ℝ → ℝ) : ℂ :=
  twistedFourthMoment T α f g Φ-bblrSixMainTerms T a b α G f g Φ

def BBLREntireWeight (G : ℂ → ℂ) (_α : MomentShifts) : Prop :=
  AnalyticOnNhd ℂ G univ ∧ (∀ z, G (-z)=G z) ∧ G 0=1 ∧
    ∀ R : ℝ, 0 < R → ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, |z.re| ≤ R → ‖G z‖*(1+|z.im|)^N ≤ C

def BBLRPoleCancellingWeight (G : ℂ → ℂ) (α : MomentShifts) : Prop :=
  BBLREntireWeight G α ∧ ∀ k : Fin 6, ∀ i : Fin 2, ∀ j : Fin 2,
    let ρ := -((bblrSixShifts α k) i.castSucc.castSucc+
      (bblrSixShifts α k) ⟨j.val+2, by omega⟩)/2
    ρ ≠ 0 → G ρ=0

end
end Sechstmoment.Source
