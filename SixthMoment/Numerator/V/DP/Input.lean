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
import SixthMoment.Analysis.Profiles.Classes
import SixthMoment.Numerator.V.DP.MainTerm
import SixthMoment.Zeta.Moments.Definitions
import Std


namespace SixthMoment.Source
open Complex MeasureTheory Set Polynomial Filter Asymptotics
open Classical
open scoped BigOperators Topology

noncomputable section

def DPv2Input : Prop :=
  ∀ (η : ℝ), 0 < η → η < 1/4 →
  ∀ (P : ℝ[X]) (Φ : ℝ → ℝ), SmoothDyadicWeight Φ →
  ∀ (K : Set MomentShifts), IsCompact K → (∀ σ ∈ K, DPSeparated σ) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K,
      ‖chiTwistedFourthMoment T (rawMomentShifts T σ)
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) Φ -
        dpRawMainTerm T η P Φ (rawMomentShifts T σ)‖ ≤ C*T*(Real.log T)^8

end
end SixthMoment.Source
