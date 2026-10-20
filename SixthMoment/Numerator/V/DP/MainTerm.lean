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
import SixthMoment.Arithmetic.Factor.Definitions
import SixthMoment.Zeta.Moments.Shifts
import Std


namespace SixthMoment.Source
open Complex MeasureTheory Set Polynomial Filter Asymptotics
open Classical
open scoped BigOperators Topology

noncomputable section

def DPSeparated (α : MomentShifts) : Prop :=
  Function.Injective (![ -α 0, -α 1, α 2, α 3] : Fin 4 → ℂ)

def dpTripleIntegral (y : ℝ) (P : ℝ[X]) (β γ δ : ℂ) : ℂ :=
  ∫ x : ℝ in 0..1, ∫ v : ℝ in 0..(1-x), ∫ w : ℝ in 0..(1-x-v),
    ((Polynomial.eval (1-x-v-w : ℝ) P : ℝ) : ℂ)*
      Complex.exp ((Real.log y : ℂ)*(-β*x+γ*v+δ*w))

def dpFourResidues (T y : ℝ) (P : ℝ[X]) (α : MomentShifts) : ℂ :=
  Complex.exp ((Real.log (T/(2*Real.pi)) : ℂ)*(-α 0-α 2-α 3))*
      (dpTripleIntegral y P (α 1) (α 2) (α 3))^2 /
      ((α 1-α 0)*(α 0+α 2)*(α 0+α 3)) +
    Complex.exp ((Real.log (T/(2*Real.pi)) : ℂ)*(-α 1-α 2-α 3))*
      (dpTripleIntegral y P (α 0) (α 2) (α 3))^2 /
      ((α 0-α 1)*(α 1+α 2)*(α 1+α 3)) +
    Complex.exp ((Real.log (T/(2*Real.pi)) : ℂ)*(-α 3))*
      (dpTripleIntegral y P (α 1) (-α 0) (α 3))^2 /
      ((α 1+α 2)*(α 0+α 2)*(α 2-α 3)) +
    Complex.exp ((Real.log (T/(2*Real.pi)) : ℂ)*(-α 2))*
      (dpTripleIntegral y P (α 1) (α 2) (-α 0))^2 /
      ((α 1+α 3)*(α 3-α 2)*(α 0+α 3))

def dpRawMainTerm (T η : ℝ) (P : ℝ[X]) (Φ : ℝ → ℝ)
    (α : MomentShifts) : ℂ :=
  (arithmeticFactor : ℂ)*(T : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*
    ((Real.log (T^η))^6 : ℝ)*dpFourResidues T (T^η) P α

end
end SixthMoment.Source
