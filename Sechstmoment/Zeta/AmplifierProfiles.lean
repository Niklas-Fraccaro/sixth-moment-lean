import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Rat.Cast.Order
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Sechstmoment.Analysis.Profiles.Polynomial
import Sechstmoment.Zeta.Moments.AnalyticMomentLinearity
import Std


namespace Sechstmoment
open Complex MeasureTheory Set Filter
open scoped Topology BigOperators

set_option maxHeartbeats 0

theorem polynomialProfileDirichletSum_add {T : ℝ} (hT : 1 < T) (η : ℝ)
    (P Q : Polynomial ℝ) (s : ℂ) :
    profileDirichletSum T (zeroExtendedPolynomialProfile η (P+Q)) s =
      profileDirichletSum T (zeroExtendedPolynomialProfile η P) s+
        profileDirichletSum T (zeroExtendedPolynomialProfile η Q) s := by
  rw [zeroExtendedPolynomialProfile_add]
  exact profileDirichletSum_add hT η _ _
    (fun x hx => zeroExtendedPolynomialProfile_zero_above η P x hx)
    (fun x hx => zeroExtendedPolynomialProfile_zero_above η Q x hx) s

theorem polynomialProfileDirichletSum_sub {T : ℝ} (hT : 1 < T) (η : ℝ)
    (P Q : Polynomial ℝ) (s : ℂ) :
    profileDirichletSum T (zeroExtendedPolynomialProfile η (P-Q)) s =
      profileDirichletSum T (zeroExtendedPolynomialProfile η P) s-
        profileDirichletSum T (zeroExtendedPolynomialProfile η Q) s := by
  rw [zeroExtendedPolynomialProfile_sub]
  exact profileDirichletSum_sub hT η _ _
    (fun x hx => zeroExtendedPolynomialProfile_zero_above η P x hx)
    (fun x hx => zeroExtendedPolynomialProfile_zero_above η Q x hx) s

end Sechstmoment
