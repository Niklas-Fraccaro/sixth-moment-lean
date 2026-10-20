import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic
import Mathlib.Tactic.Ring

namespace SixthMoment
open Complex Metric MeasureTheory Set
open scoped BigOperators Topology

set_option maxHeartbeats 1000000

noncomputable def complexFirstFDeriv
    {H Y : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (F : H × Y → ℂ) (p : H × Y) : H →L[ℂ] ℂ :=
  (fderiv ℂ F p).comp (ContinuousLinearMap.inl ℂ H Y)

theorem complexFirstFDeriv_hasFDerivAt
    {H Y : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (F : H × Y → ℂ) (p : H × Y) (hF : DifferentiableAt ℂ F p) :
    HasFDerivAt (fun x => F (x,p.2)) (complexFirstFDeriv F p) p.1 :=
  hF.hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left p.1 p.2)

theorem complexFirstFDeriv_continuousAt
    {H Y : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (F : H × Y → ℂ) (p : H × Y) (hF : ContDiffAt ℂ 1 F p) :
    ContinuousAt (complexFirstFDeriv F) p :=
  (hF.continuousAt_fderiv (by norm_num)).clm_comp continuousAt_const

end SixthMoment
