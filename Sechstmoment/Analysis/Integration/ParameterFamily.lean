import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Int.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Instances.Matrix
import Sechstmoment.Analysis.Complex.PartialDerivative
import Sechstmoment.Analysis.Integration.ComplexParameter
import Std


namespace Sechstmoment
open Filter MeasureTheory Set
open scoped Topology BigOperators
noncomputable section
set_option maxHeartbeats 1000000

namespace ComplexIntegralFamily

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [ProperSpace H]
  {X : Type*} [TopologicalSpace X]

def variableIntervalIntegral (F : ComplexIntegralFamily (univ : Set H) (X × ℝ))
    (a b : X → ℝ) (ha : Continuous a) (hb : Continuous b) :
    ComplexIntegralFamily (univ : Set H) X :=
  ((F.reindexAux (fun p : X × ℝ => (p.1,(b p.1-a p.1)*p.2+a p.1))
    (by fun_prop)).mulAux (fun p : X × ℝ => ((b p.1-a p.1 : ℝ):ℂ))
      (by fun_prop)).intervalIntegral isOpen_univ 0 1 (by norm_num)

theorem variableIntervalIntegral_value
    (F : ComplexIntegralFamily (univ : Set H) (X × ℝ))
    (a b : X → ℝ) (ha : Continuous a) (hb : Continuous b) (q : H) (x : X) :
    (F.variableIntervalIntegral a b ha hb).value q x =
      ∫ t in a x..b x, F.value q (x,t) := by
  change (∫ t in (0:ℝ)..1,
    ((b x-a x:ℝ):ℂ)*F.value q (x,(b x-a x)*t+a x)) = _
  rw [intervalIntegral.integral_const_mul]
  have h := intervalIntegral.smul_integral_comp_mul_add
    (fun t => F.value q (x,t)) (a := (0:ℝ)) (b := 1) (b x-a x) (a x)
  simpa only [Complex.real_smul,mul_zero,zero_add,mul_one,sub_add_cancel] using h

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

def ofContDiff (F : H × Y → ℂ) (hF : ContDiff ℂ 1 F)
    (g : X → Y) (hg : Continuous g) : ComplexIntegralFamily (univ : Set H) X where
  value q x := F (q,g x)
  derivative q x := complexFirstFDeriv F (q,g x)
  continuous_value := hF.continuous.comp (by fun_prop)
  continuous_derivative := by
    have hc : Continuous (complexFirstFDeriv F) :=
      (hF.continuous_fderiv (by norm_num)).clm_comp_const _
    exact hc.comp (by fun_prop)
  hasFDerivAt q _ x := complexFirstFDeriv_hasFDerivAt F (q,g x)
    (hF.differentiable (by norm_num) _)

omit [ProperSpace H] in
theorem contDiff_value (F : ComplexIntegralFamily (univ : Set H) X) (x : X) :
    ContDiff ℂ 1 (fun q => F.value q x) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun q => F.derivative q x, ?_, fun q => F.hasFDerivAt q (mem_univ q) x⟩
  exact F.continuous_derivative.comp
    ((continuous_id.subtype_mk (fun q => mem_univ q)).prodMk continuous_const)

end ComplexIntegralFamily

end
end Sechstmoment
