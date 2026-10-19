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
import Sechstmoment.Analysis.Alternants.Regularity
import Sechstmoment.Analysis.Integration.ParameterFamily
import Std

/-! Holomorphic continuation of the exponential alternant through all source
collisions.  Its derivatives are obtained from the defining compact integrals. -/

namespace Sechstmoment
open Filter MeasureTheory Set
open scoped Topology BigOperators
noncomputable section
set_option maxHeartbeats 1000000

private def slopeExpFamily : ComplexIntegralFamily (univ : Set (ℂ × ℂ)) (Unit × ℝ) :=
  ComplexIntegralFamily.ofContDiff
    (fun p : (ℂ × ℂ) × ℂ => Complex.exp (p.1.1*p.1.2*p.2))
    (by fun_prop) (fun p : Unit × ℝ => (p.2:ℂ)) (by fun_prop)

theorem expFirstSlope_contDiff_joint :
    ContDiff ℂ 1 (fun p : ℂ × ℂ => expFirstSlope p.1 p.2) := by
  have h := ((slopeExpFamily.intervalIntegral isOpen_univ 0 1
    (by norm_num)).contDiff_value ())
  have heq : (fun p : ℂ × ℂ =>
      (slopeExpFamily.intervalIntegral isOpen_univ 0 1 (by norm_num)).value p ()) =
      (fun p => ∫ t in (0:ℝ)..1, Complex.exp ((p.2*p.1)*t)) := by
    funext p
    apply intervalIntegral.integral_congr
    intro t _
    change Complex.exp (p.1*p.2*(t:ℂ)) = _
    rw [mul_comm p.1 p.2]
  rw [heq] at h
  simp_rw [expFirstSlope_eq_integral]
  exact (by fun_prop : ContDiff ℂ 1 (fun p : ℂ × ℂ => p.1)).mul h

private def triangleExpFamily :
    ComplexIntegralFamily (univ : Set ((Fin 4 → ℂ) × ℂ)) (ℝ × ℝ) :=
  ComplexIntegralFamily.ofContDiff
    (fun p : ((Fin 4 → ℂ) × ℂ) × (ℂ × ℂ) =>
      Complex.exp (p.1.2*(p.1.1 0*p.2.1+p.1.1 1*p.2.2+
        p.1.1 2*(1-p.2.1-p.2.2))))
    (by fun_prop) (fun p : ℝ × ℝ => ((p.1:ℂ),(p.2:ℂ))) (by fun_prop)

private def triangleIntegralFamily :
    ComplexIntegralFamily (univ : Set ((Fin 4 → ℂ) × ℂ)) Unit :=
  ((triangleExpFamily.variableIntervalIntegral (fun _ => 0) (fun x => 1-x)
    continuous_const (by fun_prop)).reindexAux (fun p : Unit × ℝ => p.2)
      continuous_snd).intervalIntegral isOpen_univ 0 1 (by norm_num)

private theorem triangleIntegralFamily_value (p : (Fin 4 → ℂ) × ℂ) :
    triangleIntegralFamily.value p () =
      simplexTriangleExpIntegral (p.1 0) (p.1 1) (p.1 2) p.2 0 1 := by
  change (∫ x in (0:ℝ)..1,
    (triangleExpFamily.variableIntervalIntegral (fun _ => 0) (fun x => 1-x)
      continuous_const (by fun_prop)).value p x) = _
  simp_rw [ComplexIntegralFamily.variableIntervalIntegral_value]
  unfold simplexTriangleExpIntegral
  apply intervalIntegral.integral_congr
  intro x _
  apply intervalIntegral.integral_congr
  intro y _
  change Complex.exp (p.2*(p.1 0*(x:ℂ)+p.1 1*(y:ℂ)+
    p.1 2*(1-(x:ℂ)-(y:ℂ)))) = _
  push_cast
  congr 1
  ring

attribute [irreducible] triangleIntegralFamily

theorem simplexTriangleExpIntegral_contDiff_nodes :
    ContDiff ℂ 1 (fun p : (Fin 4 → ℂ) × ℂ =>
      simplexTriangleExpIntegral (p.1 0) (p.1 1) (p.1 2) p.2 0 1) := by
  have h := triangleIntegralFamily.contDiff_value ()
  simpa only [triangleIntegralFamily_value] using h

private def simplexDotExpFamily :
    ComplexIntegralFamily (univ : Set ((Fin 4 → ℂ) × ℂ)) ((ℝ × ℝ) × ℝ) :=
  ComplexIntegralFamily.ofContDiff
    (fun p : ((Fin 4 → ℂ) × ℂ) × ((ℂ × ℂ) × ℂ) =>
      Complex.exp (p.1.2*(p.1.1 0*p.2.1.1+p.1.1 1*p.2.1.2+
        p.1.1 2*p.2.2+p.1.1 3*(1-p.2.1.1-p.2.1.2-p.2.2))))
    (by fun_prop)
    (fun p : (ℝ × ℝ) × ℝ => (((p.1.1:ℂ),(p.1.2:ℂ)),(p.2:ℂ))) (by fun_prop)

private def simplexDotInnerFamily :
    ComplexIntegralFamily (univ : Set ((Fin 4 → ℂ) × ℂ)) (ℝ × ℝ) :=
  simplexDotExpFamily.variableIntervalIntegral (fun _ => 0) (fun p => 1-p.1-p.2)
    continuous_const (by fun_prop)

private def simplexDotMiddleFamily :
    ComplexIntegralFamily (univ : Set ((Fin 4 → ℂ) × ℂ)) ℝ :=
  simplexDotInnerFamily.variableIntervalIntegral (fun _ => 0) (fun x => 1-x)
    continuous_const (by fun_prop)

private def simplexDotIntegralFamily :
    ComplexIntegralFamily (univ : Set ((Fin 4 → ℂ) × ℂ)) Unit :=
  (simplexDotMiddleFamily.reindexAux (fun p : Unit × ℝ => p.2)
    continuous_snd).intervalIntegral isOpen_univ 0 1 (by norm_num)

private theorem simplexDotIntegralFamily_value (p : (Fin 4 → ℂ) × ℂ) :
    6*simplexDotIntegralFamily.value p () = simplexExpGenerator p.1 p.2 := by
  change 6*(∫ x in (0:ℝ)..1, simplexDotMiddleFamily.value p x) = _
  unfold simplexDotMiddleFamily
  simp_rw [ComplexIntegralFamily.variableIntervalIntegral_value]
  unfold simplexDotInnerFamily
  simp_rw [ComplexIntegralFamily.variableIntervalIntegral_value]
  unfold simplexExpGenerator complexSimplexExpectation complexSimplexDot
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  apply intervalIntegral.integral_congr
  intro y _
  apply intervalIntegral.integral_congr
  intro w _
  change Complex.exp (p.2*(p.1 0*(x:ℂ)+p.1 1*(y:ℂ)+p.1 2*(w:ℂ)+
    p.1 3*(1-(x:ℂ)-(y:ℂ)-(w:ℂ)))) = _
  push_cast
  congr 1

attribute [irreducible] simplexDotIntegralFamily

/-- The simplex generator is entire jointly in all four nodes and in z,
including every coincidence of nodes. -/
theorem simplexExpGenerator_contDiff_joint :
    ContDiff ℂ 1 (fun p : (Fin 4 → ℂ) × ℂ => simplexExpGenerator p.1 p.2) := by
  have h := (contDiff_const (c := (6:ℂ))).mul
    (simplexDotIntegralFamily.contDiff_value ())
  simpa only [simplexDotIntegralFamily_value] using h

attribute [local irreducible] simplexExpGenerator simplexTriangleExpIntegral expFirstSlope

theorem expNewtonMatrix_contDiff_joint (i j : Fin 4) :
    ContDiff ℂ 1 (fun p : (Fin 4 → ℂ) × (Fin 4 → ℂ) => expNewtonMatrix p.1 p.2 i j) := by
  fin_cases i
  all_goals simp only [expNewtonMatrix, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.reduceFinMk]
  · fun_prop
  · exact (by fun_prop : ContDiff ℂ 1
      (fun p : (Fin 4 → ℂ) × (Fin 4 → ℂ) => Complex.exp (p.2 j*p.1 0))).mul
      (expFirstSlope_contDiff_joint.comp (by fun_prop : ContDiff ℂ 1
        (fun p : (Fin 4 → ℂ) × (Fin 4 → ℂ) => (p.2 j,p.1 1-p.1 0))))
  · unfold expSecondNodeDifference
    exact (by fun_prop : ContDiff ℂ 1
      (fun p : (Fin 4 → ℂ) × (Fin 4 → ℂ) => (p.2 j)^2)).mul
      (simplexTriangleExpIntegral_contDiff_nodes.comp (by fun_prop : ContDiff ℂ 1
        (fun p : (Fin 4 → ℂ) × (Fin 4 → ℂ) => (p.1,p.2 j))))
  · unfold expThirdNodeDifference
    exact (by fun_prop : ContDiff ℂ 1
      (fun p : (Fin 4 → ℂ) × (Fin 4 → ℂ) => (p.2 j)^3/6)).mul
      (simplexExpGenerator_contDiff_joint.comp (by fun_prop : ContDiff ℂ 1
        (fun p : (Fin 4 → ℂ) × (Fin 4 → ℂ) => (p.1,p.2 j))))

attribute [local irreducible] expNewtonMatrix

/-- The regularized determinant has actual joint complex derivatives, even
where the unregularized Vandermonde denominator vanishes. -/
theorem exponentialAlternantRegularized_contDiff_joint :
    ContDiff ℂ 1 (fun p : (Fin 4 → ℂ) × (Fin 4 → ℂ) =>
      exponentialAlternantRegularized p.1 p.2) := by
  unfold exponentialAlternantRegularized
  apply (by fun_prop : ContDiff ℂ 1
    (fun p : (Fin 4 → ℂ) × (Fin 4 → ℂ) => Complex.exp (p.1 0+p.1 1))).mul
  simp_rw [Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact expNewtonMatrix_contDiff_joint (σ i) i

theorem exponentialAlternantRegularized_differentiable (q : Fin 4 → ℂ) :
    Differentiable ℂ (fun x => exponentialAlternantRegularized x q) :=
  (exponentialAlternantRegularized_contDiff_joint.comp
    (by fun_prop : ContDiff ℂ 1 (fun x : Fin 4 → ℂ => (x,q)))).differentiable
      (by norm_num)

/-- Distinct source shifts are dense; consequently their collision limits
determine the value of the continuous regularization uniquely. -/
theorem fourSourceShifts_injective_dense :
    Dense {x : Fin 4 → ℂ | Function.Injective x} := by
  classical
  let S (p : {p : Fin 4 × Fin 4 // p.1 ≠ p.2}) : Set (Fin 4 → ℂ) :=
    {x | x p.1.1 ≠ x p.1.2}
  have ho (p : {p : Fin 4 × Fin 4 // p.1 ≠ p.2}) : IsOpen (S p) := by
    exact isOpen_ne_fun (continuous_apply p.1.1) (continuous_apply p.1.2)
  have hd (p : {p : Fin 4 × Fin 4 // p.1 ≠ p.2}) : Dense (S p) := by
    let L : (Fin 4 → ℂ) →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj p.1.1 : (Fin 4 → ℂ) →L[ℂ] ℂ)-
        (ContinuousLinearMap.proj p.1.2 : (Fin 4 → ℂ) →L[ℂ] ℂ)
    have hs : Function.Surjective L := by
      intro z
      refine ⟨Function.update (fun _ : Fin 4 => (0:ℂ)) p.1.1 z, ?_⟩
      simp [L,p.2.symm]
    have h := (dense_compl_singleton (0:ℂ)).preimage (L.isOpenMap hs)
    have heq : L ⁻¹' ({0}ᶜ : Set ℂ) = {x | x p.1.1 ≠ x p.1.2} := by
      ext x
      simp [L, sub_ne_zero]
    rw [heq] at h
    exact h
  have h := dense_iInter_of_isOpen ho hd
  convert h using 1
  ext x
  simp only [mem_ofPred_eq, mem_iInter, S]
  constructor
  · intro hx p
    exact hx.ne p.2
  · intro hx i j hij
    by_contra hne
    exact hx ⟨(i,j),hne⟩ hij

/-- Exact continuation at the colliding U shifts, including z=0 and every
possible collision among the four polar nodes. -/
theorem exponentialAlternantRegularized_u_slice (q : Fin 4 → ℂ) (z : ℂ) :
    exponentialAlternantRegularized (![0,0,z,0]) q =
      fourVandermonde q/12*simplexExpGenerator q z := by
  let x₀ : Fin 4 → ℂ := ![0,0,z,0]
  have : NeBot (𝓝[{x : Fin 4 → ℂ | Function.Injective x}] x₀) :=
    mem_closure_iff_nhdsWithin_neBot.mp (fourSourceShifts_injective_dense x₀)
  have hc : Continuous (fun x : Fin 4 → ℂ => exponentialAlternantRegularized x q) :=
    exponentialAlternantRegularized_continuous_joint.comp
      (continuous_id.prodMk continuous_const)
  have ht := (hc.tendsto x₀).mono_left
    (nhdsWithin_le_nhds (s := {x : Fin 4 → ℂ | Function.Injective x}))
  have hr : Tendsto (fun x : Fin 4 → ℂ => exponentialAlternant x q)
      (𝓝[{x : Fin 4 → ℂ | Function.Injective x}] x₀)
      (𝓝 (exponentialAlternantRegularized x₀ q)) := by
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact exponentialAlternantRegularized_eq_raw x q hx
  exact tendsto_nhds_unique hr (exponentialAlternant_joint_shift_limit_unrestricted q z)

end
end Sechstmoment
