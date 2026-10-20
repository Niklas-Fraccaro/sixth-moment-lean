import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FunProp
import SixthMoment.Analysis.Simplex.Moments

namespace SixthMoment

open scoped BigOperators

theorem simplexExpectation_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ → ℝ) :
    simplexExpectation (fun x y z => c*f x y z) = c*simplexExpectation f := by
  simp only [simplexExpectation, intervalIntegral.integral_const_mul]
  ring

theorem simplexExpectation_finsetSum {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ → ℝ → ℝ)
    (hf : ∀ i, Continuous (fun p : ℝ × ℝ × ℝ => f i p.1 p.2.1 p.2.2)) :
    simplexExpectation (fun x y z => ∑ i, f i x y z) =
      ∑ i, simplexExpectation (f i) := by
  have hz (i : ι) (x y : ℝ) : Continuous (fun z : ℝ => f i x y z) :=
    (hf i).comp (show Continuous (fun z : ℝ => (x,y,z)) by fun_prop)
  have hzInt (i : ι) : Continuous (fun p : ℝ × ℝ =>
      ∫ z in (0 : ℝ)..1-p.1-p.2, f i p.1 p.2 z) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    · exact (hf i).comp
        (show Continuous (fun p : (ℝ × ℝ) × ℝ => (p.1.1,p.1.2,p.2)) by fun_prop)
    · fun_prop
  have hyInt (i : ι) (x : ℝ) : Continuous (fun y : ℝ =>
      ∫ z in (0 : ℝ)..1-x-y, f i x y z) := (hzInt i).comp
        (show Continuous (fun y : ℝ => (x,y)) by fun_prop)
  have hxInt (i : ι) : Continuous (fun x : ℝ =>
      ∫ y in (0 : ℝ)..1-x, ∫ z in (0 : ℝ)..1-x-y, f i x y z) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    · exact hzInt i
    · fun_prop
  have h₁ (x y : ℝ) : (∫ z in (0 : ℝ)..1-x-y, ∑ i, f i x y z) =
      ∑ i, ∫ z in (0 : ℝ)..1-x-y, f i x y z := by
    apply intervalIntegral.integral_finsetSum
    intro i _
    exact (hz i x y).intervalIntegrable 0 (1-x-y)
  have h₂ (x : ℝ) : (∫ y in (0 : ℝ)..1-x, ∑ i,
      ∫ z in (0 : ℝ)..1-x-y, f i x y z) =
      ∑ i, ∫ y in (0 : ℝ)..1-x, ∫ z in (0 : ℝ)..1-x-y, f i x y z := by
    apply intervalIntegral.integral_finsetSum
    intro i _
    exact (hyInt i x).intervalIntegrable 0 (1-x)
  unfold simplexExpectation
  simp_rw [h₁,h₂]
  rw [intervalIntegral.integral_finsetSum, Finset.mul_sum]
  intro i _
  exact (hxInt i).intervalIntegrable 0 1

end SixthMoment
