import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Cast.Order
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Instances.EReal.Lemmas
import Sechstmoment.Analysis.Complex.PositivePowers
import Sechstmoment.Arithmetic.QuadraticDivisor.ComplexWeights
import Sechstmoment.Numerator.U.Reconstruction.RectangularSmoothAFE
import Std

/-! Genuine smooth complex Mellin weights for the four positive AFE variables.
All derivative orders have proved polynomial frequency bounds. The coupled
time/gap weight and the structural quadratic-source hypotheses are separate. -/

namespace Sechstmoment
open Complex Real Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

def rectangularMellinBlockWeight (s : ℂ) (x : ℝ) : ℂ :=
  (rectangularSmoothBlockWeight x : ℂ)*(x:ℂ)^s

theorem rectangularMellinBlockWeight_complexWeight (s : ℂ) :
    RectangularComplexWeight (rectangularMellinBlockWeight s) := by
  constructor
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : 0<x
    · exact (Complex.ofRealCLM.contDiff.comp rectangularSmoothBlockWeight_contDiff).contDiffAt.mul
        (positive_cpow_contDiffAt s hx)
    · have he : rectangularMellinBlockWeight s =ᶠ[𝓝 x] fun _ => (0:ℂ) := by
        filter_upwards [Iio_mem_nhds (by linarith : x<1)] with y hy
        simp [rectangularMellinBlockWeight,rectangularSmoothBlockWeight_zero_le hy.le]
      exact contDiffAt_const.congr_of_eventuallyEq he
  · apply closure_minimal
    · intro x hx
      have h : rectangularSmoothBlockWeight x≠0 := by
        intro hz
        exact hx (by simp [rectangularMellinBlockWeight,hz])
      exact rectangularSmoothBlockWeight_tsupport (subset_tsupport _ h)
    · exact isClosed_Icc

theorem rectangularMellinBlockWeight_iteratedDeriv_tsupport (s : ℂ) (j : ℕ) :
    tsupport (iteratedDeriv j (rectangularMellinBlockWeight s))⊆Icc 1 2 := by
  induction j with
  | zero => simpa using (rectangularMellinBlockWeight_complexWeight s).2
  | succ j ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

private theorem block_ofReal_iteratedDeriv (j : ℕ) (x : ℝ) :
    iteratedDeriv j (Complex.ofRealCLM ∘ rectangularSmoothBlockWeight) x=
      ((iteratedDeriv j rectangularSmoothBlockWeight x : ℝ) : ℂ) := by
  rw [iteratedDeriv_eq_iteratedFDeriv,
    Complex.ofRealCLM.iteratedFDeriv_comp_left rectangularSmoothBlockWeight_contDiff.contDiffAt (by simp)]
  rfl

theorem rectangularMellinBlockWeight_derivative_pos (s : ℂ) (j : ℕ) {x : ℝ} (hx : 0<x) :
    iteratedDeriv j (rectangularMellinBlockWeight s) x=
      ∑ i∈Finset.range (j+1), (j.choose i : ℂ)*
        ((iteratedDeriv i rectangularSmoothBlockWeight x : ℝ) : ℂ)*
        (mellinFallingCoefficient (j-i) s*(x:ℂ)^(s-((j-i:ℕ):ℂ))) := by
  change iteratedDeriv j (fun y : ℝ => (rectangularSmoothBlockWeight y : ℂ)*(y:ℂ)^s) x=_
  have hm := iteratedDeriv_fun_mul (n := j)
    ((Complex.ofRealCLM.contDiff.comp rectangularSmoothBlockWeight_contDiff).contDiffAt.of_le (by simp))
    ((positive_cpow_contDiffAt s hx).of_le (by simp))
  simpa only [block_ofReal_iteratedDeriv,
    positive_cpow_iteratedDeriv _ s hx, Function.comp_apply, ofRealCLM_apply] using hm

theorem rectangularMellinBlockWeight_polynomial_derivative_bounds :
    ∃ B : ℕ → ℝ, (∀ j, 0≤B j) ∧ ∀ j (s : ℂ), s.re≤0 → ∀ x : ℝ,
      ‖iteratedDeriv j (rectangularMellinBlockWeight s) x‖≤B j*(1+‖s‖)^j := by
  obtain ⟨C,hC,hb⟩ := rectangularSmoothBlockWeight_derivative_bounds
  let B : ℕ → ℝ := fun j => ∑ i∈Finset.range (j+1),
    (j.choose i : ℝ)*C i*((j-i:ℕ)+1 : ℝ)^(j-i)
  have hB (j : ℕ) : 0≤B j := by
    dsimp [B]
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC i)) (by positivity)
  refine ⟨B,hB,?_⟩
  intro j s hs x
  by_cases hx : x∈Icc (1:ℝ) 2
  · have hxpos : 0<x := zero_lt_one.trans_le hx.1
    have hpow (n : ℕ) : ‖(x:ℂ)^(s-(n:ℂ))‖≤1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
      have hsn : (s-(n:ℂ)).re≤0 := by
        simp only [sub_re,natCast_re]
        linarith [(Nat.cast_nonneg n : (0:ℝ)≤n)]
      calc
        _ ≤ x^(0:ℝ) := Real.rpow_le_rpow_of_exponent_le hx.1 hsn
        _ = _ := Real.rpow_zero x
    have hp (i : ℕ) (_hi : i∈Finset.range (j+1)) :
        ‖(j.choose i : ℂ)*((iteratedDeriv i rectangularSmoothBlockWeight x : ℝ) : ℂ)*
          (mellinFallingCoefficient (j-i) s*(x:ℂ)^(s-((j-i:ℕ):ℂ)))‖≤
        ((j.choose i : ℝ)*C i*((j-i:ℕ)+1 : ℝ)^(j-i))*(1+‖s‖)^j := by
      rw [norm_mul,norm_mul,norm_mul,Complex.norm_natCast,Complex.norm_real]
      calc
        _ ≤ ((j.choose i : ℝ)*C i)*
            ((((j-i:ℕ):ℝ)+1)^(j-i)*(1+‖s‖)^(j-i)*1) := by
          gcongr
          · exact mul_nonneg (Nat.cast_nonneg _) (hC i)
          · exact hb i x
          · exact mellinFallingCoefficient_norm_le (j-i) s
          · exact hpow (j-i)
        _ ≤ ((j.choose i : ℝ)*C i)*
            ((((j-i:ℕ):ℝ)+1)^(j-i)*(1+‖s‖)^j*1) := by
          simp only [mul_one]
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg _) (hC i))
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_right₀ (by linarith [norm_nonneg s]) (Nat.sub_le j i)
        _ = _ := by ring
    rw [rectangularMellinBlockWeight_derivative_pos s j hxpos]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum hp).trans_eq (by
      rw [← Finset.sum_mul]))
  · have hz : iteratedDeriv j (rectangularMellinBlockWeight s) x=0 := by
      by_contra h
      exact hx (rectangularMellinBlockWeight_iteratedDeriv_tsupport s j (subset_tsupport _ h))
    rw [hz,norm_zero]
    exact mul_nonneg (hB j) (pow_nonneg (by linarith [norm_nonneg s]) j)

end
end Sechstmoment
