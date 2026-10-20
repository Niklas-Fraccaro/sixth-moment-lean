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
import Std


namespace Sechstmoment
open Complex Real Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem positive_cpow_contDiffAt (s : ℂ) {x : ℝ} (hx : 0<x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℝ => (y:ℂ)^s) x := by
  have hl : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℝ => (Real.log y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_log.mpr hx.ne')
  have hm : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℝ => (Real.log y : ℂ)*s) x :=
    hl.mul contDiffAt_const
  have hexp : ContDiff ℝ (⊤ : ℕ∞) Complex.exp := Complex.contDiff_exp
  have he := hexp.contDiffAt.comp x hm
  apply he.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hy)),
    ← Complex.ofReal_log (le_of_lt hy)]
  rfl

theorem positive_cpow_hasDerivAt (s : ℂ) {x : ℝ} (hx : 0<x) :
    HasDerivAt (fun y : ℝ => (y:ℂ)^s) (s*(x:ℂ)^(s-1)) x := by
  exact (Complex.hasStrictDerivAt_cpow_const (by simpa using hx)).hasDerivAt.comp_ofReal

def mellinFallingCoefficient (j : ℕ) (s : ℂ) : ℂ :=
  ∏ i∈Finset.range j, (s-(i:ℂ))

theorem mellinFallingCoefficient_succ (j : ℕ) (s : ℂ) :
    mellinFallingCoefficient (j+1) s=mellinFallingCoefficient j s*(s-(j:ℂ)) := by
  exact Finset.prod_range_succ _ j

theorem positive_cpow_iteratedDeriv (j : ℕ) (s : ℂ) {x : ℝ} (hx : 0<x) :
    iteratedDeriv j (fun y : ℝ => (y:ℂ)^s) x=
      mellinFallingCoefficient j s*(x:ℂ)^(s-(j:ℂ)) := by
  induction j generalizing x with
  | zero => simp [mellinFallingCoefficient]
  | succ j ih =>
    have he : iteratedDeriv j (fun y : ℝ => (y:ℂ)^s) =ᶠ[𝓝 x]
        fun y : ℝ => mellinFallingCoefficient j s*(y:ℂ)^(s-(j:ℂ)) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact ih hy
    rw [iteratedDeriv_succ,he.deriv_eq,
      ((positive_cpow_hasDerivAt (s-(j:ℂ)) hx).const_mul (mellinFallingCoefficient j s)).deriv,
      mellinFallingCoefficient_succ]
    push_cast
    have h : s-(j:ℂ)-1=s-((j:ℂ)+1) := by ring
    rw [h]
    ring

theorem mellinFallingCoefficient_norm_le (j : ℕ) (s : ℂ) :
    ‖mellinFallingCoefficient j s‖≤((j:ℝ)+1)^j*(1+‖s‖)^j := by
  have hp (i : ℕ) (hi : i∈Finset.range j) :
      ‖s-(i:ℂ)‖≤((j:ℝ)+1)*(1+‖s‖) := by
    have hij : (i:ℝ)≤j := by exact_mod_cast (Finset.mem_range.mp hi).le
    have hn := norm_sub_le s (i:ℂ)
    simp only [Complex.norm_natCast] at hn
    nlinarith [norm_nonneg s, (Nat.cast_nonneg j : (0:ℝ)≤j)]
  unfold mellinFallingCoefficient
  rw [norm_prod]
  calc
    _ ≤ ∏ _i∈Finset.range j, ((j:ℝ)+1)*(1+‖s‖) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hp
    _ = _ := by simp [mul_pow]

end
end Sechstmoment
