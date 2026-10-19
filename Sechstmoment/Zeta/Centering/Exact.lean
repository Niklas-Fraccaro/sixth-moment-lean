import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Sechstmoment.Zeta.Chi.Basic
import Sechstmoment.Zeta.Generators
import Std

/-!
# Exact shifted functional equation before asymptotic centering

`centeringFactor` is the literal ratio in (1.4), built from the actual
archimedean Gamma factors. The functional equation below is exact on the
critical strip and on every fixed shift disk once its radius is smaller than
`log T / 2`. No Stirling estimate or moment estimate is assumed or asserted.
-/

namespace Sechstmoment
open Complex Filter Set
open scoped Topology

noncomputable section

/-- The shifted complex argument used by the two normalized generators. -/
def centeringShift (T t : ℝ) (z : ℂ) : ℂ :=
  criticalLinePoint t + z / (Real.log T : ℂ)

/-- The exact factor `exp z · χ(s+z/log T)/χ(s)` in §1.1. -/
def centeringFactor (T t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp z * zetaChi (centeringShift T t z) / criticalChi t

/-- The error to be estimated uniformly by Stirling; it is an actual function,
not an asymptotic hypothesis. -/
def centeringError (T t : ℝ) (z : ℂ) : ℂ := centeringFactor T t z - 1

/-- The exact generator identity preceding equation (1.4). -/
theorem centering_generator_functional_equation (T t : ℝ) (z : ℂ)
    (hlo : 0 < (centeringShift T t z).re)
    (hhi : (centeringShift T t z).re < 1) :
    (criticalChi t)⁻¹ * zetaCPlus T t z =
      centeringFactor T t z * zetaCMinus T t (-z) := by
  have hfe := riemannZeta_strip_functional_equation hlo hhi
  have hs : 1-(criticalLinePoint t + z/(Real.log T : ℂ)) =
      1-criticalLinePoint t + (-z)/(Real.log T : ℂ) := by ring
  have he : Complex.exp z * Complex.exp ((-z)/2) = Complex.exp (z/2) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  simp only [zetaCPlus, zetaCMinus, shiftedZetaGenerator, centeringFactor,
    centeringShift] at hfe ⊢
  rw [hfe, hs]
  rw [← he]
  ring

@[simp] theorem centeringFactor_zero (T t : ℝ) : centeringFactor T t 0 = 1 := by
  simp [centeringFactor, centeringShift, criticalChi_ne_zero t]

@[simp] theorem centeringError_zero (T t : ℝ) : centeringError T t 0 = 0 := by
  simp [centeringError]

/-- Every bounded shift remains in the critical strip once `log T` dominates
its radius. This domain control does not depend on the height `t`. -/
theorem centeringShift_mem_strip {T : ℝ} (hT : 0 < Real.log T) (t : ℝ)
    (z : ℂ) (hz : 2*‖z‖ < Real.log T) :
    0 < (centeringShift T t z).re ∧ (centeringShift T t z).re < 1 := by
  have hzr := Complex.abs_re_le_norm z
  have hzl : -‖z‖ ≤ z.re := (abs_le.mp hzr).1
  have hzu : z.re ≤ ‖z‖ := (abs_le.mp hzr).2
  have hl : -(Real.log T)/2 < z.re := by linarith
  have hu : z.re < (Real.log T)/2 := by linarith
  have hl' : -(1/2 : ℝ) < z.re/Real.log T :=
    (lt_div_iff₀ hT).mpr (by linarith)
  have hu' : z.re/Real.log T < (1/2 : ℝ) :=
    (div_lt_iff₀ hT).mpr (by linarith)
  simp only [centeringShift, add_re, criticalLinePoint_re, div_ofReal_re]
  constructor <;> linarith

theorem centering_generator_functional_equation_on_disk {T : ℝ}
    (hT : 0 < Real.log T) (t : ℝ) {R : ℝ} (hR : 2*R < Real.log T)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    (criticalChi t)⁻¹ * zetaCPlus T t z =
      centeringFactor T t z * zetaCMinus T t (-z) := by
  have hs := centeringShift_mem_strip hT t z (by linarith)
  exact centering_generator_functional_equation T t z hs.1 hs.2

theorem centeringFactor_analyticAt {T t : ℝ} {z : ℂ}
    (hz : 0 < (centeringShift T t z).re ∧ (centeringShift T t z).re < 1) :
    AnalyticAt ℂ (centeringFactor T t) z := by
  have hs := zetaChi_analyticOnNhd_strip (centeringShift T t z) hz
  have ha : AnalyticAt ℂ (centeringShift T t) z := by
    unfold centeringShift
    fun_prop
  exact ((analyticAt_cexp.mul (hs.comp (f := centeringShift T t) ha)).div_const :
    AnalyticAt ℂ (centeringFactor T t) z)

theorem centeringError_analyticAt {T t : ℝ} {z : ℂ}
    (hz : 0 < (centeringShift T t z).re ∧ (centeringShift T t z).re < 1) :
    AnalyticAt ℂ (centeringError T t) z :=
  (centeringFactor_analyticAt hz).sub analyticAt_const

/-- Every fixed closed shift disk is a genuine holomorphy domain once the
logarithm dominates twice the radius. -/
theorem centeringFactor_analyticOnNhd_disk {T : ℝ} (hT : 0 < Real.log T)
    (t R : ℝ) (hR : 2*R < Real.log T) :
    AnalyticOnNhd ℂ (centeringFactor T t) (Metric.closedBall 0 R) := by
  intro z hz
  exact centeringFactor_analyticAt (centeringShift_mem_strip hT t z (by
    have hnorm : ‖z‖ ≤ R := by simpa using hz
    linarith))

theorem centeringError_analyticOnNhd_disk {T : ℝ} (hT : 0 < Real.log T)
    (t R : ℝ) (hR : 2*R < Real.log T) :
    AnalyticOnNhd ℂ (centeringError T t) (Metric.closedBall 0 R) :=
  (centeringFactor_analyticOnNhd_disk hT t R hR).sub analyticOnNhd_const

private theorem zetaCMinus_neg_analyticAt_zero (T t : ℝ) :
    AnalyticAt ℂ (fun z => zetaCMinus T t (-z)) 0 := by
  have hs : 1-criticalLinePoint t ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [sub_re, one_re, criticalLinePoint_re] at hr
    norm_num at hr
  have hz := analyticOn_riemannZeta (1-criticalLinePoint t) (by simpa using hs)
  have hz' : AnalyticAt ℂ riemannZeta
      (1-criticalLinePoint t + -(0 : ℂ)/(Real.log T : ℂ)) := by simpa using hz
  have ha : AnalyticAt ℂ (fun z : ℂ =>
      1-criticalLinePoint t + -z/(Real.log T : ℂ)) 0 := by fun_prop
  have he : AnalyticAt ℂ (fun z : ℂ => Complex.exp (-z/2)) 0 := by fun_prop
  exact he.mul (hz'.comp (f := fun z : ℂ => 1-criticalLinePoint t + -z/(Real.log T : ℂ)) ha)

private theorem centering_generator_eventually (T t : ℝ) :
    (fun z => (criticalChi t)⁻¹ * zetaCPlus T t z) =ᶠ[𝓝 0]
      (fun z => centeringFactor T t z * zetaCMinus T t (-z)) := by
  have hc : Continuous (fun z : ℂ => (centeringShift T t z).re) := by
    unfold centeringShift
    fun_prop
  have ho : IsOpen {z : ℂ | 0 < (centeringShift T t z).re ∧
      (centeringShift T t z).re < 1} :=
    (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
  have hzero : (0 : ℂ) ∈ {z : ℂ | 0 < (centeringShift T t z).re ∧
      (centeringShift T t z).re < 1} := by
    norm_num [centeringShift]
  filter_upwards [ho.mem_nhds hzero] with z hz
  exact centering_generator_functional_equation T t z hz.1 hz.2

/-- Exact all-order Leibniz formula. The phase-factor derivatives remain
visible, so this does not make the false exact parity assertion (1.5). -/
theorem centering_generator_derivatives (T t : ℝ) (m : ℕ) :
    (criticalChi t)⁻¹ * iteratedDeriv m (zetaCPlus T t) 0 =
      ∑ j ∈ Finset.range (m+1), (m.choose j : ℂ) *
        iteratedDeriv j (centeringFactor T t) 0 *
        (-1 : ℂ)^(m-j) * iteratedDeriv (m-j) (zetaCMinus T t) 0 := by
  have hf : ContDiffAt ℂ m (centeringFactor T t) 0 :=
    (centeringFactor_analyticAt (by norm_num [centeringShift])).contDiffAt
  have hg : ContDiffAt ℂ m (fun z => zetaCMinus T t (-z)) 0 :=
    (zetaCMinus_neg_analyticAt_zero T t).contDiffAt
  rw [← iteratedDeriv_const_mul_field]
  rw [(centering_generator_eventually T t).iteratedDeriv_eq m,
    iteratedDeriv_fun_mul hf hg]
  simp only [iteratedDeriv_comp_neg, neg_zero, smul_eq_mul, mul_assoc]

/-- The actual generator discrepancy is exactly the actual scalar error
multiplied by the reflected negative generator. -/
theorem centering_generator_error (T t : ℝ) (z : ℂ)
    (hz : 0 < (centeringShift T t z).re ∧ (centeringShift T t z).re < 1) :
    (criticalChi t)⁻¹*zetaCPlus T t z - zetaCMinus T t (-z) =
      centeringError T t z * zetaCMinus T t (-z) := by
  rw [centering_generator_functional_equation T t z hz.1 hz.2]
  unfold centeringError
  ring

/-- The normalized factor with the actual critical-line Gamma ratios exposed. -/
theorem centeringFactor_gamma_ratios (T t : ℝ) (z : ℂ) :
    centeringFactor T t z = Complex.exp z *
      (Real.pi : ℂ)^(z/(Real.log T : ℂ)) *
      (Gamma ((1-criticalLinePoint t-z/(Real.log T : ℂ))/2)/
        Gamma ((1-criticalLinePoint t)/2)) *
      (Gamma (criticalLinePoint t/2)/
        Gamma ((criticalLinePoint t+z/(Real.log T : ℂ))/2)) := by
  unfold centeringFactor centeringShift
  rw [← zetaChi_criticalLinePoint t, mul_div_assoc, zetaChi_shift_ratio]
  ring

/-- Fixed shift disks eventually satisfy all of the exact domain and
holomorphy statements above; no restriction on the height is needed. -/
theorem eventually_centering_disk (R : ℝ) :
    ∀ᶠ T : ℝ in atTop, 0 < Real.log T ∧ 2*R < Real.log T := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_gt_atTop (max 0 (2*R)))]
    with T hT
  exact ⟨lt_of_le_of_lt (le_max_left _ _) hT, lt_of_le_of_lt (le_max_right _ _) hT⟩

end
end Sechstmoment
