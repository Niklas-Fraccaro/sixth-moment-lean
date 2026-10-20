import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Rat.Cast.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Compact
import Sechstmoment.Analysis.Gaussian.Tails
import Sechstmoment.Numerator.Polar.GaussianControl
import Sechstmoment.Zeta.Gamma.QuotientTail
import Std


namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section

theorem bblrVerticalIntegrand_gaussian_majorant :
    ∃ D : ℝ, 0 < D ∧ ∀ T : ℝ, ∀ σ α : MomentShifts, (∀ j, ‖α j‖ ≤ 1/4) →
      ∀ t x v : ℝ, 0 ≤ t → 0 < x →
      ‖bblrVerticalIntegrand (polarPoleKiller T σ) α x t v‖ ≤
        (D*polarGaussianConstant T σ 1*(2+t)^8/x)*
          (1+|v|)^56*Real.exp (-v^2) := by
  obtain ⟨C,hC,hΓ⟩ := bblrGammaQuotient_polynomial_line_bound
  refine ⟨C*Real.pi^(-2 : ℝ), by positivity, ?_⟩
  intro T σ α hα t x v ht hx
  have hCG := polarGaussianConstant_nonneg T σ 1
  have hz : 1 ≤ ‖(1 : ℂ)+(v : ℂ)*I‖ := by
    simpa using Complex.abs_re_le_norm ((1 : ℂ)+(v : ℂ)*I)
  have hg : ‖polarPoleKiller T σ (1+(v : ℂ)*I)/(1+(v : ℂ)*I)‖ ≤
      polarGaussianConstant T σ 1*(1+|v|)^48*Real.exp (-v^2) := by
    rw [norm_div]
    apply (div_le_self (norm_nonneg _) hz).trans
    exact polarPoleKiller_vertical_norm_le T σ 1 v
  have hπ : ‖(Real.pi : ℂ)^(-2*(1+(v : ℂ)*I))‖ = Real.pi^(-2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    simp
  have hxp : ‖(x : ℂ)^(-(1+(v : ℂ)*I))‖ = 1/x := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp [Real.rpow_neg_one]
  have hp : (2+t+|v|)^8 ≤ (2+t)^8*(1+|v|)^8 := by
    rw [← mul_pow]
    gcongr
    nlinarith [abs_nonneg v]
  unfold bblrVerticalIntegrand
  dsimp only
  rw [norm_mul, norm_mul, norm_mul, hπ, hxp]
  calc
    _ ≤ (polarGaussianConstant T σ 1*(1+|v|)^48*Real.exp (-v^2))*
        (C*((2+t)^8*(1+|v|)^8))*Real.pi^(-2 : ℝ)*(1/x) := by
      gcongr
      exact (hΓ t v ht α hα).trans (mul_le_mul_of_nonneg_left hp hC.le)
    _ = _ := by rw [show (1+|v|)^56 = (1+|v|)^48*(1+|v|)^8 by rw [← pow_add]]; ring

def bblrGaussianVTail (T : ℝ) (σ α : MomentShifts) (x t R : ℝ) : ℂ :=
  (1/(2*Real.pi) : ℂ)*
    ∫ v in {v : ℝ | R < |v|}, bblrVerticalIntegrand (polarPoleKiller T σ) α x t v

theorem bblrGaussianVTail_norm_le :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ T : ℝ, ∀ σ α : MomentShifts, (∀ j, ‖α j‖ ≤ 1/4) →
      ∀ t x R : ℝ, 0 ≤ t → 0 < x → 0 ≤ R →
      ‖bblrGaussianVTail T σ α x t R‖ ≤
        D*polarGaussianConstant T σ 1*(2+t)^8/x*Real.exp (-(1/2)*R^2) := by
  obtain ⟨C,hC,hbound⟩ := bblrVerticalIntegrand_gaussian_majorant
  have hJ := gaussianTailConstant_nonneg 56
  refine ⟨C*gaussianTailConstant 56/(2*Real.pi), by positivity, ?_⟩
  intro T σ α hα t x R ht hx hR
  have hαre : ∀ j, -1/2 < (α j).re := by
    intro j
    have h := (abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))).1
    linarith
  have hfi := bblrVerticalIntegrand_integrable (polarPoleKiller T σ)
    (polarPoleKiller_differentiable T σ).continuous
    (polarPoleKiller_vertical_integrable T σ 1).norm α x t hx hαre
  have hCG := polarGaussianConstant_nonneg T σ 1
  have htail := gaussian_integral_tail_norm_le
    (bblrVerticalIntegrand (polarPoleKiller T σ) α x t) hfi 56
    (by positivity : 0 ≤ C*polarGaussianConstant T σ 1*(2+t)^8/x) hR
    (fun v => hbound T σ α hα t x v ht hx)
  unfold bblrGaussianVTail
  rw [norm_mul]
  have hc : ‖(1/(2*Real.pi) : ℂ)‖ = 1/(2*Real.pi) := by
    simp [Complex.norm_real, abs_of_pos Real.pi_pos]
  rw [hc]
  calc
    _ ≤ (1/(2*Real.pi))*(C*polarGaussianConstant T σ 1*(2+t)^8/x*
        gaussianTailConstant 56*Real.exp (-(1/2)*R^2)) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = _ := by ring

end
end Sechstmoment.Source
