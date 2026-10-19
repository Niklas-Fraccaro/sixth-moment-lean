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
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
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
import Sechstmoment.Zeta.AFE.Four.GammaRemainder
import Std

/-! Working central-remainder estimates. These statements concern the
actual Gamma quotient; no V-error or moment estimate is assumed. -/

namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section

/-- On any positive central line at most one unit from the origin, the
actual Gaussian difference has degree 49 and the shifted power scale. -/
theorem bblrCentralWeightDifference_vertical_norm_le {t A x c R : ℝ}
    (hA : 0 ≤ A) (ht : 8*(A+1) ≤ t) (hx : 0 < x)
    (hc : 0 < c) (hc1 : c ≤ 1) (hR : 0 ≤ R)
    (hcentral : 192*((1+R)+(1+R)^2) < t)
    (hphase : (4+8*A)*(1+R) ≤ t)
    (T : ℝ) (σ α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ A)
    (v : ℝ) (hv : |v| ≤ R) :
    ‖bblrCentralWeightDifference (polarPoleKiller T σ) t α x ((c:ℂ)+(v:ℂ)*I)‖ ≤
      (polarGaussianConstant T σ c*(t/2)^(2*c)*Real.pi^(-2*c)*x^(-c)*
        ((2884+8*A)/t))*(1+|v|)^49*Real.exp (-v^2) := by
  have htpos : 0 < t := by linarith
  let z : ℂ := (c:ℂ)+(v:ℂ)*I
  have hzn : ‖z‖ ≤ c+|v| := by
    exact (norm_add_le _ _).trans_eq (by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one,
        abs_of_pos hc])
  have hnR : ‖z‖ ≤ 1+R := by linarith
  have hsq : ‖z‖^2 ≤ (1+R)^2 := by nlinarith [norm_nonneg z]
  have hz : 192*(‖z‖+‖z‖^2) < t := by linarith
  have hp : (4+8*A)*‖z‖ ≤ t := by nlinarith
  have hb := bblrCentralWeightDifference_norm_le hA ht hx (polarPoleKiller T σ) α hα z hz hp
  have hzre : z.re = c := by simp [z]
  rw [hzre] at hb
  have hg := polarPoleKiller_vertical_norm_le T σ c v
  have hCG := polarGaussianConstant_nonneg T σ c
  have hp49 : (1+|v|)^49 = (1+|v|)^48*(1+|v|) := by
    rw [show (49:ℕ)=48+1 by norm_num,pow_add,pow_one]
  have herr : 1440*(1+‖z‖)+4+8*A ≤ (2884+8*A)*(1+|v|) := by
    nlinarith [abs_nonneg v]
  calc
    _ ≤ (polarGaussianConstant T σ c*(1+|v|)^48*Real.exp (-v^2))*
        (t/2)^(2*c)*Real.pi^(-2*c)*x^(-c)*
        (((2884+8*A)*(1+|v|))/t) := by
      apply hb.trans
      gcongr
    _ = _ := by rw [hp49]; ring

def bblrCentralGaussianDifferenceCore (T : ℝ) (σ α : MomentShifts)
    (t x c R : ℝ) : ℂ :=
  (1/(2*Real.pi) : ℂ)*∫ v in Icc (-R) R,
    bblrCentralWeightDifference (polarPoleKiller T σ) t α x ((c:ℂ)+(v:ℂ)*I)

/-- A genuinely integrated central estimate on the shifted positive line.
All integrability is derived from the actual Gamma holomorphy and Gaussian.
Identifying this core with the original line still requires the contour move
and quantitative shifted tails. -/
theorem bblrCentralGaussianDifferenceCore_norm_le {t x c R : ℝ}
    (ht : 10 ≤ t) (hx : 0 < x) (hc : 0 < c) (hc1 : c ≤ 1) (hR : 0 ≤ R)
    (hcentral : 192*((1+R)+(1+R)^2) < t) (hphase : 6*(1+R) ≤ t)
    (T : ℝ) (σ α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    ‖bblrCentralGaussianDifferenceCore T σ α t x c R‖ ≤
      (2886/(2*Real.pi))*polarGaussianConstant T σ c*(t/2)^(2*c)*
        Real.pi^(-2*c)*x^(-c)*gaussianTailConstant 49/t := by
  have htpos : 0 < t := by linarith
  let f : ℝ → ℂ := fun v =>
    bblrCentralWeightDifference (polarPoleKiller T σ) t α x ((c:ℂ)+(v:ℂ)*I)
  have hfc : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro v
    have hd := bblrCentralWeightDifference_differentiableOn_rightHalfPlane htpos hx
      (polarPoleKiller T σ) (polarPoleKiller_differentiable T σ) α hα
    have hz : ((c:ℂ)+(v:ℂ)*I) ∈ {z : ℂ | 0<z.re} := by simpa using hc
    have hdAt := hd.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
    have hl : ContinuousAt (fun u : ℝ => (c:ℂ)+(u:ℂ)*I) v := by fun_prop
    exact hdAt.continuousAt.comp (f := fun u : ℝ => (c:ℂ)+(u:ℂ)*I) hl
  have hfi : IntegrableOn f (Icc (-R) R) := hfc.continuousOn.integrableOn_Icc
  let B : ℝ := polarGaussianConstant T σ c*(t/2)^(2*c)*Real.pi^(-2*c)*x^(-c)*(2886/t)
  have hCG := polarGaussianConstant_nonneg T σ c
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let g : ℝ → ℝ := fun v => B*((1+|v|)^49*Real.exp (-(1/2)*v^2))
  have hgi : Integrable g := (gaussian_polynomial_half_integrable 49).const_mul B
  have hpoint : ∀ v ∈ Icc (-R) R, ‖f v‖ ≤ g v := by
    intro v hv
    have hav : |v| ≤ R := abs_le.mpr hv
    have hb := bblrCentralWeightDifference_vertical_norm_le (by norm_num : (0:ℝ)≤1/4)
      (by norm_num at ht ⊢; exact ht) hx hc hc1 hR hcentral
      (by norm_num; exact hphase) T σ α hα v hav
    rw [show (2884+8*(1/4:ℝ))=2886 by norm_num] at hb
    change ‖f v‖ ≤ B*(1+|v|)^49*Real.exp (-v^2) at hb
    refine hb.trans ?_
    dsimp [g]
    have he : Real.exp (-v^2) ≤ Real.exp (-(1/2)*v^2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg v]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left he (mul_nonneg hB (by positivity : 0 ≤ (1+|v|)^49))
  have hi : ‖∫ v in Icc (-R) R, f v‖ ≤ B*gaussianTailConstant 49 := by
    calc
      _ ≤ ∫ v in Icc (-R) R, ‖f v‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ v in Icc (-R) R, g v :=
        setIntegral_mono_on hfi.norm hgi.integrableOn measurableSet_Icc hpoint
      _ ≤ ∫ v : ℝ, g v := setIntegral_le_integral hgi
        (Eventually.of_forall (fun v => by dsimp [g]; positivity))
      _ = _ := by rw [integral_const_mul]; rfl
  unfold bblrCentralGaussianDifferenceCore
  rw [norm_mul]
  have hconstant : ‖(1/(2*Real.pi) : ℂ)‖ = 1/(2*Real.pi) := by
    simp [Complex.norm_real,abs_of_pos Real.pi_pos]
  rw [hconstant]
  calc
    _ ≤ (1/(2*Real.pi))*(B*gaussianTailConstant 49) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by dsimp [B]; ring

end
end Sechstmoment.Source
