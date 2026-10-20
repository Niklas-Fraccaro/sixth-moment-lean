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
import SixthMoment.Zeta.AFE.Four.GammaHolomorphy
import Std


namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section

def bblrCentralGammaPuncturedError (t : ℝ) (α : MomentShifts) (z : ℂ) : ℂ :=
  (bblrGammaQuotient t α z/(t/2 : ℂ)^(2*z)-1)/z

theorem bblrCentralGammaPuncturedError_norm_le {t A : ℝ} (hA : 0 ≤ A)
    (ht : 8*(A+1) ≤ t) (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ A)
    (z : ℂ) (hz : 192*(‖z‖+‖z‖^2) < t) (hphase : (4+8*A)*‖z‖ ≤ t) :
    ‖bblrCentralGammaPuncturedError t α z‖ ≤ (1440*(1+‖z‖)+4+8*A)/t := by
  have htpos : 0 < t := by linarith
  by_cases hz0 : z = 0
  · simp only [bblrCentralGammaPuncturedError,hz0,div_zero,norm_zero]
    positivity
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hb := bblrGammaQuotient_normalized_error_le hA ht α hα z hz hphase
    unfold bblrCentralGammaPuncturedError
    rw [norm_div]
    calc
      _ ≤ ((1440*(‖z‖+‖z‖^2)+(4+8*A)*‖z‖)/t)/‖z‖ :=
        div_le_div_of_nonneg_right hb hn.le
      _ = _ := by field_simp; ring

def bblrCentralWeightDifference (G : ℂ → ℂ) (t : ℝ) (α : MomentShifts)
    (x : ℝ) (z : ℂ) : ℂ :=
  G z/z*(bblrGammaQuotient t α z-(t/2 : ℂ)^(2*z))*
    (Real.pi : ℂ)^(-2*z)*(x : ℂ)^(-z)

theorem bblrCentralWeightDifference_differentiableOn_rightHalfPlane {t x : ℝ}
    (ht : 0 < t) (hx : 0 < x) (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    DifferentiableOn ℂ (bblrCentralWeightDifference G t α x) {z : ℂ | 0<z.re} := by
  have hbase : (t/2 : ℂ) ≠ 0 :=
    div_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne') (by norm_num)
  have hP : DifferentiableOn ℂ (fun z : ℂ => (t/2 : ℂ)^(2*z)) {z : ℂ | 0<z.re} :=
    (differentiableOn_id.const_mul (2:ℂ)).const_cpow (.inl hbase)
  have hF := bblrCentralNormalizedGamma_differentiableOn_rightHalfPlane ht α hα
  have hQ : DifferentiableOn ℂ (bblrGammaQuotient t α) {z : ℂ | 0<z.re} := by
    convert hF.mul hP using 1
    ext z
    unfold bblrCentralNormalizedGamma
    have hp : (t/2 : ℂ)^(2*z) ≠ 0 := by simp [hbase]
    exact (div_mul_cancel₀ _ hp).symm
  have hπ : DifferentiableOn ℂ (fun z : ℂ => (Real.pi:ℂ)^(-2*z)) {z : ℂ | 0<z.re} :=
    (differentiableOn_id.const_mul (-2:ℂ)).const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hxp : DifferentiableOn ℂ (fun z : ℂ => (x:ℂ)^(-z)) {z : ℂ | 0<z.re} :=
    differentiableOn_id.neg.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have hz0 : ∀ z ∈ {z : ℂ | 0<z.re}, z ≠ 0 := by
    intro z hz he
    simp [he] at hz
  exact (((hG.differentiableOn.div differentiableOn_id hz0).mul (hQ.sub hP)).mul hπ).mul hxp

theorem bblrCentralWeightDifference_norm_le {t A x : ℝ} (hA : 0 ≤ A)
    (ht : 8*(A+1) ≤ t) (hx : 0 < x) (G : ℂ → ℂ)
    (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ A)
    (z : ℂ) (hz : 192*(‖z‖+‖z‖^2) < t) (hphase : (4+8*A)*‖z‖ ≤ t) :
    ‖bblrCentralWeightDifference G t α x z‖ ≤
      ‖G z‖*(t/2)^(2*z.re)*Real.pi^(-2*z.re)*x^(-z.re)*
        ((1440*(1+‖z‖)+4+8*A)/t) := by
  have htpos : 0 < t := by linarith
  have hbase : (t/2 : ℂ) ≠ 0 :=
    div_ne_zero (Complex.ofReal_ne_zero.mpr htpos.ne') (by norm_num)
  have hp0 : (t/2 : ℂ)^(2*z) ≠ 0 := by
    simp [hbase]
  have he : G z/z*(bblrGammaQuotient t α z-(t/2 : ℂ)^(2*z)) =
      G z*(t/2 : ℂ)^(2*z)*bblrCentralGammaPuncturedError t α z := by
    unfold bblrCentralGammaPuncturedError
    generalize (t/2 : ℂ)^(2*z) = p at hp0 ⊢
    field_simp [hp0]
  have htn : ‖(t/2 : ℂ)^(2*z)‖ = (t/2)^(2*z.re) := by
    have hh := Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < t/2) (2*z)
    simpa using hh
  have hπ : ‖(Real.pi : ℂ)^(-2*z)‖ = Real.pi^(-2*z.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    simp
  have hxn : ‖(x : ℂ)^(-z)‖ = x^(-z.re) := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hx (-z)
  unfold bblrCentralWeightDifference
  rw [he,norm_mul,norm_mul,norm_mul,norm_mul,htn,hπ,hxn]
  have hb := bblrCentralGammaPuncturedError_norm_le hA ht α hα z hz hphase
  calc
    _ ≤ (‖G z‖*(t/2)^(2*z.re)*((1440*(1+‖z‖)+4+8*A)/t))*
        Real.pi^(-2*z.re)*x^(-z.re) := by gcongr
    _ = _ := by ring

theorem bblrCentralNormalizedGamma_dslope_norm_le {t A : ℝ} (hA : 0 ≤ A)
    (ht : 1200*(A+1) ≤ t) (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ A)
    (z : ℂ) (hz : 192*(‖z‖+‖z‖^2) < t) (hphase : (4+8*A)*‖z‖ ≤ t) :
    ‖dslope (bblrCentralNormalizedGamma t α) 0 z‖ ≤
      (4324+8*A)*(1+‖z‖)/t := by
  have htpos : 0 < t := by linarith
  have htA : A < t := by linarith
  have ht8 : 8*(A+1) ≤ t := by linarith
  have hF0 := bblrCentralNormalizedGamma_zero hA htA α hα
  by_cases hsmall : ‖z‖ < 2
  · have hd := (bblrCentralNormalizedGamma_analyticOnNhd_ball hA htA α hα
        (by linarith : (2:ℝ) < t-A)).differentiableOn
    have hmaps : MapsTo (bblrCentralNormalizedGamma t α) (Metric.ball 0 2)
        (Metric.closedBall (bblrCentralNormalizedGamma t α 0) ((8648+16*A)/t)) := by
      intro w hw
      have hwn : ‖w‖ < 2 := by simpa only [Metric.mem_ball,dist_zero_right] using hw
      have hw0 := norm_nonneg w
      have hwsq : ‖w‖^2 < 4 := by nlinarith
      have hwcentral : 192*(‖w‖+‖w‖^2) < t := by nlinarith
      have hwphase : (4+8*A)*‖w‖ ≤ t := by nlinarith
      have he := bblrGammaQuotient_normalized_error_le hA ht8 α hα w hwcentral hwphase
      rw [Metric.mem_closedBall,dist_eq_norm,hF0]
      change ‖bblrGammaQuotient t α w/(t/2 : ℂ)^(2*w)-1‖ ≤ _
      refine he.trans (div_le_div_of_nonneg_right ?_ htpos.le)
      nlinarith
    have hschwarz := Complex.norm_dslope_le_div_of_mapsTo_ball hd hmaps
      (show z ∈ Metric.ball 0 2 by simpa only [Metric.mem_ball,dist_zero_right] using hsmall)
    have hdiv : ((8648+16*A)/t)/2 = (4324+8*A)/t := by ring
    rw [hdiv] at hschwarz
    refine hschwarz.trans (div_le_div_of_nonneg_right ?_ htpos.le)
    nlinarith [norm_nonneg z]
  · have hz0 : z ≠ 0 := by intro he; simp [he] at hsmall
    rw [bblrCentralNormalizedGamma_dslope_eq hA htA α hα hz0]
    change ‖bblrCentralGammaPuncturedError t α z‖ ≤ _
    refine (bblrCentralGammaPuncturedError_norm_le hA ht8 α hα z hz hphase).trans
      (div_le_div_of_nonneg_right ?_ htpos.le)
    nlinarith [norm_nonneg z]

end
end SixthMoment.Source
