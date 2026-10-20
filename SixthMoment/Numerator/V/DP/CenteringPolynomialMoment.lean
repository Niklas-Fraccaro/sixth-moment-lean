import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Rat.Cast.Order
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import SixthMoment.Numerator.V.DP.DPAllPositiveBilinearDerivatives
import SixthMoment.Numerator.V.ReflectedKernel
import Std

namespace SixthMoment
open Complex MeasureTheory Set Metric Filter Polynomial
open scoped Topology BigOperators ComplexConjugate Interval
noncomputable section
set_option maxHeartbeats 1600000

private theorem v_reCLM_norm_le_one : ‖Complex.reCLM‖ ≤ 1 := by
  apply Complex.reCLM.opNorm_le_bound (by norm_num)
  intro v
  simpa using Complex.abs_re_le_norm v

private theorem v_imCLM_norm_le_one : ‖Complex.imCLM‖ ≤ 1 := by
  apply Complex.imCLM.opNorm_le_bound (by norm_num)
  intro v
  simpa using Complex.abs_im_le_norm v

theorem lowerCenteringFactor_zero_real (T x : ℝ) :
    lowerCenteringFactor T (x : ℂ) 0 = 1 := by
  have hs : 0 < (1-complexHeightPoint T (x : ℂ)).re ∧
      (1-complexHeightPoint T (x : ℂ)).re < 1 := by
    simp [complexHeightPoint]
    norm_num
  simp [lowerCenteringFactor,centeringFactorAt,zetaChi_ne_zero_strip hs.1 hs.2]

def vLowerCenteringRemainderMoment (T η : ℝ) (P Q : ℝ[X])
    (Φ : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, (lowerCenteringFactor T ((t/T : ℝ):ℂ) z-1)*
    dpAllPositiveIntegrand T t (Source.dpCoincidentShifts (-z))
      (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) Φ

private theorem vLowerIntegrand_eq_real_weights {T : ℝ} (hT : 1<T)
    (η : ℝ) (P Q : ℝ[X]) (Φ : ℝ→ℝ) (z : ℂ) (t : ℝ) :
    (lowerCenteringFactor T ((t/T : ℝ):ℂ) z-1)*
      dpAllPositiveIntegrand T t (Source.dpCoincidentShifts (-z))
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) Φ =
    (Real.log T:ℂ)⁻¹ *
      (dpAllPositiveIntegrand T t (Source.dpCoincidentShifts (-z))
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q)
        (dpCenteringErrorWeight T Φ z 0 Complex.reCLM)+Complex.I*
      dpAllPositiveIntegrand T t (Source.dpCoincidentShifts (-z))
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q)
        (dpCenteringErrorWeight T Φ z 0 Complex.imCLM)) := by
  have hL0 : (Real.log T:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hT).ne'
  have hs := dpCenteringErrorWeight_complex_split T Φ z 0 (t/T)
  rw [dpCenteringPairError,lowerCenteringFactor_zero_real,mul_one] at hs
  unfold dpAllPositiveIntegrand
  rw [mul_add]
  have hh : (Real.log T:ℂ)⁻¹ *
      ((dpCenteringErrorWeight T Φ z 0 Complex.reCLM (t/T):ℂ)+
        I*(dpCenteringErrorWeight T Φ z 0 Complex.imCLM (t/T):ℂ)) =
      (Φ (t/T):ℂ)*(lowerCenteringFactor T ((t/T:ℝ):ℂ) z-1) := by
    rw [hs]
    field_simp
  linear_combination
    -(zetaChi (1-criticalLinePoint t)*
      allPositiveFourthProduct t (rawMomentShifts T (Source.dpCoincidentShifts (-z)))*
      profileDirichletSum T (zeroExtendedPolynomialProfile η P) (1-criticalLinePoint t)*
      profileDirichletSum T (zeroExtendedPolynomialProfile η Q) (1-criticalLinePoint t))*hh

theorem vLowerCenteringRemainderMoment_eq_real_weights {T : ℝ} (hT : 1<T)
    (η : ℝ) (P Q : ℝ[X]) (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (z : ℂ) (hz : 2*‖z‖ < Real.log T) :
    vLowerCenteringRemainderMoment T η P Q Φ z =
    (dpAllPositiveBilinearMoment T η P Q (Source.dpCoincidentShifts (-z))
      (dpCenteringErrorWeight T Φ z 0 Complex.reCLM)+Complex.I*
      dpAllPositiveBilinearMoment T η P Q (Source.dpCoincidentShifts (-z))
      (dpCenteringErrorWeight T Φ z 0 Complex.imCLM))/(Real.log T:ℂ) := by
  have hL := Real.log_pos hT
  have hzero : 2*‖(0:ℂ)‖ < Real.log T := by simpa using hL
  have hr := dpCenteringErrorWeight_smooth hΦ hL z 0 hz hzero Complex.reCLM
  have hi := dpCenteringErrorWeight_smooth hΦ hL z 0 hz hzero Complex.imCLM
  have hσ : Source.dpCoincidentShifts (-z) ∈ momentNormalizedShiftDomain T := by
    intro j
    have hn : ‖Source.dpCoincidentShifts (-z) j‖ ≤ ‖z‖ := by
      fin_cases j <;> simp [Source.dpCoincidentShifts]
    calc
      _ ≤ ‖rawMomentShifts T (Source.dpCoincidentShifts (-z)) j‖ :=
        Complex.abs_re_le_norm _
      _ = ‖Source.dpCoincidentShifts (-z) j‖/Real.log T := by
        rw [rawMomentShifts,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
      _ ≤ ‖z‖/Real.log T := div_le_div_of_nonneg_right hn hL.le
      _ < 1/2 := (div_lt_iff₀ hL).mpr (by linarith)
  have hir := allPositiveRawIntegrand_integrable hT η η
    (rawMomentShifts T (Source.dpCoincidentShifts (-z))) _ _ _ hσ
    (zeroExtendedPolynomialProfile_zero_above η P)
    (zeroExtendedPolynomialProfile_zero_above η Q) hr
  have hii := allPositiveRawIntegrand_integrable hT η η
    (rawMomentShifts T (Source.dpCoincidentShifts (-z))) _ _ _ hσ
    (zeroExtendedPolynomialProfile_zero_above η P)
    (zeroExtendedPolynomialProfile_zero_above η Q) hi
  change Integrable (fun t => dpAllPositiveIntegrand T t (Source.dpCoincidentShifts (-z))
    (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q)
    (dpCenteringErrorWeight T Φ z 0 Complex.reCLM)) at hir
  change Integrable (fun t => dpAllPositiveIntegrand T t (Source.dpCoincidentShifts (-z))
    (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q)
    (dpCenteringErrorWeight T Φ z 0 Complex.imCLM)) at hii
  unfold vLowerCenteringRemainderMoment
  rw [integral_congr_ae (Filter.Eventually.of_forall
    (vLowerIntegrand_eq_real_weights hT η P Q Φ z)),integral_const_mul,
    integral_add hir (hii.const_mul Complex.I),integral_const_mul]
  unfold dpAllPositiveBilinearMoment
  ring

theorem vLowerCenteringRemainderIntegrand_integrable {T : ℝ} (hT : 1<T)
    (η : ℝ) (P Q : ℝ[X]) (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (z : ℂ) (hz : 2*‖z‖<Real.log T) :
    Integrable (fun t : ℝ => (lowerCenteringFactor T ((t/T:ℝ):ℂ) z-1)*
      dpAllPositiveIntegrand T t (Source.dpCoincidentShifts (-z))
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) Φ) := by
  have hL := Real.log_pos hT
  have hzero : 2*‖(0:ℂ)‖<Real.log T := by simpa using hL
  have hσ : Source.dpCoincidentShifts (-z) ∈ momentNormalizedShiftDomain T := by
    intro j
    have hn : ‖Source.dpCoincidentShifts (-z) j‖≤‖z‖ := by
      fin_cases j <;> simp [Source.dpCoincidentShifts]
    calc
      _ ≤ ‖rawMomentShifts T (Source.dpCoincidentShifts (-z)) j‖ := Complex.abs_re_le_norm _
      _ = ‖Source.dpCoincidentShifts (-z) j‖/Real.log T := by
        rw [rawMomentShifts,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
      _ ≤ ‖z‖/Real.log T := div_le_div_of_nonneg_right hn hL.le
      _ < 1/2 := (div_lt_iff₀ hL).mpr (by linarith)
  have hi (ℓ : ℂ→L[ℝ]ℝ) : Integrable (fun t : ℝ =>
      dpAllPositiveIntegrand T t (Source.dpCoincidentShifts (-z))
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q)
        (dpCenteringErrorWeight T Φ z 0 ℓ)) :=
    allPositiveRawIntegrand_integrable hT η η _ _ _ _ hσ
      (zeroExtendedPolynomialProfile_zero_above η P)
      (zeroExtendedPolynomialProfile_zero_above η Q)
      (dpCenteringErrorWeight_smooth hΦ hL z 0 hz hzero ℓ)
  exact (((hi Complex.reCLM).add ((hi Complex.imCLM).const_mul Complex.I)).const_mul
    (Real.log T:ℂ)⁻¹).congr (Filter.Eventually.of_forall
      (fun t => (vLowerIntegrand_eq_real_weights hT η P Q Φ z t).symm))

theorem vPolynomialMixedIntegrand_functional_equation {T : ℝ} (hT : 1<T)
    (f g Φ : ℝ→ℝ) (z : ℂ) (hz : 2*‖z‖<Real.log T) (t : ℝ) :
    vPolynomialMixedAmplitude T f g Φ t*zetaCMinus T t z =
      Complex.exp (-z/2)*lowerCenteringFactor T ((t/T:ℝ):ℂ) z*
        dpAllPositiveIntegrand T t (Source.dpCoincidentShifts (-z)) f g Φ := by
  have hL := Real.log_pos hT
  have hT0 : T≠0 := (zero_lt_one.trans hT).ne'
  have hp : complexHeightPoint T ((t/T:ℝ):ℂ)=criticalLinePoint t := by
    unfold complexHeightPoint criticalLinePoint
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hT0]
  have hs := centeringShift_mem_strip hL (-t) z hz
  have he : centeringShift T (-t) z=1-criticalLinePoint t+z/(Real.log T:ℂ) := by
    unfold centeringShift criticalLinePoint
    push_cast
    ring
  rw [he] at hs
  have hfe := riemannZeta_strip_functional_equation hs.1 hs.2
  rw [show 1-(1-criticalLinePoint t+z/(Real.log T:ℂ))=
    criticalLinePoint t-z/(Real.log T:ℂ) by ring] at hfe
  have hprod : allPositiveFourthProduct t (rawMomentShifts T (Source.dpCoincidentShifts (-z)))=
      riemannZeta (criticalLinePoint t)^3*riemannZeta (criticalLinePoint t-z/(Real.log T:ℂ)) := by
    simp [allPositiveFourthProduct,rawMomentShifts,Source.dpCoincidentShifts]
    ring
  have hχ : zetaChi (1-criticalLinePoint t)≠0 :=
    zetaChi_ne_zero_strip (by norm_num [sub_re,criticalLinePoint_re])
      (by norm_num [sub_re,criticalLinePoint_re])
  have hexp : Complex.exp (-z/2)*Complex.exp z=Complex.exp (z/2) := by
    rw [←Complex.exp_add]
    congr 1
    ring
  unfold vPolynomialMixedAmplitude zetaCMinus shiftedZetaGenerator
    lowerCenteringFactor centeringFactorAt dpAllPositiveIntegrand
  rw [hp,hprod,hfe]
  field_simp
  simp only [neg_div] at hexp ⊢
  linear_combination
    -((Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
      profileDirichletSum T f (1-criticalLinePoint t)*
      profileDirichletSum T g (1-criticalLinePoint t)*
      zetaChi (1-criticalLinePoint t+z/(Real.log T:ℂ))*
      riemannZeta (criticalLinePoint t-z/(Real.log T:ℂ)))*hexp

theorem vPolynomialMixedGenerator_eq_allPositive_and_error {T : ℝ} (hT : 1<T)
    (η : ℝ) (P Q : ℝ[X]) (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (z : ℂ) (hz : 2*‖z‖<Real.log T) :
    vPolynomialMixedGenerator T (zeroExtendedPolynomialProfile η P)
      (zeroExtendedPolynomialProfile η Q) Φ z = Complex.exp (-z/2)*
      (dpAllPositiveBilinearMoment T η P Q (Source.dpCoincidentShifts (-z)) Φ+
        vLowerCenteringRemainderMoment T η P Q Φ z) := by
  have hL := Real.log_pos hT
  have hσ : Source.dpCoincidentShifts (-z) ∈ momentNormalizedShiftDomain T := by
    intro j
    have hn : ‖Source.dpCoincidentShifts (-z) j‖≤‖z‖ := by
      fin_cases j <;> simp [Source.dpCoincidentShifts]
    calc
      _ ≤ ‖rawMomentShifts T (Source.dpCoincidentShifts (-z)) j‖ := Complex.abs_re_le_norm _
      _ = ‖Source.dpCoincidentShifts (-z) j‖/Real.log T := by
        rw [rawMomentShifts,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
      _ ≤ ‖z‖/Real.log T := div_le_div_of_nonneg_right hn hL.le
      _ < 1/2 := (div_lt_iff₀ hL).mpr (by linarith)
  have hi : Integrable (fun t : ℝ => dpAllPositiveIntegrand T t
      (Source.dpCoincidentShifts (-z)) (zeroExtendedPolynomialProfile η P)
      (zeroExtendedPolynomialProfile η Q) Φ) :=
    allPositiveRawIntegrand_integrable hT η η _ _ _ _ hσ
      (zeroExtendedPolynomialProfile_zero_above η P)
      (zeroExtendedPolynomialProfile_zero_above η Q) hΦ
  have hr := vLowerCenteringRemainderIntegrand_integrable hT η P Q Φ hΦ z hz
  unfold vPolynomialMixedGenerator dpAllPositiveBilinearMoment vLowerCenteringRemainderMoment
  rw [←integral_add hi hr,←integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [vPolynomialMixedIntegrand_functional_equation hT _ _ _ z hz t]
  ring

private theorem v_smooth_integral_norm_le (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    {B : ℝ} (hbound : ∀ x, ‖Φ x‖≤B) : ‖∫ x : ℝ, (Φ x:ℂ)‖≤2*B := by
  have hs : Function.support (fun x : ℝ => (Φ x:ℂ)) ⊆ Ioc (0:ℝ) 2 := by
    intro x hx
    have hm := hΦ.2 (subset_tsupport Φ (by simpa using hx))
    exact ⟨by linarith [hm.1],hm.2⟩
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hs]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 2) (C := B) (f := fun x : ℝ => (Φ x:ℂ))
    (fun x (_hx : x ∈ Ι (0:ℝ) 2) => by simpa only [Complex.norm_real] using hbound x)
  simpa [mul_comm] using hh

private theorem v_square_kernel_compact_bound (η : ℝ) (hη : 0≤η) (P : ℝ[X]) :
    ∃ D : ℝ, 0≤D ∧ ∀ z : ℂ, ‖z‖≤4 → ‖polarPolynomialJ η P z‖≤D := by
  have hc : ContinuousOn (fun z => Source.dpAllPositiveRegularKernel η P
      (Source.dpCoincidentShifts z)) (closedBall (0:ℂ) 4) :=
    (Source.dpAllPositiveRegularKernel_differentiableOn hη P).continuousOn.comp
      Source.dpCoincidentShifts_differentiable.continuous.continuousOn (by
        intro z hz
        exact Source.dpCoincidentShifts_mem_polydisc
          (by simpa only [mem_closedBall,dist_zero_right] using hz))
  obtain ⟨D,hD⟩ := (isCompact_closedBall (0:ℂ) 4).exists_bound_of_continuousOn hc
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro z hz
  have he := Source.dpAllPositiveRegularKernel_coincident η P z (by linarith)
  rw [← he]
  exact (hD z (by simpa only [mem_closedBall,dist_zero_right] using hz)).trans
    (le_max_left _ _)

private theorem v_allPositive_analyticAt {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (η : ℝ) (P Q : ℝ[X]) (Φ : ℝ→ℝ)
    (hΦ : SmoothDyadicWeight Φ) (z : ℂ) (hz : ‖z‖<4) :
    AnalyticAt ℂ (fun w => dpAllPositiveBilinearMoment T η P Q
      (Source.dpCoincidentShifts (-w)) Φ) z := by
  have hR (j : Fin 4) : 2*Source.dpCauchyRadii j<Real.log T := by
    have hr : Source.dpCauchyRadii j≤(8:ℝ) := by fin_cases j <;> norm_num [Source.dpCauchyRadii]
    linarith
  have hm := dpAllPositiveBilinearMoment_differentiableOn_polydisc hT Source.dpCauchyRadii hR
    η P Q Φ hΦ
  have hs : Differentiable ℂ (fun w => Source.dpCoincidentShifts (-w)) :=
    Source.dpCoincidentShifts_differentiable.comp (by fun_prop)
  have hd : DifferentiableOn ℂ (fun w => dpAllPositiveBilinearMoment T η P Q
      (Source.dpCoincidentShifts (-w)) Φ) (ball (0:ℂ) 4) :=
    hm.comp hs.differentiableOn (by
      intro w hw
      apply Source.dpCoincidentShifts_mem_polydisc
      have hn : ‖w‖<4 := by simpa only [mem_ball,dist_zero_right] using hw
      simpa only [norm_neg] using hn.le)
  exact hd.analyticAt (isOpen_ball.mem_nhds
    (by simpa only [mem_ball,dist_zero_right] using hz))

private theorem v_lower_analyticAt {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (η : ℝ) (P Q : ℝ[X]) (Φ : ℝ→ℝ)
    (hΦ : SmoothDyadicWeight Φ) (z : ℂ) (hz : ‖z‖<4) :
    AnalyticAt ℂ (vLowerCenteringRemainderMoment T η P Q Φ) z := by
  have hm := vPolynomialMixedGenerator_analyticAt hT hL η η
    (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) Φ
    (zeroExtendedPolynomialProfile_zero_above η P)
    (zeroExtendedPolynomialProfile_zero_above η Q) hΦ z hz
  have ha := v_allPositive_analyticAt hT hL η P Q Φ hΦ z hz
  have he : vLowerCenteringRemainderMoment T η P Q Φ =ᶠ[𝓝 z]
      (fun w => Complex.exp (w/2)*vPolynomialMixedGenerator T
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) Φ w-
        dpAllPositiveBilinearMoment T η P Q (Source.dpCoincidentShifts (-w)) Φ) := by
    filter_upwards [isOpen_ball.mem_nhds
      (show z∈ball (0:ℂ) 4 by simpa only [mem_ball,dist_zero_right] using hz)] with w hw
    have hn : ‖w‖<4 := by simpa only [mem_ball,dist_zero_right] using hw
    rw [vPolynomialMixedGenerator_eq_allPositive_and_error hT η P Q Φ hΦ w (by linarith)]
    rw [←mul_assoc,←Complex.exp_add]
    simp [show w/2+-w/2=(0:ℂ) by ring]
  exact (((by fun_prop : AnalyticAt ℂ (fun w : ℂ => Complex.exp (w/2)) z).mul hm).sub ha).congr he.symm

private theorem v_reflected_J_analyticAt (η : ℝ) (hη : 0≤η) (P Q : ℝ[X])
    (z : ℂ) (hz : ‖z‖<4) : AnalyticAt ℂ (vReflectedPolynomialJ η P Q) z := by
  exact (by fun_prop : AnalyticAt ℂ (fun w : ℂ => Complex.exp (-w/2)) z).mul
    ((Source.polarPolynomialBilinearJ_analyticAt η hη P Q (-z)
      (by simpa only [norm_neg] using hz)).comp (by fun_prop))

namespace Source

private theorem v_square_actual_uniform_norm_bound (hsource : DPv2SharpInput)
    (η : ℝ) (hη : 0<η) (hηu : η<1/4) (P : ℝ[X]) (B : ℝ) (hB : 0≤B) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ z : ℂ, ‖z‖≤4 →
      ∀ Φ : ℝ→ℝ, SmoothDyadicWeight Φ → WeightSeminormBound 1 B Φ →
      ‖dpAllPositiveMoment T η P (dpCoincidentShifts z) Φ‖≤C*T*(Real.log T)^9 := by
  obtain ⟨C,hC,hSmooth⟩ := dpAllPositiveMoment_coincident_uniform_smoothing
    hsource η hη hηu P B hB
  obtain ⟨D,hD,hKernel⟩ := v_square_kernel_compact_bound η hη.le P
  let A := C+2*B*‖(arithmeticFactor:ℂ)‖*D
  refine ⟨A,by dsimp [A]; positivity,?_⟩
  filter_upwards [hSmooth,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (1:ℝ))]
    with T hSmooth hT hL z hz Φ hΦ hΦB
  have hLp := Real.log_pos hT
  have hW : ‖∫ x : ℝ, (Φ x:ℂ)‖≤2*B :=
    v_smooth_integral_norm_le Φ hΦ (fun x => by simpa using hΦB 0 (by omega) x)
  have hDensity : ‖dpAllPositiveRegularLeadingDensity T η P (dpCoincidentShifts z)‖≤
      ‖(arithmeticFactor:ℂ)‖*(Real.log T)^9*D := by
    unfold dpAllPositiveRegularLeadingDensity
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hLp]
    rw [dpAllPositiveRegularKernel_coincident η P z (by linarith)]
    exact mul_le_mul_of_nonneg_left (hKernel z hz) (by positivity)
  have h89 : (Real.log T)^8≤(Real.log T)^9 := by
    calc
      _ = (Real.log T)^8*1 := by ring
      _ ≤ (Real.log T)^8*Real.log T := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ‖dpAllPositiveMoment T η P (dpCoincidentShifts z) Φ-
      (T:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*dpAllPositiveRegularLeadingDensity T η P (dpCoincidentShifts z)‖+
      ‖(T:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*dpAllPositiveRegularLeadingDensity T η P (dpCoincidentShifts z)‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ C*T*(Real.log T)^8+T*(2*B)*(‖(arithmeticFactor:ℂ)‖*(Real.log T)^9*D) := by
      apply add_le_add (hSmooth _ (dpCoincidentShifts_mem_polydisc hz) Φ hΦ hΦB)
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (zero_lt_one.trans hT)]
      gcongr
      simpa only [Complex.norm_real,Real.norm_eq_abs] using hDensity
    _ ≤ C*T*(Real.log T)^9+T*(2*B)*(‖(arithmeticFactor:ℂ)‖*(Real.log T)^9*D) := by gcongr
    _ = _ := by dsimp [A]; ring

private theorem v_bilinear_actual_uniform_norm_bound (hsource : DPv2SharpInput)
    (η : ℝ) (hη : 0<η) (hηu : η<1/4) (P Q : ℝ[X]) (B : ℝ) (hB : 0≤B) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ z : ℂ, ‖z‖≤4 →
      ∀ Φ : ℝ→ℝ, SmoothDyadicWeight Φ → WeightSeminormBound 1 B Φ →
      ‖dpAllPositiveBilinearMoment T η P Q (dpCoincidentShifts z) Φ‖≤C*T*(Real.log T)^9 := by
  obtain ⟨A,hA,hp⟩ := v_square_actual_uniform_norm_bound hsource η hη hηu (P+Q) B hB
  obtain ⟨D,hD,hm⟩ := v_square_actual_uniform_norm_bound hsource η hη hηu (P-Q) B hB
  refine ⟨(1/4)*(A+D),by positivity,?_⟩
  filter_upwards [hp,hm,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16:ℝ))]
    with T hp hm hT hL z hz Φ hΦ hΦB
  have hR (j : Fin 4) : 2*dpCauchyRadii j<Real.log T := by
    have hj : dpCauchyRadii j≤(8:ℝ) := by fin_cases j <;> norm_num [dpCauchyRadii]
    linarith
  rw [dpAllPositiveBilinearMoment_polarization hT η P Q _ Φ
    (closedPolydisc_subset_momentNormalizedShiftDomain hT dpCauchyRadii hR
      (dpCoincidentShifts_mem_polydisc hz)) hΦ,norm_mul]
  have hc : ‖(1/4:ℂ)‖=(1/4:ℝ) := by norm_num
  rw [hc]
  calc
    _ ≤ (1/4)*(‖dpAllPositiveMoment T η (P+Q) (dpCoincidentShifts z) Φ‖+
      ‖dpAllPositiveMoment T η (P-Q) (dpCoincidentShifts z) Φ‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ ≤ (1/4)*(A*T*(Real.log T)^9+D*T*(Real.log T)^9) := by
      gcongr
      · exact hp z hz Φ hΦ hΦB
      · exact hm z hz Φ hΦ hΦB
    _ = _ := by ring

theorem vLowerCenteringRemainderMoment_uniform_bound (hsource : DPv2SharpInput)
    (η : ℝ) (hη : 0<η) (hηu : η<1/4) (P Q : ℝ[X]) (B : ℝ) (hB : 0≤B) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ Φ : ℝ→ℝ, SmoothDyadicWeight Φ → WeightSeminormBound 1 B Φ →
      ∀ z : ℂ, ‖z‖≤4 →
      ‖vLowerCenteringRemainderMoment T η P Q Φ z‖≤C*T*(Real.log T)^8 := by
  have hCen : 0≤centeringUniformConstant 4 := by
    unfold centeringUniformConstant centeringPhaseComplexBound
    have hp : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  let BW := 15*B*centeringUniformConstant 4
  have hBW : 0≤BW := by dsimp [BW]; positivity
  obtain ⟨A,hA,hActual⟩ := v_bilinear_actual_uniform_norm_bound hsource
    η hη hηu P Q BW hBW
  refine ⟨2*A,by positivity,?_⟩
  filter_upwards [hActual,dpCenteringErrorWeight_uniform_deriv_bound (by norm_num : (0:ℝ)≤4) hB,
    dpCenteringErrorWeight_uniform_norm_bound (by norm_num : (0:ℝ)≤4) hB,
    eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually (eventually_gt_atTop (8:ℝ))]
    with T hActual hDeriv hNorm hT hL Φ hΦ hΦB z hz
  have hLp := Real.log_pos hT
  have hzstrip : 2*‖z‖<Real.log T := by linarith
  have hzero : 2*‖(0:ℂ)‖<Real.log T := by simpa using hLp
  have hMoment (ℓ : ℂ→L[ℝ]ℝ) (hℓ : ‖ℓ‖≤1) :
      ‖dpAllPositiveBilinearMoment T η P Q (dpCoincidentShifts (-z))
        (dpCenteringErrorWeight T Φ z 0 ℓ)‖≤A*T*(Real.log T)^9 := by
    have hW := dpCenteringErrorWeight_smooth hΦ hLp z 0 hzstrip hzero ℓ
    have hWB : WeightSeminormBound 1 BW (dpCenteringErrorWeight T Φ z 0 ℓ) := by
      intro j hj x
      interval_cases j
      · rw [iteratedDeriv_zero]
        exact (hNorm Φ hΦ hΦB z 0 hz (by norm_num) ℓ hℓ x).trans (by dsimp [BW]; nlinarith)
      · rw [iteratedDeriv_one]
        exact hDeriv Φ hΦ hΦB z 0 hz (by norm_num) ℓ hℓ x
    exact hActual (-z) (by simpa using hz) _ hW hWB
  rw [vLowerCenteringRemainderMoment_eq_real_weights hT η P Q Φ hΦ z hzstrip,
    norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hLp]
  calc
    _ ≤ (‖dpAllPositiveBilinearMoment T η P Q (dpCoincidentShifts (-z))
        (dpCenteringErrorWeight T Φ z 0 Complex.reCLM)‖+
      ‖Complex.I*dpAllPositiveBilinearMoment T η P Q (dpCoincidentShifts (-z))
        (dpCenteringErrorWeight T Φ z 0 Complex.imCLM)‖)/Real.log T :=
      div_le_div_of_nonneg_right (norm_add_le _ _) hLp.le
    _ ≤ (A*T*(Real.log T)^9+A*T*(Real.log T)^9)/Real.log T := by
      simp only [norm_mul,Complex.norm_I,one_mul]
      exact div_le_div_of_nonneg_right (add_le_add
        (hMoment Complex.reCLM v_reCLM_norm_le_one)
        (hMoment Complex.imCLM v_imCLM_norm_le_one)) hLp.le
    _ = _ := by field_simp; ring

theorem vLowerCenteringRemainderMoment_uniform_derivative_bound (n : ℕ)
    (hsource : DPv2SharpInput) (η : ℝ) (hη : 0<η) (hηu : η<1/4)
    (P Q : ℝ[X]) (B : ℝ) (hB : 0≤B) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ Φ : ℝ→ℝ, SmoothDyadicWeight Φ → WeightSeminormBound 1 B Φ →
      ∀ z : ℂ, ‖z‖≤2 →
      ‖iteratedDeriv n (vLowerCenteringRemainderMoment T η P Q Φ) z‖≤
        C*T*(Real.log T)^8 := by
  obtain ⟨C,hC,hbound⟩ := vLowerCenteringRemainderMoment_uniform_bound
    hsource η hη hηu P Q B hB
  refine ⟨(n.factorial:ℝ)*C,by positivity,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16:ℝ))]
    with T hbound hT hL Φ hΦ hΦB z hz
  have ha : DifferentiableOn ℂ (vLowerCenteringRemainderMoment T η P Q Φ) (ball (0:ℂ) 4) := by
    intro w hw
    exact (v_lower_analyticAt hT hL η P Q Φ hΦ w
      (by simpa only [mem_ball,dist_zero_right] using hw)).differentiableWithinAt
  have hclosed : closedBall z 1⊆ball (0:ℂ) 4 := by
    intro w hw
    have hwn : ‖w-z‖≤1 := by simpa only [mem_closedBall,dist_eq_norm] using hw
    have hn : ‖w‖≤‖w-z‖+‖z‖ := by
      convert norm_add_le (w-z) z using 1; simp
    have hw4 : ‖w‖<4 := by linarith
    simpa only [mem_ball,dist_zero_right] using hw4
  have hb (w : ℂ) (hw : w∈sphere z 1) :
      ‖vLowerCenteringRemainderMoment T η P Q Φ w‖≤C*T*(Real.log T)^8 :=
    hbound Φ hΦ hΦB w (by
      have hh := hclosed (sphere_subset_closedBall hw)
      exact (show ‖w‖<4 by simpa only [mem_ball,dist_zero_right] using hh).le)
  have hh := cauchy_iteratedDeriv_bound n (by norm_num : (0:ℝ)<1)
    ((ha.mono hclosed).diffContOnCl_ball Subset.rfl) hb
  simp only [one_pow,div_one] at hh
  convert hh using 1; ring

theorem vLowerCenteringRemainderMoment_derivative_normalized_tendsto (n : ℕ)
    (hsource : DPv2SharpInput) (η : ℝ) (hη : 0<η) (hηu : η<1/4)
    (P Q : ℝ[X]) (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (z : ℂ) (hz : ‖z‖≤2) :
    Tendsto (fun T : ℝ => iteratedDeriv n (vLowerCenteringRemainderMoment T η P Q Φ) z/
      ((T:ℂ)*(Real.log T:ℂ)^9)) atTop (𝓝 0) := by
  obtain ⟨B,hB,hΦB⟩ := smoothDyadicWeight_seminorm_one_bound Φ hΦ
  obtain ⟨C,_,hbound⟩ := vLowerCenteringRemainderMoment_uniform_derivative_bound n
    hsource η hη hηu P Q B hB
  exact logNormalizedRemainder_tendsto _ C
    (hbound.mono (fun T h => h Φ hΦ hΦB z hz))

theorem vLowerCenteringRemainderMoment_operator_normalized_tendsto
    (N : ℕ) (q : Fin (N+1)→ℂ) (hsource : DPv2SharpInput)
    (η : ℝ) (hη : 0<η) (hηu : η<1/4) (P Q : ℝ[X])
    (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) (z : ℂ) (hz : ‖z‖≤2) :
    Tendsto (fun T : ℝ => finiteDifferentialOperator N q
      (vLowerCenteringRemainderMoment T η P Q Φ) z/((T:ℂ)*(Real.log T:ℂ)^9))
      atTop (𝓝 0) := by
  have ht := tendsto_finsetSum Finset.univ (fun j (_hj : j∈Finset.univ) =>
    (tendsto_const_nhds (x := q j)).mul
      (vLowerCenteringRemainderMoment_derivative_normalized_tendsto j.val
        hsource η hη hηu P Q Φ hΦ z hz))
  simp only [mul_zero,Finset.sum_const_zero] at ht
  convert ht using 1
  funext T
  unfold finiteDifferentialOperator
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem v_bilinear_polar_error_uniform_bound (hsource : DPv2SharpInput)
    (η : ℝ) (hη : 0<η) (hηu : η<1/4) (P Q : ℝ[X]) (B : ℝ) (hB : 0≤B) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ Φ : ℝ→ℝ, SmoothDyadicWeight Φ → WeightSeminormBound 1 B Φ →
      ∀ z : ℂ, ‖z‖≤4 →
      ‖dpAllPositiveBilinearMoment T η P Q (dpCoincidentShifts z) Φ-
        ((T:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*(arithmeticFactor:ℂ)*(Real.log T:ℂ)^9)*
          polarPolynomialBilinearJ η P Q z‖≤C*T*(Real.log T)^8 := by
  obtain ⟨A,hA,hp⟩ := dpAllPositiveMoment_coincident_uniform_smoothing
    hsource η hη hηu (P+Q) B hB
  obtain ⟨D,hD,hm⟩ := dpAllPositiveMoment_coincident_uniform_smoothing
    hsource η hη hηu (P-Q) B hB
  refine ⟨(1/4)*(A+D),by positivity,?_⟩
  filter_upwards [hp,hm,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16:ℝ))]
    with T hp hm hT hL Φ hΦ hΦB z hz
  have hR (j : Fin 4) : 2*dpCauchyRadii j<Real.log T := by
    have hj : dpCauchyRadii j≤(8:ℝ) := by fin_cases j <;> norm_num [dpCauchyRadii]
    linarith
  have hzp := dpCoincidentShifts_mem_polydisc hz
  have hz16 : ‖z‖<16 := by linarith
  let C0 : ℂ := (T:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*(arithmeticFactor:ℂ)*(Real.log T:ℂ)^9
  have hplus : ‖dpAllPositiveMoment T η (P+Q) (dpCoincidentShifts z) Φ-
      C0*polarPolynomialJ η (P+Q) z‖≤A*T*(Real.log T)^8 := by
    have he : (T:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
        dpAllPositiveRegularLeadingDensity T η (P+Q) (dpCoincidentShifts z)=
        C0*polarPolynomialJ η (P+Q) z := by
      unfold dpAllPositiveRegularLeadingDensity
      rw [dpAllPositiveRegularKernel_coincident η (P+Q) z hz16]
      dsimp [C0]
      ring
    rw [←he]
    exact hp _ hzp Φ hΦ hΦB
  have hminus : ‖dpAllPositiveMoment T η (P-Q) (dpCoincidentShifts z) Φ-
      C0*polarPolynomialJ η (P-Q) z‖≤D*T*(Real.log T)^8 := by
    have he : (T:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
        dpAllPositiveRegularLeadingDensity T η (P-Q) (dpCoincidentShifts z)=
        C0*polarPolynomialJ η (P-Q) z := by
      unfold dpAllPositiveRegularLeadingDensity
      rw [dpAllPositiveRegularKernel_coincident η (P-Q) z hz16]
      dsimp [C0]
      ring
    rw [←he]
    exact hm _ hzp Φ hΦ hΦB
  have he : dpAllPositiveBilinearMoment T η P Q (dpCoincidentShifts z) Φ-
      C0*polarPolynomialBilinearJ η P Q z = (1/4:ℂ)*
      ((dpAllPositiveMoment T η (P+Q) (dpCoincidentShifts z) Φ-C0*polarPolynomialJ η (P+Q) z)-
        (dpAllPositiveMoment T η (P-Q) (dpCoincidentShifts z) Φ-C0*polarPolynomialJ η (P-Q) z)) := by
    rw [dpAllPositiveBilinearMoment_polarization hT η P Q _ Φ
      (closedPolydisc_subset_momentNormalizedShiftDomain hT dpCauchyRadii hR hzp) hΦ,
      polarPolynomialBilinearJ_polarization]
    ring
  change ‖dpAllPositiveBilinearMoment T η P Q (dpCoincidentShifts z) Φ-
    C0*polarPolynomialBilinearJ η P Q z‖≤_
  rw [he,norm_mul,show ‖(1/4:ℂ)‖=(1/4:ℝ) by norm_num]
  calc
    _ ≤ (1/4)*(‖dpAllPositiveMoment T η (P+Q) (dpCoincidentShifts z) Φ-C0*polarPolynomialJ η (P+Q) z‖+
      ‖dpAllPositiveMoment T η (P-Q) (dpCoincidentShifts z) Φ-C0*polarPolynomialJ η (P-Q) z‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ ≤ (1/4)*(A*T*(Real.log T)^8+D*T*(Real.log T)^8) := by gcongr
    _ = _ := by ring

def vPolynomialMomentError (T η : ℝ) (P Q : ℝ[X]) (Φ : ℝ→ℝ) (z : ℂ) : ℂ :=
  vPolynomialMixedGenerator T (zeroExtendedPolynomialProfile η P)
    (zeroExtendedPolynomialProfile η Q) Φ z-
    ((T:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*(arithmeticFactor:ℂ)*(Real.log T:ℂ)^9)*
      vReflectedPolynomialJ η P Q z

theorem vPolynomialMomentError_uniform_bound (hsource : DPv2SharpInput)
    (η : ℝ) (hη : 0<η) (hηu : η<1/4) (P Q : ℝ[X]) (B : ℝ) (hB : 0≤B) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ Φ : ℝ→ℝ, SmoothDyadicWeight Φ → WeightSeminormBound 1 B Φ →
      ∀ z : ℂ, ‖z‖≤4 → ‖vPolynomialMomentError T η P Q Φ z‖≤C*T*(Real.log T)^8 := by
  obtain ⟨A,hA,hPolar⟩ := v_bilinear_polar_error_uniform_bound hsource η hη hηu P Q B hB
  obtain ⟨D,hD,hLower⟩ := vLowerCenteringRemainderMoment_uniform_bound hsource η hη hηu P Q B hB
  refine ⟨Real.exp 2*(A+D),by positivity,?_⟩
  filter_upwards [hPolar,hLower,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16:ℝ))]
    with T hPolar hLower hT hL Φ hΦ hΦB z hz
  have hphase : ‖Complex.exp (-z/2)‖≤Real.exp 2 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hh : (-z/2).re≤‖-z/2‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
    have hn : ‖-z/2‖=‖z‖/2 := by simp
    rw [hn] at hh
    linarith
  have he : vPolynomialMomentError T η P Q Φ z = Complex.exp (-z/2)*
      ((dpAllPositiveBilinearMoment T η P Q (dpCoincidentShifts (-z)) Φ-
        ((T:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*(arithmeticFactor:ℂ)*(Real.log T:ℂ)^9)*
          polarPolynomialBilinearJ η P Q (-z))+vLowerCenteringRemainderMoment T η P Q Φ z) := by
    unfold vPolynomialMomentError vReflectedPolynomialJ
    rw [vPolynomialMixedGenerator_eq_allPositive_and_error hT η P Q Φ hΦ z (by linarith)]
    ring
  rw [he,norm_mul]
  calc
    _ ≤ Real.exp 2*
      (‖dpAllPositiveBilinearMoment T η P Q (dpCoincidentShifts (-z)) Φ-
        ((T:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*(arithmeticFactor:ℂ)*(Real.log T:ℂ)^9)*
          polarPolynomialBilinearJ η P Q (-z)‖+‖vLowerCenteringRemainderMoment T η P Q Φ z‖) :=
      mul_le_mul hphase (norm_add_le _ _) (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp 2*(A*T*(Real.log T)^8+D*T*(Real.log T)^8) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact add_le_add (hPolar Φ hΦ hΦB (-z) (by simpa only [norm_neg] using hz))
        (hLower Φ hΦ hΦB z hz)
    _ = _ := by ring

private theorem v_moment_error_analyticAt {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (η : ℝ) (hη : 0≤η) (P Q : ℝ[X])
    (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) (z : ℂ) (hz : ‖z‖<4) :
    AnalyticAt ℂ (vPolynomialMomentError T η P Q Φ) z := by
  exact (vPolynomialMixedGenerator_analyticAt hT hL η η
    (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) Φ
    (zeroExtendedPolynomialProfile_zero_above η P)
    (zeroExtendedPolynomialProfile_zero_above η Q) hΦ z hz).sub
    (analyticAt_const.mul (v_reflected_J_analyticAt η hη P Q z hz))

theorem vPolynomialMomentError_uniform_derivative_bound (n : ℕ)
    (hsource : DPv2SharpInput) (η : ℝ) (hη : 0<η) (hηu : η<1/4)
    (P Q : ℝ[X]) (B : ℝ) (hB : 0≤B) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ Φ : ℝ→ℝ, SmoothDyadicWeight Φ → WeightSeminormBound 1 B Φ →
      ∀ z : ℂ, ‖z‖≤2 → ‖iteratedDeriv n (vPolynomialMomentError T η P Q Φ) z‖≤
        C*T*(Real.log T)^8 := by
  obtain ⟨C,hC,hbound⟩ := vPolynomialMomentError_uniform_bound hsource η hη hηu P Q B hB
  refine ⟨(n.factorial:ℝ)*C,by positivity,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16:ℝ))]
    with T hbound hT hL Φ hΦ hΦB z hz
  have ha : DifferentiableOn ℂ (vPolynomialMomentError T η P Q Φ) (ball (0:ℂ) 4) := by
    intro w hw
    exact (v_moment_error_analyticAt hT hL η hη.le P Q Φ hΦ w
      (by simpa only [mem_ball,dist_zero_right] using hw)).differentiableWithinAt
  have hclosed : closedBall z 1⊆ball (0:ℂ) 4 := by
    intro w hw
    have hwn : ‖w-z‖≤1 := by simpa only [mem_closedBall,dist_eq_norm] using hw
    have hn : ‖w‖≤‖w-z‖+‖z‖ := by convert norm_add_le (w-z) z using 1; simp
    have hw4 : ‖w‖<4 := by linarith
    simpa only [mem_ball,dist_zero_right] using hw4
  have hb (w : ℂ) (hw : w∈sphere z 1) :
      ‖vPolynomialMomentError T η P Q Φ w‖≤C*T*(Real.log T)^8 :=
    hbound Φ hΦ hΦB w (by
      have hh := hclosed (sphere_subset_closedBall hw)
      exact (show ‖w‖<4 by simpa only [mem_ball,dist_zero_right] using hh).le)
  have hh := cauchy_iteratedDeriv_bound n (by norm_num : (0:ℝ)<1)
    ((ha.mono hclosed).diffContOnCl_ball Subset.rfl) hb
  simp only [one_pow,div_one] at hh
  convert hh using 1; ring

theorem vPolynomialMixedGenerator_derivative_tendsto (n : ℕ)
    (hsource : DPv2SharpInput) (η : ℝ) (hη : 0<η) (hηu : η<1/4)
    (P Q : ℝ[X]) (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) (z : ℂ) (hz : ‖z‖≤2) :
    Tendsto (fun T : ℝ => iteratedDeriv n (vPolynomialMixedGenerator T
      (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) Φ) z/
      ((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
        iteratedDeriv n (vReflectedPolynomialJ η P Q) z)) := by
  obtain ⟨B,hB,hΦB⟩ := smoothDyadicWeight_seminorm_one_bound Φ hΦ
  obtain ⟨C,_,hbound⟩ := vPolynomialMomentError_uniform_derivative_bound n hsource η hη hηu P Q B hB
  let E : ℝ→ℂ := fun T => iteratedDeriv n (vPolynomialMomentError T η P Q Φ) z
  have hE := logNormalizedRemainder_tendsto E C (hbound.mono (fun T h => h Φ hΦ hΦB z hz))
  have ht := (tendsto_const_nhds (x := (arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
    iteratedDeriv n (vReflectedPolynomialJ η P Q) z)).add hE
  simp only [add_zero] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16:ℝ))] with T hT hL
  have hT0 : (T:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hT).ne'
  have hL0 : (Real.log T:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hT).ne'
  have hz4 : ‖z‖<4 := by linarith
  have hm := (vPolynomialMixedGenerator_analyticAt hT hL η η
    (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) Φ
    (zeroExtendedPolynomialProfile_zero_above η P)
    (zeroExtendedPolynomialProfile_zero_above η Q) hΦ z hz4).contDiffAt (n := n)
  have hj := (v_reflected_J_analyticAt η hη.le P Q z hz4).contDiffAt (n := n)
  have he : E T=iteratedDeriv n (vPolynomialMixedGenerator T
      (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) Φ) z-
      ((T:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*(arithmeticFactor:ℂ)*(Real.log T:ℂ)^9)*
        iteratedDeriv n (vReflectedPolynomialJ η P Q) z := by
    dsimp only [E]
    unfold vPolynomialMomentError
    rw [iteratedDeriv_fun_sub hm (contDiffAt_const.mul hj),iteratedDeriv_const_mul_field]
  rw [he]
  field_simp
  ring

theorem vPolynomialMixedGenerator_operator_tendsto (N : ℕ) (q : Fin (N+1)→ℂ)
    (hsource : DPv2SharpInput) (η : ℝ) (hη : 0<η) (hηu : η<1/4)
    (P Q : ℝ[X]) (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) (z : ℂ) (hz : ‖z‖≤2) :
    Tendsto (fun T : ℝ => finiteDifferentialOperator N q (vPolynomialMixedGenerator T
      (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) Φ) z/
      ((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
        finiteDifferentialOperator N q (vReflectedPolynomialJ η P Q) z)) := by
  have ht := tendsto_finsetSum Finset.univ (fun j (_hj : j∈Finset.univ) =>
    (tendsto_const_nhds (x := q j)).mul
      (vPolynomialMixedGenerator_derivative_tendsto j.val hsource η hη hηu P Q Φ hΦ z hz))
  convert ht using 1
  · funext T
    unfold finiteDifferentialOperator
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · congr 1
    unfold finiteDifferentialOperator
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

end Source
end
end SixthMoment
