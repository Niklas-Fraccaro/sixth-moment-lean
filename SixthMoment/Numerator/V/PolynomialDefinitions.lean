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
import SixthMoment.Analysis.Complex.CauchyBounds
import SixthMoment.Arithmetic.QuadraticDivisor.Definitions
import SixthMoment.Zeta.GeneratorRegularity
import SixthMoment.Zeta.Moments.AnalyticMomentLinearity
import SixthMoment.Zeta.Tests
import Std

namespace SixthMoment
open Complex MeasureTheory Set Metric Filter Polynomial
open scoped Topology BigOperators ComplexConjugate
noncomputable section
set_option maxHeartbeats 1600000

def vPolynomialMixedAmplitude (T : ℝ) (f g Φ : ℝ→ℝ) (t : ℝ) : ℂ :=
  (Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
    profileDirichletSum T f (1-criticalLinePoint t)*
    profileDirichletSum T g (1-criticalLinePoint t)

def vPolynomialMixedGenerator (T : ℝ) (f g Φ : ℝ→ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, vPolynomialMixedAmplitude T f g Φ t*zetaCMinus T t z

def vPolynomialMixedDerivative (n : ℕ) (T : ℝ) (f g Φ : ℝ→ℝ) (z : ℂ) : ℂ :=
  ∫ t in T..2*T, vPolynomialMixedAmplitude T f g Φ t*
    iteratedDeriv n (zetaCMinus T t) z

theorem vPolynomialMixedAmplitude_continuous {T : ℝ} (hT : 1<T)
    (a b : ℝ) (f g Φ : ℝ→ℝ) (hf : ∀x,a<x→f x=0) (hg : ∀x,b<x→g x=0)
    (hΦ : Continuous Φ) : Continuous (vPolynomialMixedAmplitude T f g Φ) := by
  have hs : Continuous (fun t:ℝ=>1-criticalLinePoint t) := by
    unfold criticalLinePoint
    fun_prop
  have hζ : Continuous (fun t:ℝ=>riemannZeta (criticalLinePoint t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (analyticOn_riemannZeta _ (by simpa using criticalLinePoint_ne_one t)).continuousAt.comp
      (by unfold criticalLinePoint; fun_prop)
  exact (((by fun_prop : Continuous (fun t:ℝ=>(Φ (t/T):ℂ))).mul (hζ.pow 3)).mul
    ((profileDirichletSum_continuous hT a f hf).comp hs)).mul
      ((profileDirichletSum_continuous hT b g hg).comp hs)

private def vMinusDerivativeFamily (n : ℕ) {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) : ComplexIntegralFamily (ball (0:ℂ) 4) ℝ where
  value z t := iteratedDeriv n (zetaCMinus T t) z
  derivative z t := ContinuousLinearMap.toSpanSingleton ℂ
    (iteratedDeriv (n+1) (zetaCMinus T t) z)
  continuous_value := zetaCMinus_iteratedDeriv_joint_continuous n hT hL
  continuous_derivative := by
    convert (zetaCMinus_iteratedDeriv_joint_continuous (n+1) hT hL).smul
      (continuous_const (y := ContinuousLinearMap.id ℂ ℂ)) using 1
    funext p
    apply ContinuousLinearMap.ext
    intro v
    change v*iteratedDeriv (n+1) (zetaCMinus T p.2) p.1.1 =
      iteratedDeriv (n+1) (zetaCMinus T p.2) p.1.1*v
    ring
  hasFDerivAt := by
    intro z hz t
    have hn : ‖z‖<4 := by simpa only [mem_ball,dist_zero_right] using hz
    have hd := (zetaCMinus_iteratedDeriv_analyticAt n hT t z (by linarith)).differentiableAt.hasDerivAt
    rw [← iteratedDeriv_succ] at hd
    exact hd.hasFDerivAt

theorem vPolynomialMixedDerivative_hasDerivAt (n : ℕ) {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (a b : ℝ) (f g Φ : ℝ→ℝ)
    (hf : ∀x,a<x→f x=0) (hg : ∀x,b<x→g x=0) (hΦ : SmoothDyadicWeight Φ)
    (z : ℂ) (hz : ‖z‖<4) :
    HasDerivAt (vPolynomialMixedDerivative n T f g Φ)
      (vPolynomialMixedDerivative (n+1) T f g Φ z) z := by
  let A := vPolynomialMixedAmplitude T f g Φ
  have hA : Continuous A := vPolynomialMixedAmplitude_continuous hT a b f g Φ hf hg hΦ.1.continuous
  let F := (((vMinusDerivativeFamily n hT hL).mulAux A hA).reindexAux
    (fun p:Unit×ℝ=>p.2) continuous_snd).intervalIntegral isOpen_ball T (2*T) (by linarith)
  have h := (F.hasFDerivAt z (by simpa only [mem_ball,dist_zero_right] using hz) ()).hasDerivAt
  have hcontinuous : Continuous (fun t:ℝ=>A t • ContinuousLinearMap.toSpanSingleton ℂ
      (iteratedDeriv (n+1) (zetaCMinus T t) z)) := by
    have hh := (zetaCMinus_iteratedDeriv_joint_continuous (n+1) hT hL).comp
      (continuous_const.prodMk continuous_id : Continuous
        (fun t:ℝ => ((⟨z,by simpa only [mem_ball,dist_zero_right] using hz⟩:ball (0:ℂ) 4),t)))
    have hc : Continuous (fun t:ℝ=>ContinuousLinearMap.toSpanSingleton ℂ
        (iteratedDeriv (n+1) (zetaCMinus T t) z)) := by
      convert hh.smul (continuous_const (y := ContinuousLinearMap.id ℂ ℂ)) using 1
      funext t
      apply ContinuousLinearMap.ext
      intro v
      change v*iteratedDeriv (n+1) (zetaCMinus T t) z =
        iteratedDeriv (n+1) (zetaCMinus T t) z*v
      ring
    exact hA.smul hc
  change HasDerivAt (vPolynomialMixedDerivative n T f g Φ)
    ((∫ t in T..2*T, A t • ContinuousLinearMap.toSpanSingleton ℂ
      (iteratedDeriv (n+1) (zetaCMinus T t) z)) 1) z at h
  rw [ContinuousLinearMap.intervalIntegral_apply (hcontinuous.intervalIntegrable T (2*T))] at h
  simpa only [ContinuousLinearMap.toSpanSingleton_apply,smul_apply,
    one_smul,smul_eq_mul,one_mul,vPolynomialMixedDerivative,A] using h

theorem vPolynomialMixedGenerator_eq_interval {T : ℝ} (hT : 0<T)
    (f g Φ : ℝ→ℝ) (hΦ : tsupport Φ⊆Icc 1 2) (z : ℂ) :
    vPolynomialMixedGenerator T f g Φ z = vPolynomialMixedDerivative 0 T f g Φ z := by
  unfold vPolynomialMixedGenerator vPolynomialMixedDerivative
  simp only [iteratedDeriv_zero]
  rw [intervalIntegral.integral_of_le (by linarith : T≤2*T),
    ←integral_Icc_eq_integral_Ioc]
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
  intro t ht
  have hx : t/T∉Icc (1:ℝ) 2 := by
    intro hx
    apply ht
    constructor
    · have hh := (le_div_iff₀ hT).mp hx.1
      linarith
    · have hh := (div_le_iff₀ hT).mp hx.2
      linarith
  have hf0 : Φ (t/T)=0 := image_eq_zero_of_notMem_tsupport (fun h=>hx (hΦ h))
  simp only [vPolynomialMixedAmplitude,hf0,Complex.ofReal_zero,zero_mul]

theorem vPolynomialMixedGenerator_iteratedDeriv (n : ℕ) {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (a b : ℝ) (f g Φ : ℝ→ℝ)
    (hf : ∀x,a<x→f x=0) (hg : ∀x,b<x→g x=0) (hΦ : SmoothDyadicWeight Φ)
    (z : ℂ) (hz : ‖z‖<4) :
    iteratedDeriv n (vPolynomialMixedGenerator T f g Φ) z =
      vPolynomialMixedDerivative n T f g Φ z := by
  induction n generalizing z with
  | zero => exact vPolynomialMixedGenerator_eq_interval (zero_lt_one.trans hT) f g Φ hΦ.2 z
  | succ n hn =>
    have he : iteratedDeriv n (vPolynomialMixedGenerator T f g Φ) =ᶠ[𝓝 z]
        vPolynomialMixedDerivative n T f g Φ := by
      filter_upwards [isOpen_ball.mem_nhds
        (show z∈ball (0:ℂ) 4 by simpa only [mem_ball,dist_zero_right] using hz)] with w hw
      apply hn w
      simpa only [mem_ball,dist_zero_right] using hw
    rw [iteratedDeriv_succ,he.deriv_eq]
    exact (vPolynomialMixedDerivative_hasDerivAt n hT hL a b f g Φ hf hg hΦ z hz).deriv

theorem vPolynomialMixedAmplitude_integral_eq_interval {T : ℝ} (hT : 0<T)
    (f g Φ : ℝ→ℝ) (hΦ : tsupport Φ⊆Icc 1 2) (K : ℝ→ℂ) :
    (∫ t:ℝ, vPolynomialMixedAmplitude T f g Φ t*K t) =
      ∫ t in T..2*T, vPolynomialMixedAmplitude T f g Φ t*K t := by
  rw [intervalIntegral.integral_of_le (by linarith : T≤2*T),←integral_Icc_eq_integral_Ioc]
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
  intro t ht
  have hx : t/T∉Icc (1:ℝ) 2 := by
    intro hx
    apply ht
    constructor
    · have hh := (le_div_iff₀ hT).mp hx.1
      linarith
    · have hh := (div_le_iff₀ hT).mp hx.2
      linarith
  have hf0 : Φ (t/T)=0 := image_eq_zero_of_notMem_tsupport (fun h=>hx (hΦ h))
  simp only [vPolynomialMixedAmplitude,hf0,Complex.ofReal_zero,zero_mul]

theorem vPolynomialMixedDerivative_integrable (n : ℕ) {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (a b : ℝ) (f g Φ : ℝ→ℝ)
    (hf : ∀x,a<x→f x=0) (hg : ∀x,b<x→g x=0) (hΦ : SmoothDyadicWeight Φ)
    (z : ℂ) (hz : ‖z‖<4) :
    Integrable (fun t:ℝ=>vPolynomialMixedAmplitude T f g Φ t*
      iteratedDeriv n (zetaCMinus T t) z) := by
  let zz : ball (0:ℂ) 4 := ⟨z,by simpa only [mem_ball,dist_zero_right] using hz⟩
  have hd := (zetaCMinus_iteratedDeriv_joint_continuous n hT hL).comp
    (continuous_const.prodMk continuous_id : Continuous (fun t:ℝ=>(zz,t)))
  change Continuous (fun t:ℝ=>iteratedDeriv n (zetaCMinus T t) z) at hd
  have hc := (vPolynomialMixedAmplitude_continuous hT a b f g Φ hf hg hΦ.1.continuous).mul hd
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Icc T (2*T)))
  intro t ht
  by_contra hout
  have hx : t/T∉Icc (1:ℝ) 2 := by
    intro hx
    apply hout
    constructor
    · have hh := (le_div_iff₀ (zero_lt_one.trans hT)).mp hx.1
      linarith
    · have hh := (div_le_iff₀ (zero_lt_one.trans hT)).mp hx.2
      linarith
  have hf0 : Φ (t/T)=0 := image_eq_zero_of_notMem_tsupport (fun h=>hx (hΦ.2 h))
  change vPolynomialMixedAmplitude T f g Φ t*
    iteratedDeriv n (zetaCMinus T t) z ≠ 0 at ht
  simp only [vPolynomialMixedAmplitude,hf0,Complex.ofReal_zero,zero_mul,ne_eq,not_true_eq_false] at ht

theorem zetaCp_conj_eq_minus_generator {T : ℝ} (hT : 1<T) (t : ℝ) (p : ℝ[X]) :
    star (zetaCp T t p) =
      p.sum (fun n c => (c:ℂ)*iteratedDeriv n (zetaCMinus T t) 0) := by
  rw [zetaCp_conj]
  unfold zetaPolynomialDerivative
  simp only [Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro n _
  unfold zetaCMinus
  rw [iteratedDeriv_shiftedZetaGenerator_of_one_lt T _ n hT]
  intro h
  have hr := congrArg Complex.re h
  norm_num [sub_re,criticalLinePoint_re] at hr

def vPolynomialRawMixedMoment (T : ℝ) (p : ℝ[X]) (f g Φ : ℝ→ℝ) : ℂ :=
  ∫ t:ℝ, (Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
    star (rawZetaTest .V T t p f g)

theorem vPolynomialRawMixedIntegrand_eq {T : ℝ} (hT : 1<T) (t : ℝ)
    (p : ℝ[X]) (f g Φ : ℝ→ℝ) :
    (Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
      star (rawZetaTest .V T t p f g) =
    p.sum (fun n c => (c:ℂ)*(vPolynomialMixedAmplitude T f g Φ t*
      iteratedDeriv n (zetaCMinus T t) 0)) := by
  simp only [rawZetaTest,star_mul]
  have hc (h : ℝ→ℝ) : star (profileDirichletSum T h (criticalLinePoint t)) =
      profileDirichletSum T h (1-criticalLinePoint t) := by
    change conj (profileDirichletSum T h (criticalLinePoint t)) = _
    rw [criticalLinePoint_one_sub]
    exact (profileDirichletSum_conj T h (criticalLinePoint t)).symm
  rw [zetaCp_conj_eq_minus_generator hT t p,hc f,hc g]
  simp only [Polynomial.sum_def,Finset.mul_sum,vPolynomialMixedAmplitude]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem vPolynomialRawMixedMoment_eq_polynomialOperator {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (a b : ℝ) (p : ℝ[X]) (f g Φ : ℝ→ℝ)
    (hf : ∀x,a<x→f x=0) (hg : ∀x,b<x→g x=0) (hΦ : SmoothDyadicWeight Φ) :
    vPolynomialRawMixedMoment T p f g Φ =
      p.sum (fun n c => (c:ℂ)*iteratedDeriv n (vPolynomialMixedGenerator T f g Φ) 0) := by
  unfold vPolynomialRawMixedMoment
  simp_rw [vPolynomialRawMixedIntegrand_eq hT,Polynomial.sum_def]
  rw [integral_finsetSum _ (fun n _ =>
    (vPolynomialMixedDerivative_integrable n hT hL a b f g Φ hf hg hΦ 0 (by norm_num)).const_mul _)]
  apply Finset.sum_congr rfl
  intro n _
  rw [integral_const_mul,vPolynomialMixedGenerator_iteratedDeriv n hT hL a b f g Φ hf hg hΦ 0 (by norm_num)]
  rw [vPolynomialMixedAmplitude_integral_eq_interval (zero_lt_one.trans hT) f g Φ hΦ.2]
  rfl

theorem vPolynomialRawMixedMoment_eq_finiteDifferentialOperator (N : ℕ)
    {T : ℝ} (hT : 1<T) (hL : 16<Real.log T) (a b : ℝ) (p : ℝ[X])
    (hp : p.natDegree≤N) (f g Φ : ℝ→ℝ)
    (hf : ∀x,a<x→f x=0) (hg : ∀x,b<x→g x=0) (hΦ : SmoothDyadicWeight Φ) :
    vPolynomialRawMixedMoment T p f g Φ =
      finiteDifferentialOperator N (fun j=>(p.coeff j.val:ℂ))
        (vPolynomialMixedGenerator T f g Φ) 0 := by
  rw [vPolynomialRawMixedMoment_eq_polynomialOperator hT hL a b p f g Φ hf hg hΦ]
  rw [p.sum_over_range' (fun n=>by simp) (N+1) (by omega)]
  unfold finiteDifferentialOperator
  exact (Fin.sum_univ_eq_sum_range (fun n =>
    (p.coeff n:ℂ)*iteratedDeriv n (vPolynomialMixedGenerator T f g Φ) 0) (N+1)).symm

theorem vPolynomialMixedGenerator_differentiableOn {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (a b : ℝ) (f g Φ : ℝ→ℝ)
    (hf : ∀x,a<x→f x=0) (hg : ∀x,b<x→g x=0) (hΦ : SmoothDyadicWeight Φ) :
    DifferentiableOn ℂ (vPolynomialMixedGenerator T f g Φ) (ball (0:ℂ) 4) := by
  intro z hz
  have hn : ‖z‖<4 := by simpa only [mem_ball,dist_zero_right] using hz
  have h := vPolynomialMixedDerivative_hasDerivAt 0 hT hL a b f g Φ hf hg hΦ z hn
  have he : vPolynomialMixedGenerator T f g Φ = vPolynomialMixedDerivative 0 T f g Φ :=
    funext (vPolynomialMixedGenerator_eq_interval (zero_lt_one.trans hT) f g Φ hΦ.2)
  rw [←he] at h
  exact h.differentiableAt.differentiableWithinAt

theorem vPolynomialMixedGenerator_analyticAt {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (a b : ℝ) (f g Φ : ℝ→ℝ)
    (hf : ∀x,a<x→f x=0) (hg : ∀x,b<x→g x=0) (hΦ : SmoothDyadicWeight Φ)
    (z : ℂ) (hz : ‖z‖<4) : AnalyticAt ℂ (vPolynomialMixedGenerator T f g Φ) z :=
  (vPolynomialMixedGenerator_differentiableOn hT hL a b f g Φ hf hg hΦ).analyticAt
    (isOpen_ball.mem_nhds (by simpa only [mem_ball,dist_zero_right] using hz))

theorem vPolynomialRawMixedIntegrand_integrable {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (a b : ℝ) (p : ℝ[X]) (f g Φ : ℝ→ℝ)
    (hf : ∀x,a<x→f x=0) (hg : ∀x,b<x→g x=0) (hΦ : SmoothDyadicWeight Φ) :
    Integrable (fun t:ℝ=>(Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
      star (rawZetaTest .V T t p f g)) := by
  have hi := integrable_finsetSum p.support (fun n _ =>
    (vPolynomialMixedDerivative_integrable n hT hL a b f g Φ hf hg hΦ 0 (by norm_num)).const_mul
      (p.coeff n:ℂ))
  exact hi.congr (Eventually.of_forall (fun t =>
    (vPolynomialRawMixedIntegrand_eq hT t p f g Φ).symm))

def vPolynomialProjectedMixedMoment (T : ℝ) (p : ℝ[X]) (f g Φ : ℝ→ℝ) : ℂ :=
  ∫ t:ℝ, (Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
    star (projectedZetaTest .V T t p f g)

theorem vPolynomialProjectedMixedMoment_eq_real {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (a b : ℝ) (p : ℝ[X]) (f g Φ : ℝ→ℝ)
    (hf : ∀x,a<x→f x=0) (hg : ∀x,b<x→g x=0) (hΦ : SmoothDyadicWeight Φ) :
    vPolynomialProjectedMixedMoment T p f g Φ =
      Complex.ofReal ((vPolynomialRawMixedMoment T p f g Φ).re) := by
  have hi := vPolynomialRawMixedIntegrand_integrable hT hL a b p f g Φ hf hg hΦ
  unfold vPolynomialProjectedMixedMoment vPolynomialRawMixedMoment
  have he (t : ℝ) : (Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
      star (projectedZetaTest .V T t p f g) =
      Complex.ofReal (((Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
        star (rawZetaTest .V T t p f g)).re) := by
    rw [mul_assoc,projectedZetaTest_mixed_re]
    apply Complex.ext
    · simp [Complex.mul_re,Complex.mul_im]
      ring
    · simp [Complex.mul_re,Complex.mul_im]
  rw [integral_congr_ae (Eventually.of_forall he)]
  change (∫ t:ℝ, (((Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
    star (rawZetaTest .V T t p f g)).re:ℂ)) = _
  exact (integral_ofReal (𝕜 := ℂ)).trans
    (congrArg Complex.ofReal (integral_re hi))

end
end SixthMoment
