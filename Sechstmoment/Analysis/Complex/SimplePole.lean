import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Rat.Cast.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.RingTheory.PowerSeries.Basic
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
import Mathlib.Topology.UniformSpace.UniformConvergence
import Sechstmoment.Analysis.Mellin.VerticalIntegral
import Std


namespace Sechstmoment

open Real Complex MeasureTheory Filter Set
open scoped BigOperators Topology

noncomputable section

theorem verticalInverse_continuous {c : ℝ} (hc : c ≠ 0) :
    Continuous (fun y : ℝ => ((c:ℂ)+(y:ℂ)*I)⁻¹) := by
  apply Continuous.inv₀ (by fun_prop)
  intro y he
  have hre := congrArg Complex.re he
  simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
    sub_zero,add_zero,zero_re] at hre
  exact hc hre

theorem verticalInverse_symmetric_integral {c : ℝ} (hc : c ≠ 0) (R : ℝ) :
    (∫ y in (-R)..R, ((c:ℂ)+(y:ℂ)*I)⁻¹) = (2*Real.arctan (R/c):ℝ) := by
  have hI := (verticalInverse_continuous hc).intervalIntegrable (μ := volume) (-R) R
  have hre (y : ℝ) : (((c:ℂ)+(y:ℂ)*I)⁻¹).re = c/(c^2+y^2) := by
    change RCLike.re (((c:ℂ)+(y:ℂ)*I)⁻¹) = c/(c^2+y^2)
    rw [RCLike.inv_re,RCLike.normSq_apply]
    simp [pow_two]
  have him (y : ℝ) : (((c:ℂ)+(y:ℂ)*I)⁻¹).im = -(y/(c^2+y^2)) := by
    change RCLike.im (((c:ℂ)+(y:ℂ)*I)⁻¹) = -(y/(c^2+y^2))
    rw [RCLike.inv_im,RCLike.normSq_apply]
    simp [pow_two,neg_div]
  apply Complex.ext
  · change RCLike.re (∫ y in (-R)..R, ((c:ℂ)+(y:ℂ)*I)⁻¹) = 2*Real.arctan (R/c)
    rw [← intervalIntegral.intervalIntegral_re hI]
    change (∫ y in (-R)..R, (((c:ℂ)+(y:ℂ)*I)⁻¹).re) = _
    simp_rw [hre]
    rw [integral_div_sq_add_sq,neg_div,Real.arctan_neg]
    ring
  · change RCLike.im (∫ y in (-R)..R, ((c:ℂ)+(y:ℂ)*I)⁻¹) = 0
    rw [← intervalIntegral.intervalIntegral_im hI]
    change (∫ y in (-R)..R, (((c:ℂ)+(y:ℂ)*I)⁻¹).im) = _
    simp_rw [him]
    rw [intervalIntegral.integral_neg,integral_id_div_sq_add_sq hc]
    simp

theorem verticalInverse_symmetric_integral_tendsto_pos {c : ℝ} (hc : 0 < c) :
    Tendsto (fun R : ℝ => ∫ y in (-R)..R, ((c:ℂ)+(y:ℂ)*I)⁻¹)
      atTop (𝓝 (Real.pi:ℂ)) := by
  have hdiv : Tendsto (fun R : ℝ => R/c) atTop atTop :=
    (tendsto_div_const_atTop_of_pos hc).mpr tendsto_id
  have h := (Real.tendsto_arctan_atTop.mono_right inf_le_left).comp hdiv
  have hm := h.const_mul (2:ℝ)
  have hC := Complex.continuous_ofReal.continuousAt.tendsto.comp hm
  convert hC using 1
  · funext R
    exact verticalInverse_symmetric_integral hc.ne' R
  · congr 1
    ring

theorem verticalInverse_symmetric_integral_tendsto_neg {c : ℝ} (hc : c < 0) :
    Tendsto (fun R : ℝ => ∫ y in (-R)..R, ((c:ℂ)+(y:ℂ)*I)⁻¹)
      atTop (𝓝 (-Real.pi:ℂ)) := by
  have hdiv : Tendsto (fun R : ℝ => R/c) atTop atBot := by
    have hci : c⁻¹ < 0 := by exact inv_neg''.mpr hc
    simpa only [div_eq_mul_inv,mul_comm,id_eq] using
      tendsto_id.const_mul_atTop_of_neg hci
  have h := (Real.tendsto_arctan_atBot.mono_right inf_le_left).comp hdiv
  have hm := h.const_mul (2:ℝ)
  have hC := Complex.continuous_ofReal.continuousAt.tendsto.comp hm
  convert hC using 1
  · funext R
    exact verticalInverse_symmetric_integral hc.ne R
  · push_cast
    ring

theorem horizontalInverse_integral_tendsto_zero (a b : ℝ) :
    Tendsto (fun y : ℝ => ∫ c in a..b, ((c:ℂ)+(y:ℂ)*I)⁻¹)
      (cocompact ℝ) (𝓝 0) := by
  have habs : Tendsto (fun y : ℝ => |y|) (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop]
    exact tendsto_abs_atBot_atTop.sup tendsto_abs_atTop_atTop
  have hlarge : ∀ᶠ y : ℝ in cocompact ℝ, 1 ≤ |y| :=
    habs.eventually (eventually_ge_atTop (1:ℝ))
  have hnorm : ∀ᶠ y : ℝ in cocompact ℝ,
      ‖∫ c in a..b, ((c:ℂ)+(y:ℂ)*I)⁻¹‖ ≤ |b-a| * |y|⁻¹ := by
    filter_upwards [hlarge] with y hy
    have hyp : 0 < |y| := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hy
    have hn (c : ℝ) : ‖((c:ℂ)+(y:ℂ)*I)⁻¹‖ ≤ |y|⁻¹ := by
      rw [norm_inv]
      apply inv_anti₀ hyp
      simpa using Complex.abs_im_le_norm (((c:ℂ)+(y:ℂ)*I):ℂ)
    exact (intervalIntegral.norm_integral_le_of_norm_le_const (fun c _ => hn c)).trans_eq
      (mul_comm _ _)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim := (tendsto_inv_atTop_zero.comp habs).const_mul |b-a|
  simp only [mul_zero] at hlim
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hnorm hlim

theorem mellinDslope_vertical_integral_eq (H : ℂ → ℂ) {c : ℝ}
    (hc : c ≠ 0) (hH : Integrable (fun y : ℝ => H ((c:ℂ)+(y:ℂ)*I)/((c:ℂ)+(y:ℂ)*I)))
    (R : ℝ) :
    (∫ y in (-R)..R, dslope H 0 ((c:ℂ)+(y:ℂ)*I)) =
      (∫ y in (-R)..R, H ((c:ℂ)+(y:ℂ)*I)/((c:ℂ)+(y:ℂ)*I))-
        H 0*(∫ y in (-R)..R, ((c:ℂ)+(y:ℂ)*I)⁻¹) := by
  have hInv := (verticalInverse_continuous hc).intervalIntegrable (μ := volume) (-R) R
  calc
    _ = ∫ y in (-R)..R, H ((c:ℂ)+(y:ℂ)*I)/((c:ℂ)+(y:ℂ)*I)-
        H 0*((c:ℂ)+(y:ℂ)*I)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro y _
      dsimp only
      have hne : (c:ℂ)+(y:ℂ)*I ≠ 0 := by
        intro he
        have h := congrArg Complex.re he
        simp at h
        exact hc h
      rw [dslope_of_ne H hne,slope_def_field,sub_zero]
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub hH.intervalIntegrable (hInv.const_mul (H 0)),
        intervalIntegral.integral_const_mul]

theorem mellinDslope_horizontal_integral_eq
    (H : ℂ → ℂ) {U : Set ℂ} (hH : ContinuousOn H U)
    {a b R : ℝ} (hab : a ≤ b) (hR : R ≠ 0)
    (hstrip : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → z ∈ U) :
    (∫ c in a..b, dslope H 0 ((c:ℂ)+(R:ℂ)*I)) =
      (∫ c in a..b, H ((c:ℂ)+(R:ℂ)*I)/((c:ℂ)+(R:ℂ)*I))-
        H 0*(∫ c in a..b, ((c:ℂ)+(R:ℂ)*I)⁻¹) := by
  have hne (c : ℝ) : (c:ℂ)+(R:ℂ)*I ≠ 0 := by
    intro he
    have h := congrArg Complex.im he
    simp at h
    exact hR h
  have hz : Continuous (fun c : ℝ => (c:ℂ)+(R:ℂ)*I) := by fun_prop
  have hInv : Continuous (fun c : ℝ => ((c:ℂ)+(R:ℂ)*I)⁻¹) := hz.inv₀ hne
  have hHC : ContinuousOn (fun c : ℝ => H ((c:ℂ)+(R:ℂ)*I)) (uIcc a b) := by
    apply hH.comp hz.continuousOn
    intro c hc
    rw [uIcc_of_le hab] at hc
    exact hstrip _ (by simpa using hc.1) (by simpa using hc.2)
  have hHI : IntervalIntegrable (fun c : ℝ => H ((c:ℂ)+(R:ℂ)*I)/((c:ℂ)+(R:ℂ)*I))
      volume a b := by
    exact (hHC.div hz.continuousOn (fun c _ => hne c)).intervalIntegrable
  have hInvI := hInv.intervalIntegrable (μ := volume) a b
  calc
    _ = ∫ c in a..b, H ((c:ℂ)+(R:ℂ)*I)/((c:ℂ)+(R:ℂ)*I)-
        H 0*((c:ℂ)+(R:ℂ)*I)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro c _
      dsimp only
      rw [dslope_of_ne H (hne c),slope_def_field,sub_zero]
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub hHI (hInvI.const_mul (H 0)),
        intervalIntegral.integral_const_mul]

theorem mellinDslope_horizontal_integral_tendsto_zero
    (H : ℂ → ℂ) {U : Set ℂ} (hH : ContinuousOn H U)
    {a b : ℝ} (hab : a ≤ b)
    (hstrip : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → z ∈ U)
    (hedge : Tendsto (fun y : ℝ => ∫ c in a..b,
      H ((c:ℂ)+(y:ℂ)*I)/((c:ℂ)+(y:ℂ)*I)) (cocompact ℝ) (𝓝 0)) :
    Tendsto (fun y : ℝ => ∫ c in a..b, dslope H 0 ((c:ℂ)+(y:ℂ)*I))
      (cocompact ℝ) (𝓝 0) := by
  have hinv := (horizontalInverse_integral_tendsto_zero a b).const_mul (H 0)
  have hlim := hedge.sub hinv
  simp only [mul_zero,sub_zero] at hlim
  apply hlim.congr'
  have habs : Tendsto (fun y : ℝ => |y|) (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop]
    exact tendsto_abs_atBot_atTop.sup tendsto_abs_atTop_atTop
  filter_upwards [habs.eventually (eventually_ge_atTop (1:ℝ))] with y hy
  exact (mellinDslope_horizontal_integral_eq H hH hab
    (by intro he; norm_num [he] at hy) hstrip).symm

theorem mellinRectangle_simplePole_shift
    (H : ℂ → ℂ) {U : Set ℂ} (hU : IsOpen U) (hH : DifferentiableOn ℂ H U)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (hstrip : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → z ∈ U)
    (hLeft : Integrable (fun y : ℝ => H ((a:ℂ)+(y:ℂ)*I)/((a:ℂ)+(y:ℂ)*I)))
    (hRight : Integrable (fun y : ℝ => H ((b:ℂ)+(y:ℂ)*I)/((b:ℂ)+(y:ℂ)*I)))
    (hedge : Tendsto (fun y : ℝ => ∫ c in a..b,
      H ((c:ℂ)+(y:ℂ)*I)/((c:ℂ)+(y:ℂ)*I)) (cocompact ℝ) (𝓝 0)) :
    (∫ y : ℝ, H ((b:ℂ)+(y:ℂ)*I)/((b:ℂ)+(y:ℂ)*I)) =
      (∫ y : ℝ, H ((a:ℂ)+(y:ℂ)*I)/((a:ℂ)+(y:ℂ)*I))+(2*Real.pi:ℂ)*H 0 := by
  have hab : a ≤ b := le_of_lt (ha.trans hb)
  have h0 : (0:ℂ) ∈ U := hstrip 0 (by simpa using ha.le) (by simpa using hb.le)
  have hQ : DifferentiableOn ℂ (dslope H 0) U :=
    (Complex.differentiableOn_dslope (hU.mem_nhds h0)).mpr hH
  have hrect (R : ℝ) :
      (∫ c in a..b, dslope H 0 ((c:ℂ)+((-R:ℝ):ℂ)*I))-
      (∫ c in a..b, dslope H 0 ((c:ℂ)+(R:ℂ)*I))+
      I*(∫ y in (-R)..R, dslope H 0 ((b:ℂ)+(y:ℂ)*I))-
      I*(∫ y in (-R)..R, dslope H 0 ((a:ℂ)+(y:ℂ)*I)) = 0 := by
    have hd : DifferentiableOn ℂ (dslope H 0)
        (uIcc a b ×ℂ uIcc (-R) R) := by
      apply hQ.mono
      intro z hz
      have hre : z.re ∈ uIcc a b := hz.1
      rw [uIcc_of_le hab] at hre
      exact hstrip z hre.1 hre.2
    have hh := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (dslope H 0)
      ((a:ℂ)+((-R:ℝ):ℂ)*I) ((b:ℂ)+(R:ℂ)*I)
      (by simpa using hd)
    simpa [smul_eq_mul] using hh
  have hneg : Tendsto (fun R : ℝ => -R) atTop atBot := tendsto_neg_atTop_atBot
  have hl := MeasureTheory.intervalIntegral_tendsto_integral hLeft hneg tendsto_id
  have hr := MeasureTheory.intervalIntegral_tendsto_integral hRight hneg tendsto_id
  have hlq := hl.sub ((verticalInverse_symmetric_integral_tendsto_neg ha).const_mul (H 0))
  have hrq := hr.sub ((verticalInverse_symmetric_integral_tendsto_pos hb).const_mul (H 0))
  have hLq : Tendsto (fun R : ℝ => ∫ y in (-R)..R, dslope H 0 ((a:ℂ)+(y:ℂ)*I)) atTop
      (𝓝 ((∫ y : ℝ, H ((a:ℂ)+(y:ℂ)*I)/((a:ℂ)+(y:ℂ)*I))-H 0*(-Real.pi:ℂ))) := by
    apply hlq.congr'
    exact Eventually.of_forall (fun R => (mellinDslope_vertical_integral_eq H ha.ne hLeft R).symm)
  have hRq : Tendsto (fun R : ℝ => ∫ y in (-R)..R, dslope H 0 ((b:ℂ)+(y:ℂ)*I)) atTop
      (𝓝 ((∫ y : ℝ, H ((b:ℂ)+(y:ℂ)*I)/((b:ℂ)+(y:ℂ)*I))-H 0*(Real.pi:ℂ))) := by
    apply hrq.congr'
    exact Eventually.of_forall (fun R => (mellinDslope_vertical_integral_eq H hb.ne' hRight R).symm)
  have hEdge := mellinDslope_horizontal_integral_tendsto_zero H hH.continuousOn hab hstrip hedge
  have hTop := hEdge.mono_left atTop_le_cocompact
  have hBot := (hEdge.mono_left atBot_le_cocompact).comp hneg
  have hlim := ((hBot.sub hTop).add (hRq.const_mul I)).sub (hLq.const_mul I)
  have hzero : Tendsto (fun R : ℝ =>
      (∫ c in a..b, dslope H 0 ((c:ℂ)+((-R:ℝ):ℂ)*I))-
      (∫ c in a..b, dslope H 0 ((c:ℂ)+(R:ℂ)*I))+
      I*(∫ y in (-R)..R, dslope H 0 ((b:ℂ)+(y:ℂ)*I))-
      I*(∫ y in (-R)..R, dslope H 0 ((a:ℂ)+(y:ℂ)*I))) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall (fun R => (hrect R).symm)
  simp only [Function.comp_apply,Complex.ofReal_neg] at hlim
  simp only [Complex.ofReal_neg] at hzero
  have he := tendsto_nhds_unique hlim hzero
  simp only [sub_self,zero_add] at he
  have hh :
      (∫ y : ℝ, H ((b:ℂ)+(y:ℂ)*I)/((b:ℂ)+(y:ℂ)*I))-H 0*(Real.pi:ℂ) =
      (∫ y : ℝ, H ((a:ℂ)+(y:ℂ)*I)/((a:ℂ)+(y:ℂ)*I))-H 0*(-Real.pi:ℂ) := by
    apply mul_left_cancel₀ I_ne_zero
    exact sub_eq_zero.mp he
  linear_combination hh

end

end Sechstmoment
