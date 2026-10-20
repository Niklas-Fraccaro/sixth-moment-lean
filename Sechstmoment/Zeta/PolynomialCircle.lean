import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
import Sechstmoment.Zeta.Generators

namespace Sechstmoment
open Complex Real Polynomial MeasureTheory Filter Set Metric
open scoped Topology
noncomputable section

def d02CircleExtract (m : ℕ) (f : ℂ → ℂ) : ℂ :=
  (m.factorial:ℂ)/(2*Real.pi*I) * ∮ z in C(0, 1), (1/z^(m+1))*f z

def d02PolynomialCircle (p : ℝ[X]) (f : ℂ → ℂ) : ℂ :=
  p.sum fun m a => (a:ℂ)*d02CircleExtract m f

theorem d02CircleExtract_eq_iteratedDeriv (m : ℕ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (closedBall 0 1)) :
    d02CircleExtract m f = iteratedDeriv m f 0 := by
  have h := hf.circleIntegral_one_div_sub_center_pow_smul (by norm_num : (0:ℝ)<1) m
  simp only [sub_zero, smul_eq_mul] at h
  unfold d02CircleExtract
  rw [h]
  have hm : (m.factorial:ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  field_simp

theorem d02ShiftedZetaGenerator_differentiableOn {T : ℝ} {s : ℂ}
    (hL : 1 ≤ Real.log T) (hs : 1 < |s.im|) :
    DifferentiableOn ℂ (shiftedZetaGenerator T s) (closedBall 0 1) := by
  have hLp : 0 < Real.log T := by linarith
  intro z hz
  have hzn : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
  have hzim : |z.im| ≤ 1 := (Complex.abs_im_le_norm z).trans hzn
  have hpole : s+z/(Real.log T:ℂ) ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [add_im, Complex.div_ofReal_im, one_im] at hi
    have habs : |s.im| = |z.im|/Real.log T := by
      have he : s.im = -(z.im/Real.log T) := by linarith
      rw [he, abs_neg, abs_div, abs_of_pos hLp]
    have hdiv : |z.im|/Real.log T ≤ 1 := (div_le_iff₀ hLp).mpr (by simpa using hzim.trans hL)
    linarith
  have hzeta := (analyticOn_riemannZeta (s+z/(Real.log T:ℂ))
    (by simpa using hpole)).differentiableAt
  exact ((by fun_prop : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (w/2)) z).mul
    (hzeta.comp z (by fun_prop))).differentiableWithinAt

theorem d02_zetaPolynomialDerivative_eq_circle {T : ℝ} (s : ℂ)
    (hT : 1 < T) (hL : 1 ≤ Real.log T) (hs : 1 < |s.im|) (p : ℝ[X]) :
    zetaPolynomialDerivative T p s = d02PolynomialCircle p (shiftedZetaGenerator T s) := by
  have hs1 : s ≠ 1 := by intro h; norm_num [h] at hs
  unfold zetaPolynomialDerivative d02PolynomialCircle Polynomial.sum
  apply Finset.sum_congr rfl
  intro m hm
  change (p.coeff m : ℂ) * centeredZetaDerivative T m s =
    (p.coeff m : ℂ) * d02CircleExtract m (shiftedZetaGenerator T s)
  rw [d02CircleExtract_eq_iteratedDeriv _ _
    (d02ShiftedZetaGenerator_differentiableOn hL hs),
    iteratedDeriv_shiftedZetaGenerator_of_one_lt T s m hT hs1]

theorem d02_zetaCp_eq_circle {T t : ℝ} (hT : 1 < T)
    (hL : 1 ≤ Real.log T) (ht : 1 < |t|) (p : ℝ[X]) :
    zetaCp T t p = d02PolynomialCircle p (zetaCPlus T t) := by
  exact d02_zetaPolynomialDerivative_eq_circle (criticalLinePoint t) hT hL
    (by simpa [criticalLinePoint] using ht) p

theorem d02_lower_zetaPolynomial_eq_circle {T t : ℝ} (hT : 1 < T)
    (hL : 1 ≤ Real.log T) (ht : 1 < |t|) (q : ℝ[X]) :
    zetaPolynomialDerivative T q (1-criticalLinePoint t) =
      d02PolynomialCircle q (zetaCMinus T t) := by
  exact d02_zetaPolynomialDerivative_eq_circle (1-criticalLinePoint t) hT hL
    (by simpa [criticalLinePoint] using ht) q

theorem d02CircleExtract_exp (m : ℕ) (c : ℂ) :
    d02CircleExtract m (fun z : ℂ => Complex.exp (c*z)) = c^m := by
  rw [d02CircleExtract_eq_iteratedDeriv m _ (by fun_prop), iteratedDeriv_cexp_const_mul]
  simp

theorem d02PolynomialCircle_exp (p : ℝ[X]) (c : ℂ) :
    d02PolynomialCircle p (fun z : ℂ => Complex.exp (c*z)) =
      p.eval₂ Complex.ofRealHom c := by
  simp only [d02PolynomialCircle, d02CircleExtract_exp, Polynomial.eval₂_eq_sum]
  rfl

theorem d02PolynomialCircle_exp_real (p : ℝ[X]) (x : ℝ) :
    d02PolynomialCircle p (fun z : ℂ => Complex.exp ((x:ℂ)*z)) = ((p.eval x : ℝ) : ℂ) := by
  rw [d02PolynomialCircle_exp]
  simpa using (Polynomial.eval₂_at_apply (p := p) Complex.ofRealHom x)

private theorem d02CircleKernel_norm (m : ℕ) {z : ℂ}
    (hz : z ∈ sphere (0 : ℂ) 1) : ‖1 / z ^ (m + 1)‖ = 1 := by
  have hn : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
  simp [norm_pow, hn]

private theorem d02CircleKernel_continuousOn (m : ℕ) :
    ContinuousOn (fun z : ℂ => 1 / z ^ (m + 1)) (sphere (0 : ℂ) 1) := by
  refine continuousOn_const.div (continuousOn_id.pow _) ?_
  intro z hz
  apply pow_ne_zero
  intro hzero
  have hn : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
  simp [hzero] at hn

theorem d02CircleExtract_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (m : ℕ) {F : ι → ℂ → ℂ} {g : ℂ → ℂ}
    (hf : ∀ᶠ i in l, ContinuousOn (F i) (sphere (0 : ℂ) 1))
    (hF : TendstoUniformlyOn F g l (sphere (0 : ℂ) 1)) :
    Tendsto (fun i => d02CircleExtract m (F i)) l (𝓝 (d02CircleExtract m g)) := by
  have hw : TendstoUniformlyOn
      (fun i (z : ℂ) => (1 / z ^ (m + 1)) * F i z)
      (fun z : ℂ => (1 / z ^ (m + 1)) * g z) l (sphere (0 : ℂ) 1) := by
    rw [Metric.tendstoUniformlyOn_iff] at hF ⊢
    intro ε hε
    filter_upwards [hF ε hε] with i hi
    intro z hz
    simpa only [dist_eq_norm, ← mul_sub, norm_mul, d02CircleKernel_norm m hz,
      one_mul] using hi z hz
  have hc := hf.mono fun i hi => (d02CircleKernel_continuousOn m).mul hi
  have ht := hw.tendsto_circleIntegral_of_continuousOn (by norm_num : (0 : ℝ) ≤ 1) hc
  unfold d02CircleExtract
  exact tendsto_const_nhds.mul ht

theorem d02PolynomialCircle_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (p : ℝ[X]) {F : ι → ℂ → ℂ} {g : ℂ → ℂ}
    (hf : ∀ᶠ i in l, ContinuousOn (F i) (sphere (0 : ℂ) 1))
    (hF : TendstoUniformlyOn F g l (sphere (0 : ℂ) 1)) :
    Tendsto (fun i => d02PolynomialCircle p (F i)) l (𝓝 (d02PolynomialCircle p g)) := by
  unfold d02PolynomialCircle Polynomial.sum
  apply tendsto_finsetSum
  intro m hm
  exact tendsto_const_nhds.mul (d02CircleExtract_tendsto m hf hF)

theorem d02_iteratedDeriv_tendsto_of_uniform_circle
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (m : ℕ) {F : ι → ℂ → ℂ} {g : ℂ → ℂ}
    (hf : ∀ᶠ i in l, DifferentiableOn ℂ (F i) (closedBall (0 : ℂ) 1))
    (hg : DifferentiableOn ℂ g (closedBall (0 : ℂ) 1))
    (hF : TendstoUniformlyOn F g l (sphere (0 : ℂ) 1)) :
    Tendsto (fun i => iteratedDeriv m (F i) 0) l (𝓝 (iteratedDeriv m g 0)) := by
  have hc := d02CircleExtract_tendsto m
    (hf.mono fun i hi => hi.continuousOn.mono sphere_subset_closedBall) hF
  rw [d02CircleExtract_eq_iteratedDeriv m g hg] at hc
  exact hc.congr' (hf.mono fun i hi => d02CircleExtract_eq_iteratedDeriv m (F i) hi)

theorem d02PolynomialCircle_tendsto_exp_real
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (p : ℝ[X]) (x : ℝ) {F : ι → ℂ → ℂ}
    (hf : ∀ᶠ i in l, ContinuousOn (F i) (sphere (0 : ℂ) 1))
    (hF : TendstoUniformlyOn F (fun z : ℂ => Complex.exp ((x : ℂ) * z))
      l (sphere (0 : ℂ) 1)) :
    Tendsto (fun i => d02PolynomialCircle p (F i)) l (𝓝 ((p.eval x : ℝ) : ℂ)) := by
  simpa only [d02PolynomialCircle_exp_real] using d02PolynomialCircle_tendsto p hf hF

theorem d02CircleExtract_const_mul (m : ℕ) (a : ℂ) (f : ℂ → ℂ) :
    d02CircleExtract m (fun z => a * f z) = a * d02CircleExtract m f := by
  have hfun : (fun z : ℂ => (1 / z ^ (m + 1)) * (a * f z)) =
      fun z : ℂ => a * ((1 / z ^ (m + 1)) * f z) := by
    funext z
    ring
  unfold d02CircleExtract
  rw [hfun, circleIntegral.integral_const_mul]
  ring

theorem d02CircleExtract_mul_const (m : ℕ) (f : ℂ → ℂ) (a : ℂ) :
    d02CircleExtract m (fun z => f z * a) = d02CircleExtract m f * a := by
  rw [show (fun z => f z * a) = (fun z => a * f z) by funext z; exact mul_comm _ _,
    d02CircleExtract_const_mul]
  exact mul_comm _ _

theorem d02PolynomialCircle_const_mul (p : ℝ[X]) (a : ℂ) (f : ℂ → ℂ) :
    d02PolynomialCircle p (fun z => a * f z) = a * d02PolynomialCircle p f := by
  unfold d02PolynomialCircle Polynomial.sum
  simp_rw [d02CircleExtract_const_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem d02PolynomialCircle_mul_const (p : ℝ[X]) (f : ℂ → ℂ) (a : ℂ) :
    d02PolynomialCircle p (fun z => f z * a) = d02PolynomialCircle p f * a := by
  rw [show (fun z => f z * a) = (fun z => a * f z) by funext z; exact mul_comm _ _,
    d02PolynomialCircle_const_mul]
  exact mul_comm _ _

theorem d02CircleExtract_add (m : ℕ) (f g : ℂ → ℂ)
    (hf : ContinuousOn f (sphere (0 : ℂ) 1))
    (hg : ContinuousOn g (sphere (0 : ℂ) 1)) :
    d02CircleExtract m (fun z => f z + g z) =
      d02CircleExtract m f + d02CircleExtract m g := by
  have hfi : CircleIntegrable (fun z : ℂ => (1 / z ^ (m + 1)) * f z) 0 1 :=
    ((d02CircleKernel_continuousOn m).mul hf).circleIntegrable
    (by norm_num : (0 : ℝ) ≤ 1)
  have hgi : CircleIntegrable (fun z : ℂ => (1 / z ^ (m + 1)) * g z) 0 1 :=
    ((d02CircleKernel_continuousOn m).mul hg).circleIntegrable
    (by norm_num : (0 : ℝ) ≤ 1)
  have hfun : (fun z : ℂ => (1 / z ^ (m + 1)) * (f z + g z)) =
      fun z : ℂ => (1 / z ^ (m + 1)) * f z + (1 / z ^ (m + 1)) * g z := by
    funext z
    exact mul_add _ _ _
  unfold d02CircleExtract
  rw [hfun, circleIntegral.integral_add hfi hgi]
  ring

theorem d02PolynomialCircle_add (p : ℝ[X]) (f g : ℂ → ℂ)
    (hf : ContinuousOn f (sphere (0 : ℂ) 1))
    (hg : ContinuousOn g (sphere (0 : ℂ) 1)) :
    d02PolynomialCircle p (fun z => f z + g z) =
      d02PolynomialCircle p f + d02PolynomialCircle p g := by
  unfold d02PolynomialCircle Polynomial.sum
  simp_rw [d02CircleExtract_add _ f g hf hg, mul_add]
  rw [Finset.sum_add_distrib]


theorem d02CircleExtract_congr (m : ℕ) {f g : ℂ → ℂ}
    (hfg : EqOn f g (sphere (0 : ℂ) 1)) :
    d02CircleExtract m f = d02CircleExtract m g := by
  unfold d02CircleExtract
  congr 1
  apply circleIntegral.integral_congr (by norm_num : (0 : ℝ) ≤ 1)
  intro z hz
  change (1 / z ^ (m + 1)) * f z = (1 / z ^ (m + 1)) * g z
  rw [hfg hz]

theorem d02PolynomialCircle_congr (p : ℝ[X]) {f g : ℂ → ℂ}
    (hfg : EqOn f g (sphere (0 : ℂ) 1)) :
    d02PolynomialCircle p f = d02PolynomialCircle p g := by
  unfold d02PolynomialCircle Polynomial.sum
  apply Finset.sum_congr rfl
  intro m hm
  change (p.coeff m : ℂ) * d02CircleExtract m f =
    (p.coeff m : ℂ) * d02CircleExtract m g
  rw [d02CircleExtract_congr m hfg]

theorem d02CircleExtract_norm_le (m : ℕ) {f : ℂ → ℂ} {C : ℝ}
    (hf : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ ≤ C) :
    ‖d02CircleExtract m f‖ ≤ (m.factorial : ℝ) * C := by
  unfold d02CircleExtract
  rw [div_eq_mul_inv, mul_assoc, norm_mul]
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (by norm_num : (0 : ℝ) ≤ 1)
    (f := fun z : ℂ => (1 / z ^ (m + 1)) * f z) (C := C) (by
      intro z hz
      simpa only [norm_mul, d02CircleKernel_norm m hz, one_mul] using hf z hz)
  simp only [smul_eq_mul, one_mul] at h
  simpa using mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (m.factorial : ℝ))

def d02PolynomialCircleBound (p : ℝ[X]) : ℝ :=
  p.sum fun m a => |a| * (m.factorial : ℝ)

theorem d02PolynomialCircleBound_nonneg (p : ℝ[X]) :
    0 ≤ d02PolynomialCircleBound p := by
  unfold d02PolynomialCircleBound Polynomial.sum
  exact Finset.sum_nonneg fun m _ => mul_nonneg (abs_nonneg _) (by positivity)

theorem d02PolynomialCircle_norm_le (p : ℝ[X]) {f : ℂ → ℂ} {C : ℝ}
    (hf : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ ≤ C) :
    ‖d02PolynomialCircle p f‖ ≤ d02PolynomialCircleBound p * C := by
  unfold d02PolynomialCircle d02PolynomialCircleBound Polynomial.sum
  calc
    ‖∑ m ∈ p.support, (p.coeff m : ℂ) * d02CircleExtract m f‖ ≤
        ∑ m ∈ p.support, ‖(p.coeff m : ℂ) * d02CircleExtract m f‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ p.support, |p.coeff m| * ((m.factorial : ℝ) * C) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (d02CircleExtract_norm_le m hf) (abs_nonneg _)
    _ = _ := by simp_rw [← mul_assoc]; exact (Finset.sum_mul _ _ _).symm

theorem d02CircleExtract_tendsto_of_dominated
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (m : ℕ) {F : ι → ℂ → ℂ} {g : ℂ → ℂ} {C : ℝ}
    (hf : ∀ᶠ i in l, ContinuousOn (F i) (sphere (0 : ℂ) 1))
    (hbound : ∀ᶠ i in l, ∀ z ∈ sphere (0 : ℂ) 1, ‖F i z‖ ≤ C)
    (hlim : ∀ z ∈ sphere (0 : ℂ) 1, Tendsto (fun i => F i z) l (𝓝 (g z))) :
    Tendsto (fun i => d02CircleExtract m (F i)) l (𝓝 (d02CircleExtract m g)) := by
  let H : ι → ℝ → ℂ := fun i θ => deriv (circleMap 0 1) θ *
    ((1 / (circleMap 0 1 θ) ^ (m + 1)) * F i (circleMap 0 1 θ))
  let G : ℝ → ℂ := fun θ => deriv (circleMap 0 1) θ *
    ((1 / (circleMap 0 1 θ) ^ (m + 1)) * g (circleMap 0 1 θ))
  have hs (θ : ℝ) : circleMap 0 1 θ ∈ sphere (0 : ℂ) 1 :=
    circleMap_mem_sphere 0 (by norm_num : (0 : ℝ) ≤ 1) θ
  have hnorm (θ : ℝ) : ‖deriv (circleMap 0 1) θ‖ = 1 := by
    simp [deriv_circleMap]
  have hmeas : ∀ᶠ i in l, AEStronglyMeasurable (H i)
      (volume.restrict (Icc 0 (2 * Real.pi))) := by
    filter_upwards [hf] with i hi
    apply Continuous.aestronglyMeasurable
    have hc := ((d02CircleKernel_continuousOn m).mul hi).comp_continuous
      (continuous_circleMap 0 1) hs
    dsimp [H]
    exact (by simp_rw [deriv_circleMap]; fun_prop :
      Continuous (fun θ : ℝ => deriv (circleMap 0 1) θ)).mul hc
  have hb : ∀ᶠ i in l, ∀ᵐ θ ∂volume.restrict (Icc 0 (2 * Real.pi)),
      ‖H i θ‖ ≤ C := by
    filter_upwards [hbound] with i hi
    exact Filter.Eventually.of_forall fun θ => by
      dsimp [H]
      simpa only [norm_mul, hnorm θ, d02CircleKernel_norm m (hs θ), one_mul] using
        hi _ (hs θ)
  have ht : Tendsto (fun i => ∫ θ in Icc 0 (2 * Real.pi), H i θ) l
      (𝓝 (∫ θ in Icc 0 (2 * Real.pi), G θ)) :=
    tendsto_integral_filter_of_dominated_convergence (fun _ => C) hmeas hb
      (integrableOn_const isCompact_Icc.measure_ne_top)
      (Filter.Eventually.of_forall fun θ => tendsto_const_nhds.mul
        (tendsto_const_nhds.mul (hlim _ (hs θ))))
  unfold d02CircleExtract
  simp_rw [circleIntegral_def_Icc, smul_eq_mul]
  exact tendsto_const_nhds.mul ht

theorem d02PolynomialCircle_tendsto_of_dominated
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (p : ℝ[X]) {F : ι → ℂ → ℂ} {g : ℂ → ℂ} {C : ℝ}
    (hf : ∀ᶠ i in l, ContinuousOn (F i) (sphere (0 : ℂ) 1))
    (hbound : ∀ᶠ i in l, ∀ z ∈ sphere (0 : ℂ) 1, ‖F i z‖ ≤ C)
    (hlim : ∀ z ∈ sphere (0 : ℂ) 1, Tendsto (fun i => F i z) l (𝓝 (g z))) :
    Tendsto (fun i => d02PolynomialCircle p (F i)) l (𝓝 (d02PolynomialCircle p g)) := by
  unfold d02PolynomialCircle Polynomial.sum
  apply tendsto_finsetSum
  intro m hm
  exact tendsto_const_nhds.mul (d02CircleExtract_tendsto_of_dominated m hf hbound hlim)

theorem d02CircleExtract_continuousOn_parameter (m : ℕ) (F : ℂ → ℂ → ℂ)
    (hF : ContinuousOn (Function.uncurry F)
      ((sphere (0 : ℂ) 1) ×ˢ (sphere (0 : ℂ) 1))) :
    ContinuousOn (fun z => d02CircleExtract m (F z)) (sphere (0 : ℂ) 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous (fun y : (sphere (0 : ℂ) 1) × ℝ =>
      F y.1 (circleMap 0 1 y.2)) := by
    exact hF.comp_continuous (by fun_prop : Continuous
      (fun y : (sphere (0 : ℂ) 1) × ℝ => ((y.1 : ℂ), circleMap 0 1 y.2)))
      (fun y => ⟨y.1.property, circleMap_mem_sphere 0 (by norm_num) y.2⟩)
  have hw : Continuous (fun y : (sphere (0 : ℂ) 1) × ℝ =>
      deriv (circleMap 0 1) y.2 * (1 / (circleMap 0 1 y.2) ^ (m + 1))) := by
    have hne (y : (sphere (0 : ℂ) 1) × ℝ) : circleMap 0 1 y.2 ≠ 0 :=
      circleMap_ne_center (by norm_num : (1 : ℝ) ≠ 0)
    have hpow (y : (sphere (0 : ℂ) 1) × ℝ) :
        circleMap 0 1 y.2 ^ (m + 1) ≠ 0 := pow_ne_zero _ (hne y)
    simp_rw [deriv_circleMap]
    fun_prop
  unfold d02CircleExtract
  simp_rw [circleIntegral_def_Icc, smul_eq_mul, ← mul_assoc]
  apply continuous_const.mul
  exact continuous_parametric_integral_of_continuous (hw.mul hc) isCompact_Icc

theorem d02PolynomialCircle_continuousOn_parameter (p : ℝ[X]) (F : ℂ → ℂ → ℂ)
    (hF : ContinuousOn (Function.uncurry F)
      ((sphere (0 : ℂ) 1) ×ˢ (sphere (0 : ℂ) 1))) :
    ContinuousOn (fun z => d02PolynomialCircle p (F z)) (sphere (0 : ℂ) 1) := by
  unfold d02PolynomialCircle Polynomial.sum
  apply continuousOn_finsetSum
  intro m hm
  exact continuousOn_const.mul (d02CircleExtract_continuousOn_parameter m F hF)

theorem d02PolynomialCircle_two_tendsto_of_dominated
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (p q : ℝ[X]) {F : ι → ℂ → ℂ → ℂ} {g : ℂ → ℂ → ℂ} {C : ℝ}
    (hf : ∀ᶠ i in l, ContinuousOn (Function.uncurry (F i))
      ((sphere (0 : ℂ) 1) ×ˢ (sphere (0 : ℂ) 1)))
    (hbound : ∀ᶠ i in l, ∀ z ∈ sphere (0 : ℂ) 1,
      ∀ w ∈ sphere (0 : ℂ) 1, ‖F i z w‖ ≤ C)
    (hlim : ∀ z ∈ sphere (0 : ℂ) 1, ∀ w ∈ sphere (0 : ℂ) 1,
      Tendsto (fun i => F i z w) l (𝓝 (g z w))) :
    Tendsto (fun i => d02PolynomialCircle p (fun z => d02PolynomialCircle q (F i z))) l
      (𝓝 (d02PolynomialCircle p (fun z => d02PolynomialCircle q (g z)))) := by
  apply d02PolynomialCircle_tendsto_of_dominated p
    (C := d02PolynomialCircleBound q * C)
  · exact hf.mono fun i hi => d02PolynomialCircle_continuousOn_parameter q (F i) hi
  · filter_upwards [hbound] with i hi
    intro z hz
    exact d02PolynomialCircle_norm_le q (hi z hz)
  · intro z hz
    apply d02PolynomialCircle_tendsto_of_dominated q
      (C := C) _ (hbound.mono (fun i hi => hi z hz)) (hlim z hz)
    filter_upwards [hf] with i hi
    exact hi.comp (by fun_prop : ContinuousOn (fun w : ℂ => (z,w))
      (sphere (0 : ℂ) 1)) (fun w hw => ⟨hz,hw⟩)

end
end Sechstmoment
