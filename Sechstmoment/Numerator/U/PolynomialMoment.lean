import Sechstmoment.Numerator.U.TwistedMomentHolomorphy
import Sechstmoment.Numerator.V.PolynomialDefinitions

/-! A05: the actual U test from manuscript (1.1), including its conjugated
second amplifier. Its genuine mixed generator is differentiated under its
compact time integral in every order. No asymptotic moment is assumed. -/
namespace Sechstmoment
open Complex MeasureTheory Set Metric Filter Polynomial
open scoped Topology BigOperators ComplexConjugate
noncomputable section
set_option maxHeartbeats 1600000

/-- Actual U amplitude before the lower zeta generator is differentiated. -/
def uPolynomialMixedAmplitude (T : ℝ) (f g Φ : ℝ→ℝ) (t : ℝ) : ℂ :=
  (Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*star (criticalChi t)*
    profileDirichletSum T f (1-criticalLinePoint t)*
    profileDirichletSum T g (criticalLinePoint t)

def uPolynomialMixedGenerator (T : ℝ) (f g Φ : ℝ→ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, uPolynomialMixedAmplitude T f g Φ t*zetaCMinus T t z

def uPolynomialMixedDerivative (n : ℕ) (T : ℝ) (f g Φ : ℝ→ℝ) (z : ℂ) : ℂ :=
  ∫ t in T..2*T, uPolynomialMixedAmplitude T f g Φ t*
    iteratedDeriv n (zetaCMinus T t) z

theorem uPolynomialMixedAmplitude_continuous {T : ℝ} (hT : 1<T)
    (a b : ℝ) (f g Φ : ℝ→ℝ) (hf : ∀x,a<x→f x=0) (hg : ∀x,b<x→g x=0)
    (hΦ : Continuous Φ) : Continuous (uPolynomialMixedAmplitude T f g Φ) := by
  have hs : Continuous (fun t:ℝ=>1-criticalLinePoint t) := by
    unfold criticalLinePoint
    fun_prop
  have hsplus : Continuous (fun t:ℝ=>criticalLinePoint t) := by
    unfold criticalLinePoint
    fun_prop
  have hζ : Continuous (fun t:ℝ=>riemannZeta (criticalLinePoint t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (analyticOn_riemannZeta _ (by simpa using criticalLinePoint_ne_one t)).continuousAt.comp
      hsplus.continuousAt
  exact ((((by fun_prop : Continuous (fun t:ℝ=>(Φ (t/T):ℂ))).mul (hζ.pow 3)).mul
    criticalChi_continuous.star).mul
    ((profileDirichletSum_continuous hT a f hf).comp hs)).mul
      ((profileDirichletSum_continuous hT b g hg).comp hsplus)

private def uMinusDerivativeFamily (n : ℕ) {T : ℝ} (hT : 1<T)
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

/-- Every next derivative of the actual compact mixed integral is obtained
by differentiating its actual zeta integrand. -/
theorem uPolynomialMixedDerivative_hasDerivAt (n : ℕ) {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (a b : ℝ) (f g Φ : ℝ→ℝ)
    (hf : ∀x,a<x→f x=0) (hg : ∀x,b<x→g x=0) (hΦ : SmoothDyadicWeight Φ)
    (z : ℂ) (hz : ‖z‖<4) :
    HasDerivAt (uPolynomialMixedDerivative n T f g Φ)
      (uPolynomialMixedDerivative (n+1) T f g Φ z) z := by
  let A := uPolynomialMixedAmplitude T f g Φ
  have hA : Continuous A := uPolynomialMixedAmplitude_continuous hT a b f g Φ hf hg hΦ.1.continuous
  let F := (((uMinusDerivativeFamily n hT hL).mulAux A hA).reindexAux
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
  change HasDerivAt (uPolynomialMixedDerivative n T f g Φ)
    ((∫ t in T..2*T, A t • ContinuousLinearMap.toSpanSingleton ℂ
      (iteratedDeriv (n+1) (zetaCMinus T t) z)) 1) z at h
  rw [ContinuousLinearMap.intervalIntegral_apply (hcontinuous.intervalIntegrable T (2*T))] at h
  simpa only [ContinuousLinearMap.toSpanSingleton_apply,smul_apply,
    one_smul,smul_eq_mul,one_mul,uPolynomialMixedDerivative,A] using h

/-- The full integral is exactly the actual compact integral, because the
source weight has its proved dyadic support. -/
theorem uPolynomialMixedGenerator_eq_interval {T : ℝ} (hT : 0<T)
    (f g Φ : ℝ→ℝ) (hΦ : tsupport Φ⊆Icc 1 2) (z : ℂ) :
    uPolynomialMixedGenerator T f g Φ z = uPolynomialMixedDerivative 0 T f g Φ z := by
  unfold uPolynomialMixedGenerator uPolynomialMixedDerivative
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
  simp only [uPolynomialMixedAmplitude,hf0,Complex.ofReal_zero,zero_mul]

/-- Genuine all-order differentiation of the literal U mixed moment. -/
theorem uPolynomialMixedGenerator_iteratedDeriv (n : ℕ) {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (a b : ℝ) (f g Φ : ℝ→ℝ)
    (hf : ∀x,a<x→f x=0) (hg : ∀x,b<x→g x=0) (hΦ : SmoothDyadicWeight Φ)
    (z : ℂ) (hz : ‖z‖<4) :
    iteratedDeriv n (uPolynomialMixedGenerator T f g Φ) z =
      uPolynomialMixedDerivative n T f g Φ z := by
  induction n generalizing z with
  | zero => exact uPolynomialMixedGenerator_eq_interval (zero_lt_one.trans hT) f g Φ hΦ.2 z
  | succ n hn =>
    have he : iteratedDeriv n (uPolynomialMixedGenerator T f g Φ) =ᶠ[𝓝 z]
        uPolynomialMixedDerivative n T f g Φ := by
      filter_upwards [isOpen_ball.mem_nhds
        (show z∈ball (0:ℂ) 4 by simpa only [mem_ball,dist_zero_right] using hz)] with w hw
      apply hn w
      simpa only [mem_ball,dist_zero_right] using hw
    rw [iteratedDeriv_succ,he.deriv_eq]
    exact (uPolynomialMixedDerivative_hasDerivAt n hT hL a b f g Φ hf hg hΦ z hz).deriv

/-- Dyadic support turns any actual U-amplitude integral into its compact
interval integral, without assuming integrability of the multiplier. -/
theorem uPolynomialMixedAmplitude_integral_eq_interval {T : ℝ} (hT : 0<T)
    (f g Φ : ℝ→ℝ) (hΦ : tsupport Φ⊆Icc 1 2) (K : ℝ→ℂ) :
    (∫ t:ℝ, uPolynomialMixedAmplitude T f g Φ t*K t) =
      ∫ t in T..2*T, uPolynomialMixedAmplitude T f g Φ t*K t := by
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
  simp only [uPolynomialMixedAmplitude,hf0,Complex.ofReal_zero,zero_mul]

/-- Actual U derivative integrands are integrable: continuity and the actual
compact weight support prove the required domination. -/
theorem uPolynomialMixedDerivative_integrable (n : ℕ) {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (a b : ℝ) (f g Φ : ℝ→ℝ)
    (hf : ∀x,a<x→f x=0) (hg : ∀x,b<x→g x=0) (hΦ : SmoothDyadicWeight Φ)
    (z : ℂ) (hz : ‖z‖<4) :
    Integrable (fun t:ℝ=>uPolynomialMixedAmplitude T f g Φ t*
      iteratedDeriv n (zetaCMinus T t) z) := by
  let zz : ball (0:ℂ) 4 := ⟨z,by simpa only [mem_ball,dist_zero_right] using hz⟩
  have hd := (zetaCMinus_iteratedDeriv_joint_continuous n hT hL).comp
    (continuous_const.prodMk continuous_id : Continuous (fun t:ℝ=>(zz,t)))
  change Continuous (fun t:ℝ=>iteratedDeriv n (zetaCMinus T t) z) at hd
  have hc := (uPolynomialMixedAmplitude_continuous hT a b f g Φ hf hg hΦ.1.continuous).mul hd
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
  change uPolynomialMixedAmplitude T f g Φ t*
    iteratedDeriv n (zetaCMinus T t) z ≠ 0 at ht
  simp only [uPolynomialMixedAmplitude,hf0,Complex.ofReal_zero,zero_mul,ne_eq,not_true_eq_false] at ht

/-- The literal complex U numerator moment, with the actual test from §1.1. -/
def uPolynomialRawMixedMoment (T : ℝ) (p : ℝ[X]) (f g Φ : ℝ→ℝ) : ℂ :=
  ∫ t:ℝ, (Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
    star (rawZetaTest .U T t p f g)

/-- Exact pointwise realization of the actual U integrand by lower-generator
polynomial derivatives. -/
theorem uPolynomialRawMixedIntegrand_eq {T : ℝ} (hT : 1<T) (t : ℝ)
    (p : ℝ[X]) (f g Φ : ℝ→ℝ) :
    (Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
      star (rawZetaTest .U T t p f g) =
    p.sum (fun n c => (c:ℂ)*(uPolynomialMixedAmplitude T f g Φ t*
      iteratedDeriv n (zetaCMinus T t) 0)) := by
  simp only [rawZetaTest,star_mul]
  have hc (h : ℝ→ℝ) : star (profileDirichletSum T h (criticalLinePoint t)) =
      profileDirichletSum T h (1-criticalLinePoint t) := by
    change conj (profileDirichletSum T h (criticalLinePoint t)) = _
    rw [criticalLinePoint_one_sub]
    exact (profileDirichletSum_conj T h (criticalLinePoint t)).symm
  have hcminus : star (profileDirichletSum T g (1-criticalLinePoint t)) =
      profileDirichletSum T g (criticalLinePoint t) := by
    rw [profileDirichletSum_one_sub]
    change conj (conj _) = _
    exact conj_conj _
  rw [zetaCp_conj_eq_minus_generator hT t p,hc f,hcminus]
  simp only [Polynomial.sum_def,Finset.sum_mul,Finset.mul_sum,uPolynomialMixedAmplitude]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- The actual U numerator is exactly the same finite polynomial operator
applied to the genuine mixed integral, with proved integrability. -/
theorem uPolynomialRawMixedMoment_eq_polynomialOperator {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (a b : ℝ) (p : ℝ[X]) (f g Φ : ℝ→ℝ)
    (hf : ∀x,a<x→f x=0) (hg : ∀x,b<x→g x=0) (hΦ : SmoothDyadicWeight Φ) :
    uPolynomialRawMixedMoment T p f g Φ =
      p.sum (fun n c => (c:ℂ)*iteratedDeriv n (uPolynomialMixedGenerator T f g Φ) 0) := by
  unfold uPolynomialRawMixedMoment
  simp_rw [uPolynomialRawMixedIntegrand_eq hT,Polynomial.sum_def]
  rw [integral_finsetSum _ (fun n _ =>
    (uPolynomialMixedDerivative_integrable n hT hL a b f g Φ hf hg hΦ 0 (by norm_num)).const_mul _)]
  apply Finset.sum_congr rfl
  intro n _
  rw [integral_const_mul,uPolynomialMixedGenerator_iteratedDeriv n hT hL a b f g Φ hf hg hΦ 0 (by norm_num)]
  rw [uPolynomialMixedAmplitude_integral_eq_interval (zero_lt_one.trans hT) f g Φ hΦ.2]
  rfl

/-- Literal Fin(N+1) operator form, for every degree bound. -/
theorem uPolynomialRawMixedMoment_eq_finiteDifferentialOperator (N : ℕ)
    {T : ℝ} (hT : 1<T) (hL : 16<Real.log T) (a b : ℝ) (p : ℝ[X])
    (hp : p.natDegree≤N) (f g Φ : ℝ→ℝ)
    (hf : ∀x,a<x→f x=0) (hg : ∀x,b<x→g x=0) (hΦ : SmoothDyadicWeight Φ) :
    uPolynomialRawMixedMoment T p f g Φ =
      finiteDifferentialOperator N (fun j=>(p.coeff j.val:ℂ))
        (uPolynomialMixedGenerator T f g Φ) 0 := by
  rw [uPolynomialRawMixedMoment_eq_polynomialOperator hT hL a b p f g Φ hf hg hΦ]
  rw [p.sum_over_range' (fun n=>by simp) (N+1) (by omega)]
  unfold finiteDifferentialOperator
  exact (Fin.sum_univ_eq_sum_range (fun n =>
    (p.coeff n:ℂ)*iteratedDeriv n (uPolynomialMixedGenerator T f g Φ) 0) (N+1)).symm

/-- The actual U mixed generator is holomorphic on the fixed genuine disk. -/
theorem uPolynomialMixedGenerator_differentiableOn {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (a b : ℝ) (f g Φ : ℝ→ℝ)
    (hf : ∀x,a<x→f x=0) (hg : ∀x,b<x→g x=0) (hΦ : SmoothDyadicWeight Φ) :
    DifferentiableOn ℂ (uPolynomialMixedGenerator T f g Φ) (ball (0:ℂ) 4) := by
  intro z hz
  have hn : ‖z‖<4 := by simpa only [mem_ball,dist_zero_right] using hz
  have h := uPolynomialMixedDerivative_hasDerivAt 0 hT hL a b f g Φ hf hg hΦ z hn
  have he : uPolynomialMixedGenerator T f g Φ = uPolynomialMixedDerivative 0 T f g Φ :=
    funext (uPolynomialMixedGenerator_eq_interval (zero_lt_one.trans hT) f g Φ hΦ.2)
  rw [←he] at h
  exact h.differentiableAt.differentiableWithinAt

theorem uPolynomialMixedGenerator_analyticAt {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (a b : ℝ) (f g Φ : ℝ→ℝ)
    (hf : ∀x,a<x→f x=0) (hg : ∀x,b<x→g x=0) (hΦ : SmoothDyadicWeight Φ)
    (z : ℂ) (hz : ‖z‖<4) : AnalyticAt ℂ (uPolynomialMixedGenerator T f g Φ) z :=
  (uPolynomialMixedGenerator_differentiableOn hT hL a b f g Φ hf hg hΦ).analyticAt
    (isOpen_ball.mem_nhds (by simpa only [mem_ball,dist_zero_right] using hz))

/-- Actual raw U numerator integrability, derived from the proved compact
zeta derivative integrands. -/
theorem uPolynomialRawMixedIntegrand_integrable {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (a b : ℝ) (p : ℝ[X]) (f g Φ : ℝ→ℝ)
    (hf : ∀x,a<x→f x=0) (hg : ∀x,b<x→g x=0) (hΦ : SmoothDyadicWeight Φ) :
    Integrable (fun t:ℝ=>(Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
      star (rawZetaTest .U T t p f g)) := by
  have hi := integrable_finsetSum p.support (fun n _ =>
    (uPolynomialMixedDerivative_integrable n hT hL a b f g Φ hf hg hΦ 0 (by norm_num)).const_mul
      (p.coeff n:ℂ))
  exact hi.congr (Eventually.of_forall (fun t =>
    (uPolynomialRawMixedIntegrand_eq hT t p f g Φ).symm))

/-- The exact phase-projected U numerator integral from §1.1. -/
def uPolynomialProjectedMixedMoment (T : ℝ) (p : ℝ[X]) (f g Φ : ℝ→ℝ) : ℂ :=
  ∫ t:ℝ, (Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
    star (projectedZetaTest .U T t p f g)

/-- Projection takes exactly the real part of the actual complex U moment;
all Bochner integrability requirements are proved from the actual profiles. -/
theorem uPolynomialProjectedMixedMoment_eq_real {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (a b : ℝ) (p : ℝ[X]) (f g Φ : ℝ→ℝ)
    (hf : ∀x,a<x→f x=0) (hg : ∀x,b<x→g x=0) (hΦ : SmoothDyadicWeight Φ) :
    uPolynomialProjectedMixedMoment T p f g Φ =
      Complex.ofReal ((uPolynomialRawMixedMoment T p f g Φ).re) := by
  have hi := uPolynomialRawMixedIntegrand_integrable hT hL a b p f g Φ hf hg hΦ
  unfold uPolynomialProjectedMixedMoment uPolynomialRawMixedMoment
  have he (t : ℝ) : (Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
      star (projectedZetaTest .U T t p f g) =
      Complex.ofReal (((Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
        star (rawZetaTest .U T t p f g)).re) := by
    rw [mul_assoc,projectedZetaTest_mixed_re]
    apply Complex.ext
    · simp [Complex.mul_re,Complex.mul_im]
      ring
    · simp [Complex.mul_re,Complex.mul_im]
  rw [integral_congr_ae (Eventually.of_forall he)]
  change (∫ t:ℝ, (((Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
    star (rawZetaTest .U T t p f g)).re:ℂ)) = _
  exact (integral_ofReal (𝕜 := ℂ)).trans
    (congrArg Complex.ofReal (integral_re hi))

/-- The actual BBLR line needed by the U mixed generator. The shift is on
one lower zeta factor; the amplifier order is necessarily swapped. -/
def uBBLRShifts (z : ℂ) : MomentShifts := ![0,0,z,0]

/-- Exact, unshifted functional equation cancels the U chi multiplier. -/
theorem riemannZeta_mul_star_criticalChi (t : ℝ) :
    riemannZeta (criticalLinePoint t)*star (criticalChi t) =
      riemannZeta (1-criticalLinePoint t) := by
  rw [riemannZeta_critical_functional_equation]
  calc
    _ = (criticalChi t*star (criticalChi t))*riemannZeta (1-criticalLinePoint t) := by ring
    _ = _ := by rw [criticalChi_mul_star,one_mul]

/-- The U generator is exactly a BBLR twisted fourth moment, multiplied by
its literal exp(z/2) centering factor. No Stirling replacement is needed. -/
theorem uPolynomialMixedIntegrand_eq_twistedFourthIntegrand (T t : ℝ)
    (f g Φ : ℝ→ℝ) (z : ℂ) :
    uPolynomialMixedAmplitude T f g Φ t*zetaCMinus T t z =
      Complex.exp (z/2)*twistedFourthIntegrand T t (rawMomentShifts T (uBBLRShifts z))
        g f Φ := by
  have hχ : riemannZeta (criticalLinePoint t)*conj (criticalChi t) =
      riemannZeta (1-criticalLinePoint t) := riemannZeta_mul_star_criticalChi t
  unfold uPolynomialMixedAmplitude zetaCMinus shiftedZetaGenerator
    twistedFourthIntegrand shiftedFourthProduct rawMomentShifts uBBLRShifts
  simp
  linear_combination
    ((Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^2*
      profileDirichletSum T f (1-criticalLinePoint t)*
      profileDirichletSum T g (criticalLinePoint t)*Complex.exp (z/2)*
      riemannZeta (1-criticalLinePoint t+z/(Real.log T:ℂ)))*hχ

/-- Exact bridge from the corrected manuscript U test to the source object. -/
theorem uPolynomialMixedGenerator_eq_twistedFourthMoment (T : ℝ)
    (f g Φ : ℝ→ℝ) (z : ℂ) :
    uPolynomialMixedGenerator T f g Φ z =
      Complex.exp (z/2)*twistedFourthMoment T (rawMomentShifts T (uBBLRShifts z)) g f Φ := by
  unfold uPolynomialMixedGenerator
  simp_rw [uPolynomialMixedIntegrand_eq_twistedFourthIntegrand]
  rw [integral_const_mul]
  rfl

/-- The actual U polynomial moment is precisely its finite differential
operator on the actual centered BBLR moment, with swapped amplifier roles. -/
theorem uPolynomialRawMixedMoment_eq_BBLRDifferentialOperator (N : ℕ)
    {T : ℝ} (hT : 1<T) (hL : 16<Real.log T) (a b : ℝ) (p : ℝ[X])
    (hp : p.natDegree≤N) (f g Φ : ℝ→ℝ)
    (hf : ∀x,a<x→f x=0) (hg : ∀x,b<x→g x=0) (hΦ : SmoothDyadicWeight Φ) :
    uPolynomialRawMixedMoment T p f g Φ =
      finiteDifferentialOperator N (fun j=>(p.coeff j.val:ℂ))
        (fun z : ℂ => Complex.exp (z/2)*
          twistedFourthMoment T (rawMomentShifts T (uBBLRShifts z)) g f Φ) 0 := by
  have he : uPolynomialMixedGenerator T f g Φ = fun z : ℂ =>
      Complex.exp (z/2)*twistedFourthMoment T (rawMomentShifts T (uBBLRShifts z)) g f Φ :=
    funext (uPolynomialMixedGenerator_eq_twistedFourthMoment T f g Φ)
  rw [uPolynomialRawMixedMoment_eq_finiteDifferentialOperator N hT hL a b p hp f g Φ hf hg hΦ,he]

end
end Sechstmoment
