import Mathlib.Algebra.Order.Chebyshev
import SixthMoment.Denominator.Gram.Reflection
import SixthMoment.Denominator.Gram.SelfMoments
import SixthMoment.Zeta.Moments.AnalyticMomentLinearity

namespace SixthMoment
open Complex MeasureTheory Set Polynomial Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
set_option maxHeartbeats 0

def d06ReflectionAmplitude (τ : TestType) (T t : ℝ) (q : ℝ[X])
    (f g : ℝ → ℝ) : ℂ :=
  d06PolynomialReflectionError T t q * profileDirichletSum T f (criticalLinePoint t) *
    profileDirichletSum T g (match τ with
      | .U => 1-criticalLinePoint t
      | .V => criticalLinePoint t)

theorem d06_zetaPolynomialDerivative_X_pow (T : ℝ) (s : ℂ) (m : ℕ) :
    zetaPolynomialDerivative T (X^m) s = centeredZetaDerivative T m s := by
  simp [zetaPolynomialDerivative,X_pow_eq_monomial]

theorem d06PolynomialAmplitude_continuous (negative : Bool) (τ : TestType)
    {T : ℝ} (hT : 1<T) (a b : ℝ) (p : ℝ[X]) (f g : ℝ → ℝ)
    (hf : ∀ x,a<x → f x=0) (hg : ∀ x,b<x → g x=0) :
    Continuous (fun t => d06PolynomialAmplitude negative τ T t p f g) := by
  have hs : Continuous criticalLinePoint := by unfold criticalLinePoint; fun_prop
  have hsm : Continuous (fun t : ℝ => 1-criticalLinePoint t) := continuous_const.sub hs
  have hp : Continuous (fun t => zetaPolynomialDerivative T p (1-criticalLinePoint t)) := by
    simpa only [d04_zetaCp_conj] using (d06_zetaCp_continuous T p).star
  cases negative with
  | false =>
    cases τ with
    | U =>
      exact (((d06_zetaCp_continuous T p).mul
        ((profileDirichletSum_continuous hT a f hf).comp hs)).mul
          ((profileDirichletSum_continuous hT b g hg).comp hsm))
    | V =>
      exact (((d06_zetaCp_continuous T p).mul
        ((profileDirichletSum_continuous hT a f hf).comp hs)).mul
          ((profileDirichletSum_continuous hT b g hg).comp hs))
  | true =>
    cases τ with
    | U =>
      exact ((hp.mul ((profileDirichletSum_continuous hT a f hf).comp hs)).mul
        ((profileDirichletSum_continuous hT b g hg).comp hsm))
    | V =>
      exact ((hp.mul ((profileDirichletSum_continuous hT a f hf).comp hs)).mul
        ((profileDirichletSum_continuous hT b g hg).comp hs))

theorem d06PolynomialReflectionError_continuous (T : ℝ) (q : ℝ[X]) :
    Continuous (fun t => d06PolynomialReflectionError T t q) := by
  have hp : Continuous (fun t =>
      zetaPolynomialDerivative T (reflectedTestPolynomial q) (1-criticalLinePoint t)) := by
    simpa only [d04_zetaCp_conj] using (d06_zetaCp_continuous T (reflectedTestPolynomial q)).star
  exact ((criticalChi_continuous.inv₀ (fun t => criticalChi_ne_zero t)).mul
    (d06_zetaCp_continuous T q)).sub hp

theorem d06ReflectionAmplitude_continuous (τ : TestType) {T : ℝ} (hT : 1<T)
    (a b : ℝ) (q : ℝ[X]) (f g : ℝ → ℝ)
    (hf : ∀ x,a<x → f x=0) (hg : ∀ x,b<x → g x=0) :
    Continuous (fun t => d06ReflectionAmplitude τ T t q f g) := by
  have hs : Continuous criticalLinePoint := by unfold criticalLinePoint; fun_prop
  have hsm : Continuous (fun t : ℝ => 1-criticalLinePoint t) := continuous_const.sub hs
  cases τ <;> unfold d06ReflectionAmplitude
  · exact ((d06PolynomialReflectionError_continuous T q).mul
      ((profileDirichletSum_continuous hT a f hf).comp hs)).mul
        ((profileDirichletSum_continuous hT b g hg).comp hsm)
  · exact ((d06PolynomialReflectionError_continuous T q).mul
      ((profileDirichletSum_continuous hT a f hf).comp hs)).mul
        ((profileDirichletSum_continuous hT b g hg).comp hs)

theorem d06ReflectionAmplitude_eventually_norm_bound (q : ℝ[X]) (hq : q.natDegree≤4)
    (f g : ℝ → ℝ) :
    ∀ᶠ T : ℝ in atTop,∀ t∈Icc T (2*T),∀ τ,
      ‖d06ReflectionAmplitude τ T t q f g‖ ≤
        (d06ReflectionConstant q/Real.log T)*
          (∑ k ∈ Finset.range 5,‖d06PolynomialAmplitude true τ T t (X^k) f g‖) := by
  filter_upwards [d06PolynomialReflectionError_eventually_norm_bound q hq]
    with T hT
  intro t ht τ
  have h := hT t ht
  unfold d06ReflectionAmplitude
  simp only [norm_mul]
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (norm_nonneg _))
    (norm_nonneg _)).trans_eq
  unfold d06LowerDerivativeNormSum
  have he (k : ℕ) : ‖d06PolynomialAmplitude true τ T t (X^k) f g‖ =
      ‖centeredZetaDerivative T k (1-criticalLinePoint t)‖ *
        ‖profileDirichletSum T f (criticalLinePoint t)‖ *
        ‖profileDirichletSum T g (match τ with
          | .U => 1-criticalLinePoint t | .V => criticalLinePoint t)‖ := by
    cases τ <;> simp [d06PolynomialAmplitude,d06_zetaPolynomialDerivative_X_pow]
  simp_rw [he]
  rw [← Finset.sum_mul,← Finset.sum_mul]
  ring

theorem d06ReflectionAmplitude_self_eventually_bound
    (a b : ℝ) (ha : 0<a) (hb : 0<b) (hab : a+b<1/2)
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfs : tsupport f⊆Icc 0 a) (hgs : tsupport g⊆Icc 0 b)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (hΦpos : ∀ x,0≤Φ x)
    (q : ℝ[X]) (hq : q.natDegree≤4) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ τ,
      (∫ t : ℝ,Φ (t/T)*‖d06ReflectionAmplitude τ T t q f g‖^2)/
        (T*(Real.log T)^9)≤C/(Real.log T)^2 := by
  have hex (k : Fin 5) : ∃ B : ℝ,0≤B ∧ ∀ᶠ T : ℝ in atTop,∀ negative τ,
      (∫ t : ℝ,Φ (t/T)*‖d06PolynomialAmplitude negative τ T t (X^k.val) f g‖^2)/
        (T*(Real.log T)^9)≤B :=
    d06PolynomialAmplitude_self_eventually_bound a b ha hb hab f g hf hg hfs hgs
      Φ hΦ (X^k.val) (by simp; omega)
  choose B hBn hB using hex
  have hK : 0≤d06ReflectionConstant q := d06ReflectionConstant_nonneg q
  have hBnSum : 0≤∑ k : Fin 5,B k := Finset.sum_nonneg (fun k _ => hBn k)
  let C : ℝ := 5*(d06ReflectionConstant q)^2*(∑ k : Fin 5,B k)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  have habove : ∀ x,a<x → f x=0 := by
    intro x hx
    by_contra hn
    exact (not_le_of_gt hx) (hfs (subset_tsupport f hn)).2
  have hbabove : ∀ x,b<x → g x=0 := by
    intro x hx
    by_contra hn
    exact (not_le_of_gt hx) (hgs (subset_tsupport g hn)).2
  filter_upwards [Filter.eventually_all.mpr hB,
    d06ReflectionAmplitude_eventually_norm_bound q hq f g,eventually_gt_atTop (1:ℝ)]
    with T hB hnorm hT
  intro τ
  have hL : 0<Real.log T := Real.log_pos hT
  have hS : 0<T*(Real.log T)^9 := mul_pos (zero_lt_one.trans hT) (pow_pos hL _)
  have hiR := d06_weighted_norm_sq_integrable (zero_lt_one.trans hT) Φ
    (fun t => d06ReflectionAmplitude τ T t q f g) hΦ hΦpos
      (d06ReflectionAmplitude_continuous τ hT a b q f g habove hbabove)
  have hiP (k : Fin 5) := d06_weighted_norm_sq_integrable (zero_lt_one.trans hT) Φ
    (fun t => d06PolynomialAmplitude true τ T t (X^k.val) f g) hΦ hΦpos
      (d06PolynomialAmplitude_continuous true τ hT a b (X^k.val) f g habove hbabove)
  have hbound : (∫ t : ℝ,Φ (t/T)*‖d06ReflectionAmplitude τ T t q f g‖^2) ≤
      (5*(d06ReflectionConstant q/Real.log T)^2)*
        (∑ k : Fin 5,∫ t : ℝ,Φ (t/T)*‖d06PolynomialAmplitude true τ T t (X^k.val) f g‖^2) := by
    rw [← integral_finsetSum (Finset.univ : Finset (Fin 5)) (fun k _ => hiP k),← integral_const_mul]
    apply integral_mono hiR ((integrable_finsetSum _ (fun k _ => hiP k)).const_mul _)
    intro t
    dsimp only
    by_cases hz : Φ (t/T)=0
    · simp [hz]
    · have hwindow := hΦ.2 (subset_tsupport Φ hz)
      have ht : t∈Icc T (2*T) :=
        ⟨by simpa using (le_div_iff₀ (zero_lt_one.trans hT)).mp hwindow.1,
          (div_le_iff₀ (zero_lt_one.trans hT)).mp hwindow.2⟩
      have hnr := hnorm t ht τ
      rw [← Fin.sum_univ_eq_sum_range] at hnr
      have hsumsq : (∑ k : Fin 5,‖d06PolynomialAmplitude true τ T t (X^k.val) f g‖)^2 ≤
          5*(∑ k : Fin 5,‖d06PolynomialAmplitude true τ T t (X^k.val) f g‖^2) := by
        simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun k : Fin 5 => ‖d06PolynomialAmplitude true τ T t (X^k.val) f g‖))
      have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnr
      have hprod := hsq.trans (by
        simpa only [mul_pow] using mul_le_mul_of_nonneg_left hsumsq
          (sq_nonneg (d06ReflectionConstant q/Real.log T)))
      rw [← Finset.mul_sum]
      convert mul_le_mul_of_nonneg_left hprod (hΦpos (t/T)) using 1
      ring
  have hmass : (∑ k : Fin 5,∫ t : ℝ,Φ (t/T)*‖d06PolynomialAmplitude true τ T t (X^k.val) f g‖^2) ≤
      (∑ k : Fin 5,B k)*(T*(Real.log T)^9) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k _
    exact (div_le_iff₀ hS).mp (hB k true τ)
  apply (div_le_iff₀ hS).mpr
  apply hbound.trans
  convert mul_le_mul_of_nonneg_left hmass
    (show 0≤5*(d06ReflectionConstant q/Real.log T)^2 by positivity) using 1
  dsimp [C]
  field_simp

theorem d06ReflectionProductMoment_normalized_tendsto
    (τ σ : TestType) (k : ℤ) (a : Fin 4 → ℝ) (ha : ∀ i,0<a i)
    (hpair1 : a 0+a 1<1/2) (hpair2 : a 2+a 3<1/2)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ i,Continuous (ρ i))
    (hρs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (hΦpos : ∀ x,0≤Φ x)
    (p q : ℝ[X]) (hp : p.natDegree≤4) (hq : q.natDegree≤4) :
    Tendsto (fun T : ℝ =>
      (∫ t : ℝ,(Φ (t/T):ℂ)*(criticalChi t)^k*
        d06PolynomialAmplitude false τ T t p (ρ 0) (ρ 1)*
        d06ReflectionAmplitude σ T t q (ρ 2) (ρ 3))/(T*(Real.log T)^9:ℂ))
      atTop (𝓝 0) := by
  obtain ⟨B,hB,hFb⟩ := d06PolynomialAmplitude_self_eventually_bound
    (a 0) (a 1) (ha 0) (ha 1) hpair1 (ρ 0) (ρ 1) (hρ 0) (hρ 1)
      (hρs 0) (hρs 1) Φ hΦ p hp
  obtain ⟨C,hC,hGb⟩ := d06ReflectionAmplitude_self_eventually_bound
    (a 2) (a 3) (ha 2) (ha 3) hpair2 (ρ 2) (ρ 3) (hρ 2) (hρ 3)
      (hρs 2) (hρs 3) Φ hΦ hΦpos q hq
  have hcap : ∀ i x,a i<x → ρ i x=0 := by
    intro i x hx
    by_contra hn
    exact (not_le_of_gt hx) (hρs i (subset_tsupport (ρ i) hn)).2
  let F : ℝ → ℝ → ℂ := fun T t =>
    (criticalChi t)^k*d06PolynomialAmplitude false τ T t p (ρ 0) (ρ 1)
  let G : ℝ → ℝ → ℂ := fun T t => d06ReflectionAmplitude σ T t q (ρ 2) (ρ 3)
  have hFnorm (T t : ℝ) : ‖F T t‖=‖d06PolynomialAmplitude false τ T t p (ρ 0) (ρ 1)‖ := by
    simp [F,norm_zpow,criticalChi_norm]
  have hcont : ∀ᶠ T : ℝ in atTop,Continuous (F T) ∧ Continuous (G T) := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
    exact ⟨(criticalChi_continuous.zpow₀ k (fun t => Or.inl (criticalChi_ne_zero t))).mul
      (d06PolynomialAmplitude_continuous false τ hT (a 0) (a 1) p (ρ 0) (ρ 1)
        (hcap 0) (hcap 1)),
      d06ReflectionAmplitude_continuous σ hT (a 2) (a 3) q (ρ 2) (ρ 3)
        (hcap 2) (hcap 3)⟩
  have hFb' : ∀ᶠ T : ℝ in atTop,
      (∫ t : ℝ,Φ (t/T)*‖F T t‖^2)/(T*(Real.log T)^9)≤B := by
    filter_upwards [hFb] with T hT
    simpa only [hFnorm] using hT false τ
  have hGb' : ∀ᶠ T : ℝ in atTop,
      (∫ t : ℝ,Φ (t/T)*‖G T t‖^2)/(T*(Real.log T)^9)≤C/(Real.log T)^2 := by
    filter_upwards [hGb] with T hT
    exact hT σ
  have h := d06_weighted_product_smallL2_tendsto Φ hΦ hΦpos F G B C hB hC hcont hFb' hGb'
  apply h.congr'
  filter_upwards [] with T
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  dsimp [F,G]
  ring

end
end SixthMoment
