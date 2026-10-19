import Sechstmoment.Denominator.Gram.Analytic
import Sechstmoment.Zeta.TestTypes

/-! Weighted Cauchy--Schwarz with a coefficient bounded only on the
actual dyadic support; this is used for the literal centering errors. -/
namespace Sechstmoment
open Complex MeasureTheory Filter Set Polynomial
open scoped Topology ComplexConjugate
noncomputable section
set_option maxHeartbeats 0

theorem d06_weighted_product_coefficient_bound {T c : ℝ} (hT : 0<T) (hc : 0≤c)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (hΦpos : ∀ x,0≤Φ x)
    (F G E : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G) (hE : Continuous E)
    (hEb : ∀ t∈Icc T (2*T),‖E t‖≤c) :
    ‖∫ t : ℝ,(Φ (t/T):ℂ)*E t*F t*G t‖^2 ≤
      c^2*(∫ t : ℝ,Φ (t/T)*‖F t‖^2)*(∫ t : ℝ,Φ (t/T)*‖G t‖^2) := by
  have hcs := d06_dyadic_weighted_cauchy_schwarz hT Φ (fun t => E t*F t)
    (fun t => star (G t)) hΦ hΦpos (hE.mul hF) hG.star
  simp only [star_star,norm_star] at hcs
  have hi := d06_weighted_norm_sq_integrable hT Φ F hΦ hΦpos hF
  have hiEF := d06_weighted_norm_sq_integrable hT Φ (fun t => E t*F t)
    hΦ hΦpos (hE.mul hF)
  have hb : (∫ t : ℝ,Φ (t/T)*‖E t*F t‖^2) ≤
      c^2*(∫ t : ℝ,Φ (t/T)*‖F t‖^2) := by
    rw [← integral_const_mul]
    apply integral_mono hiEF (hi.const_mul (c^2))
    intro t
    by_cases hz : Φ (t/T)=0
    · simp [hz]
    · have ht := hΦ.2 (subset_tsupport Φ hz)
      have hwindow : t∈Icc T (2*T) := by
        constructor
        · simpa using (le_div_iff₀ hT).mp ht.1
        · exact (div_le_iff₀ hT).mp ht.2
      simp only [norm_mul,mul_pow]
      calc
        _ ≤ Φ (t/T)*(c^2*‖F t‖^2) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              ((sq_le_sq₀ (norm_nonneg (E t)) hc).mpr (hEb t hwindow)) (sq_nonneg _))
            (hΦpos _)
        _ = _ := by ring
  have hGnonneg : 0≤∫ t : ℝ,Φ (t/T)*‖G t‖^2 :=
    integral_nonneg (fun t => mul_nonneg (hΦpos _) (sq_nonneg _))
  have he : (fun t : ℝ => (Φ (t/T):ℂ)*(E t*F t)*G t) =
      (fun t : ℝ => (Φ (t/T):ℂ)*E t*F t*G t) := by funext t; ring
  rw [he] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_right hb hGnonneg)

/-- Bounded normalized L2 masses and an inverse-logarithmic coefficient
make the actual normalized product integral tend to zero. -/
theorem d06_weighted_product_inverseLog_tendsto
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (hΦpos : ∀ x,0≤Φ x)
    (F G E : ℝ → ℝ → ℂ) (B C K : ℝ) (hB : 0≤B) (hC : 0≤C) (hK : 0≤K)
    (hcont : ∀ᶠ T : ℝ in atTop,Continuous (F T) ∧ Continuous (G T) ∧ Continuous (E T))
    (hFbound : ∀ᶠ T : ℝ in atTop,
      (∫ t : ℝ,Φ (t/T)*‖F T t‖^2)/(T*(Real.log T)^9)≤B)
    (hGbound : ∀ᶠ T : ℝ in atTop,
      (∫ t : ℝ,Φ (t/T)*‖G T t‖^2)/(T*(Real.log T)^9)≤C)
    (hEbound : ∀ᶠ T : ℝ in atTop,∀ t∈Icc T (2*T),‖E T t‖≤K/Real.log T) :
    Tendsto (fun T : ℝ => (∫ t : ℝ,(Φ (t/T):ℂ)*E T t*F T t*G T t)/
      (T*(Real.log T)^9:ℂ)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ => K*(B+C+1)/Real.log T) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul (K*(B+C+1))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hlim
  filter_upwards [hcont,hFbound,hGbound,hEbound,eventually_gt_atTop (1:ℝ)]
    with T ht hf hg he hT
  have hL : 0<Real.log T := Real.log_pos hT
  have hS : 0<T*(Real.log T)^9 := mul_pos (zero_lt_one.trans hT) (pow_pos hL _)
  have hb := (div_le_iff₀ hS).mp hf
  have hc := (div_le_iff₀ hS).mp hg
  have hFn : 0≤∫ t : ℝ,Φ (t/T)*‖F T t‖^2 :=
    integral_nonneg (fun t => mul_nonneg (hΦpos _) (sq_nonneg _))
  have hGn : 0≤∫ t : ℝ,Φ (t/T)*‖G T t‖^2 :=
    integral_nonneg (fun t => mul_nonneg (hΦpos _) (sq_nonneg _))
  have hcs := d06_weighted_product_coefficient_bound (zero_lt_one.trans hT)
    (div_nonneg hK hL.le) Φ hΦ hΦpos (F T) (G T) (E T) ht.1 ht.2.1 ht.2.2 he
  rw [mul_assoc] at hcs
  have hmass : (∫ t : ℝ,Φ (t/T)*‖F T t‖^2)*
      (∫ t : ℝ,Φ (t/T)*‖G T t‖^2) ≤
      (B*(T*(Real.log T)^9))*(C*(T*(Real.log T)^9)) :=
    mul_le_mul hb hc hGn (mul_nonneg hB hS.le)
  have hBC : B*C≤(B+C+1)^2 := by nlinarith [sq_nonneg (B-C)]
  have hsquare : ‖∫ t : ℝ,(Φ (t/T):ℂ)*E T t*F T t*G T t‖^2 ≤
      ((K/Real.log T)*(B+C+1)*(T*(Real.log T)^9))^2 := by
    calc
      _ ≤ (K/Real.log T)^2*
          ((B*(T*(Real.log T)^9))*(C*(T*(Real.log T)^9))) :=
        hcs.trans (mul_le_mul_of_nonneg_left hmass (sq_nonneg _))
      _ ≤ (K/Real.log T)^2*((B+C+1)^2*(T*(Real.log T)^9)^2) := by
        have hmult := mul_le_mul_of_nonneg_right hBC (sq_nonneg (T*(Real.log T)^9))
        convert mul_le_mul_of_nonneg_left hmult (sq_nonneg (K/Real.log T)) using 1
        ring
      _ = _ := by ring
  have hn := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsquare
  rw [norm_div,← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hS]
  apply (div_le_iff₀ hS).mpr
  convert hn using 1
  ring

/-- A vanishing normalized L2 error can be multiplied by a bounded L2 test. -/
theorem d06_weighted_product_smallL2_tendsto
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (hΦpos : ∀ x,0≤Φ x)
    (F G : ℝ → ℝ → ℂ) (B C : ℝ) (hB : 0≤B) (hC : 0≤C)
    (hcont : ∀ᶠ T : ℝ in atTop,Continuous (F T) ∧ Continuous (G T))
    (hFbound : ∀ᶠ T : ℝ in atTop,
      (∫ t : ℝ,Φ (t/T)*‖F T t‖^2)/(T*(Real.log T)^9)≤B)
    (hGbound : ∀ᶠ T : ℝ in atTop,
      (∫ t : ℝ,Φ (t/T)*‖G T t‖^2)/(T*(Real.log T)^9)≤C/(Real.log T)^2) :
    Tendsto (fun T : ℝ => (∫ t : ℝ,(Φ (t/T):ℂ)*F T t*G T t)/
      (T*(Real.log T)^9:ℂ)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ => (B+C+1)/Real.log T) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul (B+C+1)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hlim
  filter_upwards [hcont,hFbound,hGbound,eventually_gt_atTop (1:ℝ)]
    with T ht hf hg hT
  have hL : 0<Real.log T := Real.log_pos hT
  have hS : 0<T*(Real.log T)^9 := mul_pos (zero_lt_one.trans hT) (pow_pos hL _)
  have hb := (div_le_iff₀ hS).mp hf
  have hc := (div_le_iff₀ hS).mp hg
  have hGn : 0≤∫ t : ℝ,Φ (t/T)*‖G T t‖^2 :=
    integral_nonneg (fun t => mul_nonneg (hΦpos _) (sq_nonneg _))
  have hcs := d06_dyadic_weighted_cauchy_schwarz (zero_lt_one.trans hT) Φ
    (F T) (fun t => star (G T t)) hΦ hΦpos ht.1 ht.2.star
  simp only [star_star,norm_star] at hcs
  have hmass : (∫ t : ℝ,Φ (t/T)*‖F T t‖^2)*
      (∫ t : ℝ,Φ (t/T)*‖G T t‖^2) ≤
      (B*(T*(Real.log T)^9))*((C/(Real.log T)^2)*(T*(Real.log T)^9)) :=
    mul_le_mul hb hc hGn (mul_nonneg hB hS.le)
  have hBC : B*C≤(B+C+1)^2 := by nlinarith [sq_nonneg (B-C)]
  have hsquare : ‖∫ t : ℝ,(Φ (t/T):ℂ)*F T t*G T t‖^2 ≤
      (((B+C+1)/Real.log T)*(T*(Real.log T)^9))^2 := by
    apply hcs.trans
    apply hmass.trans
    have hm := mul_le_mul_of_nonneg_right hBC
      (show 0≤(T*(Real.log T)^9)^2/(Real.log T)^2 by positivity)
    convert hm using 1 <;> field_simp
  have hn := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsquare
  rw [norm_div,← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hS]
  exact (div_le_iff₀ hS).mpr hn

/-- A two-profile amplitude, with either zeta side and either test arrangement. -/
def d06PolynomialAmplitude (negative : Bool) (τ : TestType) (T t : ℝ)
    (p : ℝ[X]) (f g : ℝ → ℝ) : ℂ :=
  (if negative then zetaPolynomialDerivative T p (1-criticalLinePoint t) else zetaCp T t p) *
    profileDirichletSum T f (criticalLinePoint t) *
    profileDirichletSum T g (match τ with
      | .U => 1-criticalLinePoint t
      | .V => criticalLinePoint t)

def d06SelfProfiles (f g : ℝ → ℝ) : Fin 4 → ℝ → ℝ := ![f,g,f,g]
def d06SelfCaps (a b : ℝ) : Fin 4 → ℝ := ![a,b,a,b]

/-- Conjugation shows that these four arrangements have the same norm. -/
theorem d06PolynomialAmplitude_norm (negative : Bool) (τ : TestType) (T t : ℝ)
    (p : ℝ[X]) (f g : ℝ → ℝ) :
    ‖d06PolynomialAmplitude negative τ T t p f g‖ =
      ‖zetaCp T t p‖*‖profileDirichletSum T f (criticalLinePoint t)‖*
        ‖profileDirichletSum T g (criticalLinePoint t)‖ := by
  have hl : ‖zetaPolynomialDerivative T p (1-criticalLinePoint t)‖=‖zetaCp T t p‖ := by
    rw [← d04_zetaCp_conj,norm_star]
  have hg : ‖profileDirichletSum T g (1-criticalLinePoint t)‖=
      ‖profileDirichletSum T g (criticalLinePoint t)‖ := by
    rw [criticalLinePoint_one_sub]
    change ‖profileDirichletSum T g (conj (criticalLinePoint t))‖ = _
    rw [profileDirichletSum_conj,Complex.norm_conj]
  cases negative <;> cases τ <;> simp [d06PolynomialAmplitude,hl,hg]


end
end Sechstmoment
