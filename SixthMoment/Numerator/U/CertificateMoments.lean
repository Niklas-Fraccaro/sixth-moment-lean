import SixthMoment.Certificate.Profiles.NumeratorLimit
import SixthMoment.Certificate.Tests
import SixthMoment.Numerator.U.PolynomialMoment

namespace SixthMoment
open Complex MeasureTheory Set Metric Filter Polynomial
open scoped Topology BigOperators ComplexConjugate
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem uCertificateProfile_zero_above {n : ℕ} (hn : 0<n)
    (a : ℝ) {x : ℝ} (hx : a<x) :
    uEndpointProfile uNormalizedBump uCertificateHstar a n x = 0 :=
  uEndpointProfile_zero_above uNormalizedBump (fun _ hx => uNormalizedBump_zero_nonpos hx)
    uCertificateHstar_pos a hn hx

theorem uCertificate_endpoint_geometry {d : TestDatum} (hd : d∈uCertificateRows) :
    0<(d.A:ℝ)/base ∧ (d.A:ℝ)/base≤(d.B:ℝ)/base ∧
      3*((d.A:ℝ)/base)+5*((d.B:ℝ)/base)<2 ∧ d.degree≤4 := by
  have hc := ((mem_uCertificateRows d).mp hd).1
  have htype := ((mem_uCertificateRows d).mp hd).2
  obtain ⟨hA,hAB,hdeg,hrect⟩ := certificate_valid d hc
  simp only [htype] at hrect
  have hbase : (0:ℝ)<(base:ℝ) := by norm_num [base]
  refine ⟨div_pos (by exact_mod_cast hA) hbase,
    div_le_div_of_nonneg_right (by exact_mod_cast hAB) hbase.le,?_,hdeg⟩
  have hr : (3:ℝ)*d.A+5*d.B<2*(base:ℝ) := by exact_mod_cast hrect
  rw [show 3*((d.A:ℝ)/base)+5*((d.B:ℝ)/base) =
    (3*(d.A:ℝ)+5*(d.B:ℝ))/base by ring]
  exact (div_lt_iff₀ hbase).mpr hr

theorem uCertificatePolynomialCoefficients_eq_original {d : TestDatum}
    (hd : d∈uCertificateRows) :
    (fun r : Fin 5 => (manuscriptTestPolynomial d.degree).coeff r.val) =
      (fun r : Fin 5 => (Finite.coef (Finite.cheb d.degree) r.val:ℝ)) := by
  funext r
  exact manuscriptTestPolynomial_coeff_eq_cheb d.degree
    (uCertificate_endpoint_geometry hd).2.2.2 r

def uCertificateRawZetaTest (n : ℕ) (T t : ℝ) : ℂ :=
  (uCertificateRows.map fun d => (d.coefficient:ℂ)*
    rawZetaTest .U T t (manuscriptTestPolynomial d.degree)
      (uEndpointProfile uNormalizedBump uCertificateHstar ((d.A:ℝ)/base) n)
      (uEndpointProfile uNormalizedBump uCertificateHstar ((d.B:ℝ)/base) n)).sum

def uCertificateZetaTest (n : ℕ) (T t : ℝ) : ℂ :=
  phaseProjection (criticalChi t) (uCertificateRawZetaTest n T t)

private theorem u_phaseProjection_list_sum (χ : ℂ) (l : List ℂ) :
    phaseProjection χ l.sum=(l.map (phaseProjection χ)).sum := by
  induction l with
  | nil => simp [phaseProjection]
  | cons x xs ih => simp only [List.sum_cons,List.map_cons,phaseProjection_add,ih]

theorem uCertificateZetaTest_eq_sum (n : ℕ) (T t : ℝ) :
    uCertificateZetaTest n T t=(uCertificateRows.map fun d => (d.coefficient:ℂ)*
      projectedZetaTest .U T t (manuscriptTestPolynomial d.degree)
        (uEndpointProfile uNormalizedBump uCertificateHstar ((d.A:ℝ)/base) n)
        (uEndpointProfile uNormalizedBump uCertificateHstar ((d.B:ℝ)/base) n)).sum := by
  unfold uCertificateZetaTest uCertificateRawZetaTest
  rw [u_phaseProjection_list_sum,List.map_map]
  congr 2
  funext d
  change phaseProjection (criticalChi t) ((d.coefficient:ℂ)*_)=_
  have hc : (d.coefficient:ℂ)=((d.coefficient:ℝ):ℂ) := by norm_cast
  rw [hc,phaseProjection_real_smul]
  rfl

private theorem u_mixed_list_sum (l : List TestDatum) (F : TestDatum→ℂ) (W : ℂ) :
    W*star ((l.map fun d => (d.coefficient:ℂ)*F d).sum)=
      (l.map fun d => (d.coefficient:ℂ)*(W*star (F d))).sum := by
  induction l with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons,List.sum_cons,star_add,star_mul,star_intCast,mul_add]
    rw [ih]
    ring

private theorem u_list_integrable (l : List TestDatum) (f : TestDatum→ℝ→ℂ)
    (hi : ∀ d∈l, Integrable (f d)) : Integrable (fun t => (l.map fun d => f d t).sum) := by
  induction l with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (hi d List.mem_cons_self).add (ih (fun e he => hi e (List.mem_cons_of_mem _ he)))

private theorem u_integral_list_sum (l : List TestDatum) (f : TestDatum→ℝ→ℂ)
    (hi : ∀ d∈l, Integrable (f d)) :
    (∫ t : ℝ, (l.map fun d => f d t).sum)=(l.map fun d => ∫ t : ℝ, f d t).sum := by
  induction l with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [integral_add (hi d List.mem_cons_self)
      (u_list_integrable ds f (fun e he => hi e (List.mem_cons_of_mem _ he)))]
    rw [ih (fun e he => hi e (List.mem_cons_of_mem _ he))]

def uCertificateRawMixedMoment (n : ℕ) (T : ℝ) (Φ : ℝ→ℝ) : ℂ :=
  ∫ t : ℝ, (Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
    star (uCertificateRawZetaTest n T t)

def uCertificateProjectedMixedMoment (n : ℕ) (T : ℝ) (Φ : ℝ→ℝ) : ℂ :=
  ∫ t : ℝ, (Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
    star (uCertificateZetaTest n T t)

theorem uCertificateRawMixedIntegrand_integrable (n : ℕ) (hn : 0<n) {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Integrable (fun t : ℝ => (Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
      star (uCertificateRawZetaTest n T t)) := by
  have hi (d : TestDatum) : Integrable (fun t : ℝ => (d.coefficient:ℂ)*
      ((Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
        star (rawZetaTest .U T t (manuscriptTestPolynomial d.degree)
          (uEndpointProfile uNormalizedBump uCertificateHstar ((d.A:ℝ)/base) n)
          (uEndpointProfile uNormalizedBump uCertificateHstar ((d.B:ℝ)/base) n)))) :=
    (uPolynomialRawMixedIntegrand_integrable hT hL ((d.A:ℝ)/base) ((d.B:ℝ)/base) _ _ _ Φ
      (fun x hx => uCertificateProfile_zero_above hn _ hx)
      (fun x hx => uCertificateProfile_zero_above hn _ hx) hΦ).const_mul _
  exact (u_list_integrable uCertificateRows _ (fun d _ => hi d)).congr
    (Eventually.of_forall (fun t => (u_mixed_list_sum uCertificateRows _ _).symm))

theorem uCertificateRawMixedMoment_eq_sum (n : ℕ) (hn : 0<n) {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    uCertificateRawMixedMoment n T Φ=(uCertificateRows.map fun d => (d.coefficient:ℂ)*
      uPolynomialRawMixedMoment T (manuscriptTestPolynomial d.degree)
        (uEndpointProfile uNormalizedBump uCertificateHstar ((d.A:ℝ)/base) n)
        (uEndpointProfile uNormalizedBump uCertificateHstar ((d.B:ℝ)/base) n) Φ).sum := by
  unfold uCertificateRawMixedMoment uCertificateRawZetaTest
  simp_rw [u_mixed_list_sum]
  rw [u_integral_list_sum _ _ (fun d _ =>
    (uPolynomialRawMixedIntegrand_integrable hT hL ((d.A:ℝ)/base) ((d.B:ℝ)/base) _ _ _ Φ
      (fun x hx => uCertificateProfile_zero_above hn _ hx)
      (fun x hx => uCertificateProfile_zero_above hn _ hx) hΦ).const_mul _)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro d _
  rw [integral_const_mul]
  rfl

private theorem uCertificateProjectedMixedIntegrand_eq_real (n : ℕ) (T t : ℝ) (Φ : ℝ→ℝ) :
    (Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*star (uCertificateZetaTest n T t)=
      Complex.ofReal (((Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
        star (uCertificateRawZetaTest n T t)).re) := by
  rw [mul_assoc]
  unfold uCertificateZetaTest
  rw [zeta_phaseProjection_mixed_re]
  apply Complex.ext
  · simp [Complex.mul_re,Complex.mul_im]
    ring
  · simp [Complex.mul_re,Complex.mul_im]

theorem uCertificateProjectedMixedIntegrand_integrable (n : ℕ) (hn : 0<n) {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Integrable (fun t : ℝ => (Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
      star (uCertificateZetaTest n T t)) :=
  ((uCertificateRawMixedIntegrand_integrable n hn hT hL Φ hΦ).re.ofReal).congr
    (Eventually.of_forall (fun t => (uCertificateProjectedMixedIntegrand_eq_real n T t Φ).symm))

theorem uCertificateProjectedMixedMoment_eq_real (n : ℕ) (hn : 0<n) {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    uCertificateProjectedMixedMoment n T Φ=Complex.ofReal ((uCertificateRawMixedMoment n T Φ).re) := by
  unfold uCertificateProjectedMixedMoment uCertificateRawMixedMoment
  rw [integral_congr_ae (Eventually.of_forall (fun t =>
    uCertificateProjectedMixedIntegrand_eq_real n T t Φ))]
  exact (integral_ofReal (𝕜 := ℂ)).trans
    (congrArg Complex.ofReal (integral_re (uCertificateRawMixedIntegrand_integrable n hn hT hL Φ hΦ)))


theorem uCertificateRawMixedMoment_eq_finiteDifferentialOperators
    (n : ℕ) (hn : 0<n) {T : ℝ} (hT : 1<T) (hL : 16<Real.log T)
    (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    uCertificateRawMixedMoment n T Φ = (uCertificateRows.map fun d =>
      (d.coefficient:ℂ)*finiteDifferentialOperator 4
        (fun r => ((manuscriptTestPolynomial d.degree).coeff r.val:ℂ))
        (uPolynomialMixedGenerator T
          (uEndpointProfile uNormalizedBump uCertificateHstar ((d.A:ℝ)/base) n)
          (uEndpointProfile uNormalizedBump uCertificateHstar ((d.B:ℝ)/base) n) Φ) 0).sum := by
  rw [uCertificateRawMixedMoment_eq_sum n hn hT hL Φ hΦ]
  apply congrArg List.sum
  apply List.map_congr_left
  intro d _
  rw [uPolynomialRawMixedMoment_eq_finiteDifferentialOperator 4 hT hL
    ((d.A:ℝ)/base) ((d.B:ℝ)/base) _ (manuscriptTestPolynomial_natDegree_le_four _)
    _ _ Φ (fun _ hx => uCertificateProfile_zero_above hn _ hx)
    (fun _ hx => uCertificateProfile_zero_above hn _ hx) hΦ]

def certificateActualProfiles (n : ℕ) : TestType → ℝ → ℝ → ℝ
  | .U,a => uEndpointProfile uNormalizedBump uCertificateHstar a n
  | .V,a => vEndpointProfile eta a n

def actual250RawMixedMoment (n : ℕ) (T : ℝ) (Φ : ℝ→ℝ) : ℂ :=
  ∫ t : ℝ, (Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
    star (certificateRawZetaTest (certificateActualProfiles n) T t)

def actual250ProjectedMixedMoment (n : ℕ) (T : ℝ) (Φ : ℝ→ℝ) : ℂ :=
  ∫ t : ℝ, (Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
    star (certificateZetaTest (certificateActualProfiles n) T t)

theorem a05_certificate_complex_filter_sum_partition (f : TestDatum→ℂ) :
    (uCertificateRows.map f).sum+(vCertificateRows.map f).sum=(certificate.map f).sum := by
  have h (l : List TestDatum) :
      ((l.filter (fun d => decide (d.typ=.U))).map f).sum+
        ((l.filter (fun d => decide (d.typ=.V))).map f).sum=(l.map f).sum := by
    induction l with
    | nil => simp
    | cons d ds ih => cases ht : d.typ <;> simp [ht,ih,add_assoc,add_left_comm]
  exact h certificate

theorem certificateActualRawZetaTest_eq_U_add_V (n : ℕ) (T t : ℝ) :
    certificateRawZetaTest (certificateActualProfiles n) T t =
      uCertificateRawZetaTest n T t+vCertificateRawZetaTest n T t := by
  unfold certificateRawZetaTest
  rw [←a05_certificate_complex_filter_sum_partition]
  congr 1

theorem certificateActualZetaTest_eq_U_add_V (n : ℕ) (T t : ℝ) :
    certificateZetaTest (certificateActualProfiles n) T t =
      uCertificateZetaTest n T t+vCertificateZetaTest n T t := by
  unfold certificateZetaTest uCertificateZetaTest vCertificateZetaTest
  rw [certificateActualRawZetaTest_eq_U_add_V,phaseProjection_add]

theorem actual250RawMixedIntegrand_integrable (n : ℕ) (hn : 0<n)
    {T : ℝ} (hT : 1<T) (hL : 16<Real.log T)
    (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Integrable (fun t : ℝ => (Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
      star (certificateRawZetaTest (certificateActualProfiles n) T t)) := by
  simp_rw [certificateActualRawZetaTest_eq_U_add_V,star_add,mul_add]
  exact (uCertificateRawMixedIntegrand_integrable n hn hT hL Φ hΦ).add
    (vCertificateRawMixedIntegrand_integrable n hT hL Φ hΦ)

theorem actual250RawMixedMoment_eq_U_add_V (n : ℕ) (hn : 0<n)
    {T : ℝ} (hT : 1<T) (hL : 16<Real.log T)
    (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    actual250RawMixedMoment n T Φ = uCertificateRawMixedMoment n T Φ+
      vCertificateRawMixedMoment n T Φ := by
  unfold actual250RawMixedMoment uCertificateRawMixedMoment vCertificateRawMixedMoment
  simp_rw [certificateActualRawZetaTest_eq_U_add_V,star_add,mul_add]
  rw [integral_add (uCertificateRawMixedIntegrand_integrable n hn hT hL Φ hΦ)
    (vCertificateRawMixedIntegrand_integrable n hT hL Φ hΦ)]

theorem actual250ProjectedMixedIntegrand_integrable (n : ℕ) (hn : 0<n)
    {T : ℝ} (hT : 1<T) (hL : 16<Real.log T)
    (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Integrable (fun t : ℝ => (Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
      star (certificateZetaTest (certificateActualProfiles n) T t)) := by
  simp_rw [certificateActualZetaTest_eq_U_add_V,star_add,mul_add]
  exact (uCertificateProjectedMixedIntegrand_integrable n hn hT hL Φ hΦ).add
    (vCertificateProjectedMixedIntegrand_integrable n hT hL Φ hΦ)

theorem actual250ProjectedMixedMoment_eq_U_add_V (n : ℕ) (hn : 0<n)
    {T : ℝ} (hT : 1<T) (hL : 16<Real.log T)
    (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    actual250ProjectedMixedMoment n T Φ = uCertificateProjectedMixedMoment n T Φ+
      vCertificateProjectedMixedMoment n T Φ := by
  unfold actual250ProjectedMixedMoment uCertificateProjectedMixedMoment vCertificateProjectedMixedMoment
  simp_rw [certificateActualZetaTest_eq_U_add_V,star_add,mul_add]
  rw [integral_add (uCertificateProjectedMixedIntegrand_integrable n hn hT hL Φ hΦ)
    (vCertificateProjectedMixedIntegrand_integrable n hT hL Φ hΦ)]

theorem actual250ProjectedMixedMoment_eq_real (n : ℕ) (hn : 0<n)
    {T : ℝ} (hT : 1<T) (hL : 16<Real.log T)
    (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    actual250ProjectedMixedMoment n T Φ =
      Complex.ofReal ((actual250RawMixedMoment n T Φ).re) := by
  have hi := actual250RawMixedIntegrand_integrable n hn hT hL Φ hΦ
  unfold actual250ProjectedMixedMoment actual250RawMixedMoment
  have he (t : ℝ) : (Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
      star (certificateZetaTest (certificateActualProfiles n) T t) =
      Complex.ofReal (((Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
        star (certificateRawZetaTest (certificateActualProfiles n) T t)).re) := by
    rw [mul_assoc,certificateZetaTest_mixed_re]
    apply Complex.ext
    · simp [Complex.mul_re,Complex.mul_im]
      ring
    · simp [Complex.mul_re,Complex.mul_im]
  rw [integral_congr_ae (Eventually.of_forall he)]
  exact (integral_ofReal (𝕜 := ℂ)).trans (congrArg Complex.ofReal (integral_re hi))

theorem actual250ProjectedMixedMoment_normalized_eq_real (n : ℕ) (hn : 0<n)
    {T : ℝ} (hT : 1<T) (hL : 16<Real.log T)
    (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    actual250ProjectedMixedMoment n T Φ/((T:ℂ)*(Real.log T:ℂ)^9) =
      Complex.ofReal ((actual250RawMixedMoment n T Φ/((T:ℂ)*(Real.log T:ℂ)^9)).re) := by
  rw [actual250ProjectedMixedMoment_eq_real n hn hT hL Φ hΦ]
  have hden : (T:ℂ)*(Real.log T:ℂ)^9 = Complex.ofReal (T*(Real.log T)^9) := by
    push_cast
    rfl
  rw [hden,Complex.div_ofReal_re,Complex.ofReal_div]

theorem actual250MainTerm_profile_tendsto (Φ : ℝ→ℝ) :
    Tendsto (fun n : ℕ => (arithmeticFactor:ℂ)*(∫ x : ℝ,(Φ x:ℂ))*
      Complex.ofReal (certificateProfileNumerator n)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ,(Φ x:ℂ))*Complex.ofReal (finiteNumerator:ℝ))) :=
  (Complex.continuous_ofReal.continuousAt.tendsto.comp
    certificateProfileNumerator_tendsto).const_mul _

end
end SixthMoment
