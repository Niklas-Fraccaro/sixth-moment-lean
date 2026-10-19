import Sechstmoment.Certificate.Profiles.V.Numerator
import Sechstmoment.Numerator.V.PolynomialMoment

/-! The original thirty V rows, with their actual beta profiles and fixed
stage limits, derived from the independent moment evaluation. -/

namespace Sechstmoment
open Complex MeasureTheory Set Metric Filter Polynomial
open scoped Topology BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

private theorem noDP_beta_weightedPointKernel_eq (d : TestDatum) (n : ℕ) :
    weightedNumeratorPointKernel (vCertificatePolynomialCoefficients d) eta
      (betaProfilePolynomial eta n (betaProfileIndex eta ((d.A:ℝ)/base) n))
      (betaProfilePolynomial eta n (betaProfileIndex eta ((d.B:ℝ)/base) n)) =
    ∫ x in (0:ℝ)..eta, ∫ y in (0:ℝ)..eta,
      betaScaledProfile eta n (betaProfileIndex eta ((d.A:ℝ)/base) n) x*
      betaScaledProfile eta n (betaProfileIndex eta ((d.B:ℝ)/base) n) y*
      numeratorPointKernel (vCertificatePolynomialCoefficients d) x (1-y) := by
  unfold weightedNumeratorPointKernel polynomialIntervalProfile
  simp_rw [← betaScaledProfile_eq_polynomial_eval]

private theorem noDP_list_sum_div (l : List TestDatum) (f : TestDatum → ℂ) (b : ℂ) :
    (l.map f).sum/b = (l.map fun d => f d/b).sum := by
  induction l with
  | nil => simp
  | cons d ds ih => simp only [List.map_cons,List.sum_cons,add_div,ih]

private theorem noDP_weighted_complex_list_sum (l : List TestDatum) (c : ℂ) (f : TestDatum → ℝ) :
    (l.map fun d => (d.coefficient:ℂ)*(c*Complex.ofReal (f d))).sum =
      c*Complex.ofReal ((l.map fun d => (d.coefficient:ℝ)*f d).sum) := by
  induction l with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons,List.sum_cons,ih,Complex.ofReal_add,Complex.ofReal_mul]
    have hc : (d.coefficient:ℂ) = ((d.coefficient:ℝ):ℂ) := by norm_cast
    rw [hc]
    ring

namespace Source

private theorem noDP_v_certificate_row_fixed_stage_tendsto
    (d : TestDatum) (hd : d ∈ vCertificateRows) (n : ℕ) (hn : 0 < n)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun T : ℝ => vPolynomialRawMixedMoment T (manuscriptTestPolynomial d.degree)
      (vEndpointProfile eta ((d.A:ℝ)/base) n)
      (vEndpointProfile eta ((d.B:ℝ)/base) n) Φ/((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*Complex.ofReal
        (∫ x in (0:ℝ)..eta, ∫ y in (0:ℝ)..eta,
          betaScaledProfile eta n (betaProfileIndex eta ((d.A:ℝ)/base) n) x*
          betaScaledProfile eta n (betaProfileIndex eta ((d.B:ℝ)/base) n) y*
          numeratorPointKernel (vCertificatePolynomialCoefficients d) x (1-y)))) := by
  obtain ⟨ha,haη,hb,hbη,_⟩ := vCertificate_endpoint_geometry hd
  have ht := noDP_vPolynomialRawMixedMoment_tendsto 4 eta_pos eta_lt_quarter
    (betaProfilePolynomial eta n (betaProfileIndex eta ((d.A:ℝ)/base) n))
    (betaProfilePolynomial eta n (betaProfileIndex eta ((d.B:ℝ)/base) n))
    (manuscriptTestPolynomial d.degree) (manuscriptTestPolynomial_natDegree_le_four d.degree) Φ hΦ
  rw [← vEndpointProfile_eq_polynomialProfile eta_pos ha.le haη hn,
    ← vEndpointProfile_eq_polynomialProfile eta_pos hb.le hbη hn] at ht
  change Tendsto _ _ (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
    finiteDifferentialOperator 4 (fun r => (vCertificatePolynomialCoefficients d r:ℂ))
      (vReflectedPolynomialJ eta
        (betaProfilePolynomial eta n (betaProfileIndex eta ((d.A:ℝ)/base) n))
        (betaProfilePolynomial eta n (betaProfileIndex eta ((d.B:ℝ)/base) n))) 0)) at ht
  rw [vReflectedPolynomialJ_operator_eq_weightedNumerator _ eta eta_pos eta_lt_quarter,
    noDP_beta_weightedPointKernel_eq] at ht
  exact ht

theorem noDP_vCertificateRawMixedMoment_fixed_stage_tendsto
    (n : ℕ) (hn : 0 < n) (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun T : ℝ => vCertificateRawMixedMoment n T Φ/((T:ℂ)*(Real.log T:ℂ)^9))
      atTop (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*Complex.ofReal (vCertificateBetaKernel n))) := by
  have ht := tendsto_list_sum vCertificateRows (fun d hd =>
    (noDP_v_certificate_row_fixed_stage_tendsto d hd n hn Φ hΦ).const_mul (d.coefficient:ℂ))
  rw [noDP_weighted_complex_list_sum] at ht
  change Tendsto _ _ (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
    Complex.ofReal (vCertificateBetaKernel n))) at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16:ℝ))] with T hT hL
  rw [vCertificateRawMixedMoment_eq_sum n hT hL Φ hΦ,noDP_list_sum_div]
  apply congrArg List.sum
  apply List.map_congr_left
  intro d _
  ring

theorem noDP_vCertificateProjectedMixedMoment_fixed_stage_tendsto
    (n : ℕ) (hn : 0 < n) (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun T : ℝ => vCertificateProjectedMixedMoment n T Φ/((T:ℂ)*(Real.log T:ℂ)^9))
      atTop (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*Complex.ofReal (vCertificateBetaKernel n))) := by
  have ht := noDP_vCertificateRawMixedMoment_fixed_stage_tendsto n hn Φ hΦ
  have hr := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (Complex.continuous_re.continuousAt.tendsto.comp ht)
  have he : Complex.ofReal (((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
      Complex.ofReal (vCertificateBetaKernel n)).re) =
      (arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*Complex.ofReal (vCertificateBetaKernel n) := by
    have hI : (∫ x : ℝ, (Φ x:ℂ)) = Complex.ofReal (∫ x : ℝ, Φ x) := integral_ofReal (𝕜 := ℂ)
    rw [hI]
    simp
  rw [he] at hr
  apply hr.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16:ℝ))] with T hT hL
  exact (vCertificateProjectedMixedMoment_normalized_eq_real n hT hL Φ hΦ).symm

end Source
end
end Sechstmoment
