import SixthMoment.Numerator.U.CertificateMoments
import SixthMoment.Numerator.U.MomentLimit
import SixthMoment.Numerator.U.RegularProfileOperator


namespace SixthMoment
open Complex MeasureTheory Filter Polynomial Source
open scoped Topology
noncomputable section
set_option maxHeartbeats 2000000

theorem uPolynomialRawMixedMoment_normalized_profile_limit
    (hAFE : BBLRv1FixedApproximateFEInput) (hSource : SeparatedQuadraticInput)
    {a b : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2)
    (p : ℝ[X]) (hp : p.natDegree≤4) (f g Φ : ℝ → ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun T : ℝ => uPolynomialRawMixedMoment T p f g Φ /
      ((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
        Complex.ofReal (∫ A : ℝ, ∫ B : ℝ, f A*g B*
          numeratorPointKernel (fun r : Fin 5 => p.coeff r.val) A B))) := by
  have h := uPolynomialRawMixedMoment_normalized_regular_limit
    hAFE hSource ha hab hlen p hp f g Φ hf hg hΦ
  rw [actualCenteredNumeratorProfileGenerator_operator_eq_globalPointKernel
    (fun r => p.coeff r.val) a b f g Φ hf hg] at h
  exact h

theorem uCertificate_row_fixed_stage_tendsto
    (hAFE : BBLRv1FixedApproximateFEInput) (hSource : SeparatedQuadraticInput)
    (d : TestDatum) (hd : d∈uCertificateRows) (n : ℕ) (hn : 0<n)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun T : ℝ => uPolynomialRawMixedMoment T (manuscriptTestPolynomial d.degree)
      (uEndpointProfile uNormalizedBump uCertificateHstar ((d.A:ℝ)/base) n)
      (uEndpointProfile uNormalizedBump uCertificateHstar ((d.B:ℝ)/base) n) Φ /
      ((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*Complex.ofReal
        (∫ A : ℝ, ∫ B : ℝ,
          uEndpointProfile uNormalizedBump uCertificateHstar ((d.A:ℝ)/base) n A*
          uEndpointProfile uNormalizedBump uCertificateHstar ((d.B:ℝ)/base) n B*
          numeratorPointKernel (fun r => (Finite.coef (Finite.cheb d.degree) r.val:ℝ)) A B))) := by
  obtain ⟨ha,hab,hlen,_⟩ := uCertificate_endpoint_geometry hd
  obtain ⟨hf,hg⟩ := certificate_uProfile_admissible ((mem_uCertificateRows d).mp hd).1 hn
  have h := uPolynomialRawMixedMoment_normalized_profile_limit hAFE hSource ha.le hab hlen
    (manuscriptTestPolynomial d.degree) (manuscriptTestPolynomial_natDegree_le_four d.degree)
    _ _ Φ hf hg hΦ
  rw [uCertificatePolynomialCoefficients_eq_original hd] at h
  exact h

private theorem u_numerator_list_sum_div (l : List TestDatum) (f : TestDatum → ℂ) (b : ℂ) :
    (l.map f).sum/b = (l.map fun d => f d/b).sum := by
  induction l with
  | nil => simp
  | cons d ds ih => simp only [List.map_cons,List.sum_cons,add_div,ih]

private theorem u_numerator_weighted_complex_list_sum
    (l : List TestDatum) (c : ℂ) (f : TestDatum → ℝ) :
    (l.map fun d => (d.coefficient:ℂ)*(c*Complex.ofReal (f d))).sum =
      c*Complex.ofReal ((l.map fun d => (d.coefficient:ℝ)*f d).sum) := by
  induction l with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons,List.sum_cons,ih,Complex.ofReal_add,Complex.ofReal_mul]
    have hc : (d.coefficient:ℂ) = ((d.coefficient:ℝ):ℂ) := by norm_cast
    rw [hc]
    ring

theorem uCertificateRawMixedMoment_fixed_stage_tendsto
    (hAFE : BBLRv1FixedApproximateFEInput) (hSource : SeparatedQuadraticInput)
    (n : ℕ) (hn : 0<n) (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun T : ℝ => uCertificateRawMixedMoment n T Φ /
      ((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
        Complex.ofReal (uCertificateProfileNumerator n))) := by
  have h := tendsto_list_sum uCertificateRows (fun d hd =>
    (uCertificate_row_fixed_stage_tendsto hAFE hSource d hd n hn Φ hΦ).const_mul
      (d.coefficient:ℂ))
  rw [u_numerator_weighted_complex_list_sum] at h
  change Tendsto _ _ (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
    Complex.ofReal (uCertificateProfileNumerator n))) at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16:ℝ))] with T hT hL
  rw [uCertificateRawMixedMoment_eq_sum n hn hT hL Φ hΦ,u_numerator_list_sum_div]
  apply congrArg List.sum
  apply List.map_congr_left
  intro d _
  ring

theorem uCertificateProjectedMixedMoment_normalized_eq_real
    (n : ℕ) (hn : 0<n) {T : ℝ} (hT : 1<T) (hL : 16<Real.log T)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    uCertificateProjectedMixedMoment n T Φ/((T:ℂ)*(Real.log T:ℂ)^9) =
      Complex.ofReal ((uCertificateRawMixedMoment n T Φ/
        ((T:ℂ)*(Real.log T:ℂ)^9)).re) := by
  rw [uCertificateProjectedMixedMoment_eq_real n hn hT hL Φ hΦ]
  have hden : (T:ℂ)*(Real.log T:ℂ)^9 = Complex.ofReal (T*(Real.log T)^9) := by
    push_cast
    rfl
  rw [hden,Complex.div_ofReal_re,Complex.ofReal_div]

theorem uCertificateProjectedMixedMoment_fixed_stage_tendsto
    (hAFE : BBLRv1FixedApproximateFEInput) (hSource : SeparatedQuadraticInput)
    (n : ℕ) (hn : 0<n) (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun T : ℝ => uCertificateProjectedMixedMoment n T Φ /
      ((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
        Complex.ofReal (uCertificateProfileNumerator n))) := by
  have h := uCertificateRawMixedMoment_fixed_stage_tendsto hAFE hSource n hn Φ hΦ
  have hr := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (Complex.continuous_re.continuousAt.tendsto.comp h)
  have he : Complex.ofReal (((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
      Complex.ofReal (uCertificateProfileNumerator n)).re) =
      (arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*Complex.ofReal (uCertificateProfileNumerator n) := by
    have hI : (∫ x : ℝ, (Φ x:ℂ)) = Complex.ofReal (∫ x : ℝ, Φ x) :=
      integral_ofReal (𝕜 := ℂ)
    rw [hI]
    simp
  rw [he] at hr
  apply hr.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16:ℝ))] with T hT hL
  exact (uCertificateProjectedMixedMoment_normalized_eq_real n hn hT hL Φ hΦ).symm

theorem uCertificate_two_stage_numerator_limit
    (hAFE : BBLRv1FixedApproximateFEInput) (hSource : SeparatedQuadraticInput)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    (∀ n : ℕ, 12≤n → Tendsto
      (fun T : ℝ => uCertificateRawMixedMoment n T Φ/((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*Complex.ofReal (uCertificateProfileNumerator n)))) ∧
    (∀ n : ℕ, 12≤n → Tendsto
      (fun T : ℝ => uCertificateProjectedMixedMoment n T Φ/((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*Complex.ofReal (uCertificateProfileNumerator n)))) ∧
    Tendsto (fun n : ℕ => (arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
      Complex.ofReal (uCertificateProfileNumerator n)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*Complex.ofReal uCertificatePointNumerator)) := by
  refine ⟨fun n hn => uCertificateRawMixedMoment_fixed_stage_tendsto hAFE hSource n
      (by omega) Φ hΦ,
    fun n hn => uCertificateProjectedMixedMoment_fixed_stage_tendsto hAFE hSource n
      (by omega) Φ hΦ,?_⟩
  exact (Complex.continuous_ofReal.continuousAt.tendsto.comp
    uCertificateProfileNumerator_tendsto).const_mul _

end
end SixthMoment
