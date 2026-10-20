import Sechstmoment.Arithmetic.QuadraticDivisor.WattInput
import Sechstmoment.Numerator.CertificateStatement
import Sechstmoment.Numerator.U.CertificateLimit
import Sechstmoment.Numerator.V.CertificateLimit
import Sechstmoment.Zeta.AFE.Four.Identity


namespace Sechstmoment
open Complex MeasureTheory Filter Source
open scoped Topology
noncomputable section
set_option maxHeartbeats 2000000

theorem actual250RawMixedMoment_fixed_stage_tendsto
    (hSource : DivisorProof.Watt41)
    (n : ℕ) (hn : 0<n)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun T : ℝ => actual250RawMixedMoment n T Φ/
      ((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
        Complex.ofReal (certificateProfileNumerator n))) := by
  have h := (uCertificateRawMixedMoment_fixed_stage_tendsto bblrFixedAFE_proved (separatedQuadraticInput_of_watt41 hSource) n hn Φ hΦ).add
    (Source.noDP_vCertificateRawMixedMoment_fixed_stage_tendsto n hn Φ hΦ)
  have he : (arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*Complex.ofReal (uCertificateProfileNumerator n) +
      (arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*Complex.ofReal (vCertificateBetaKernel n) =
      (arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*Complex.ofReal (certificateProfileNumerator n) := by
    rw [certificateProfileNumerator_eq_U_add_V,Complex.ofReal_add,mul_add]
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16:ℝ))] with T hT hL
  rw [actual250RawMixedMoment_eq_U_add_V n hn hT hL Φ hΦ,add_div]

theorem actual250ProjectedMixedMoment_fixed_stage_tendsto
    (hSource : DivisorProof.Watt41)
    (n : ℕ) (hn : 0<n)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun T : ℝ => actual250ProjectedMixedMoment n T Φ/
      ((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
        Complex.ofReal (certificateProfileNumerator n))) := by
  have h := actual250RawMixedMoment_fixed_stage_tendsto hSource n hn Φ hΦ
  have hr := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (Complex.continuous_re.continuousAt.tendsto.comp h)
  have he : Complex.ofReal (((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
      Complex.ofReal (certificateProfileNumerator n)).re) =
      (arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*Complex.ofReal (certificateProfileNumerator n) := by
    have hI : (∫ x : ℝ, (Φ x:ℂ)) = Complex.ofReal (∫ x : ℝ, Φ x) :=
      integral_ofReal (𝕜 := ℂ)
    rw [hI]
    simp
  rw [he] at hr
  apply hr.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16:ℝ))] with T hT hL
  exact (actual250ProjectedMixedMoment_normalized_eq_real n hn hT hL Φ hΦ).symm

theorem actual250_two_stage_numerator_limit
    (hSource : DivisorProof.Watt41)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    (∀ n : ℕ, 12≤n → Tendsto
      (fun T : ℝ => actual250RawMixedMoment n T Φ/((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*Complex.ofReal (certificateProfileNumerator n)))) ∧
    (∀ n : ℕ, 12≤n → Tendsto
      (fun T : ℝ => actual250ProjectedMixedMoment n T Φ/((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*Complex.ofReal (certificateProfileNumerator n)))) ∧
    Tendsto (fun n : ℕ => (arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
      Complex.ofReal (certificateProfileNumerator n)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*Complex.ofReal (finiteNumerator:ℝ))) := by
  exact ⟨fun n hn => actual250RawMixedMoment_fixed_stage_tendsto hSource n
      (by omega) Φ hΦ,
    fun n hn => actual250ProjectedMixedMoment_fixed_stage_tendsto hSource n
      (by omega) Φ hΦ,
    actual250MainTerm_profile_tendsto Φ⟩

theorem firstRowNumeratorConsumer : FirstRowNumeratorConsumer := by
  intro hSource Φ hΦ
  exact actual250_two_stage_numerator_limit hSource Φ hΦ

end
end Sechstmoment
