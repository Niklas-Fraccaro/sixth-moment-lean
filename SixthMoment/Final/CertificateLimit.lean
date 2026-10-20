import SixthMoment.Denominator.Gram.CertificateAsymptotic
import SixthMoment.Final.DyadicScaling
import SixthMoment.Numerator.CertificateLimit


namespace SixthMoment
open Complex Filter MeasureTheory
open scoped Topology
noncomputable section
set_option maxHeartbeats 1000000

def f01CertificateLowerBound (n : ℕ) (T : ℝ) (Φ : ℝ → ℝ) : ℝ :=
  (‖actual250ProjectedMixedMoment n T Φ‖^2/actual250ProjectedGramMoment n T Φ)/
    f01SixthMomentScale T

theorem f01ActualGram_eventually_pos (n : ℕ) (hn : 12 ≤ n)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (hΦpos : ∀ x, 0 ≤ Φ x)
    (hI : 0 < ∫ x : ℝ, Φ x) (hD : 0 < certificateProfileDenominator n) :
    ∀ᶠ T : ℝ in atTop, 0 < actual250ProjectedGramMoment n T Φ := by
  have ha := arithmeticFactor_wellDefined.2
  have hg := d06ActualCertificateGramAsymptotic_closed Φ hΦ hΦpos n hn
  have hp : 0 < arithmeticFactor*(∫ x : ℝ, Φ x)*certificateProfileDenominator n :=
    mul_pos (mul_pos ha hI) hD
  filter_upwards [(tendsto_order.mp hg).1 0 hp, eventually_gt_atTop (1 : ℝ)] with T h hT
  have hk : 0 < T*(Real.log T)^9 := mul_pos (zero_lt_one.trans hT) (pow_pos (Real.log_pos hT) 9)
  exact (div_pos_iff_of_pos_right hk).mp h

theorem f01CertificateLowerBound_tendsto
    (hSource : DivisorProof.Watt41)
    (n : ℕ) (hn : 12 ≤ n)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (hΦpos : ∀ x, 0 ≤ Φ x)
    (hI : 0 < ∫ x : ℝ, Φ x) (hD : 0 < certificateProfileDenominator n) :
    Tendsto (fun T : ℝ => f01CertificateLowerBound n T Φ) atTop
      (𝓝 ((∫ x : ℝ, Φ x)*(362880 * certificateProfileNumerator n ^ 2 / certificateProfileDenominator n))) := by
  have ha := arithmeticFactor_wellDefined.2
  have hm := actual250ProjectedMixedMoment_fixed_stage_tendsto hSource n
    (by omega) Φ hΦ
  have hΦIntegral : (∫ x : ℝ, (Φ x : ℂ)) = Complex.ofReal (∫ x : ℝ, Φ x) :=
    integral_ofReal (𝕜 := ℂ)
  have hmc : Tendsto (fun T : ℝ => actual250ProjectedMixedMoment n T Φ/
      ((T : ℂ)*(Real.log T : ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor*(∫ x : ℝ, Φ x)*certificateProfileNumerator n : ℝ) : ℂ)) := by
    simpa only [hΦIntegral, Complex.ofReal_mul] using hm
  have hms := hmc.norm.pow 2
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hms
  have hg := d06ActualCertificateGramAsymptotic_closed Φ hΦ hΦpos n hn
  have hden : arithmeticFactor*(∫ x : ℝ, Φ x)*certificateProfileDenominator n ≠ 0 :=
    (mul_pos (mul_pos ha hI) hD).ne'
  have hl := (hms.div hg hden).const_mul ((Nat.factorial 9 : ℝ)/arithmeticFactor)
  have he : ((Nat.factorial 9 : ℝ)/arithmeticFactor)*
      ((arithmeticFactor*(∫ x : ℝ, Φ x)*certificateProfileNumerator n)^2/
        (arithmeticFactor*(∫ x : ℝ, Φ x)*certificateProfileDenominator n)) =
      (∫ x : ℝ, Φ x)*(362880 * certificateProfileNumerator n ^ 2 / certificateProfileDenominator n) := by
    norm_num [Nat.factorial]
    field_simp [ha.ne', hI.ne', hD.ne']
  rw [he] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    f01ActualGram_eventually_pos n hn Φ hΦ hΦpos hI hD] with T hT hG
  have hk : 0 < T*(Real.log T)^9 := mul_pos (zero_lt_one.trans hT) (pow_pos (Real.log_pos hT) 9)
  have hnorm : ‖((T : ℂ)*(Real.log T : ℂ)^9)‖ = T*(Real.log T)^9 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_of_nonneg hk.le]
  simp only [Pi.div_apply, f01CertificateLowerBound, f01SixthMomentScale, norm_div, hnorm, div_pow]
  field_simp [ha.ne', hG.ne', hk.ne', (Real.log_pos hT).ne', (zero_lt_one.trans hT).ne']

end
end SixthMoment
