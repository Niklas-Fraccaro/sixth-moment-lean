import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import SixthMoment.Analysis.Integration.CauchySchwarz
import SixthMoment.Numerator.U.CertificateMoments


namespace SixthMoment
open Complex MeasureTheory Set Polynomial
open scoped Topology ComplexConjugate
noncomputable section

theorem riemannZeta_criticalLine_continuous :
    Continuous (fun t : ℝ => riemannZeta (criticalLinePoint t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (analyticOn_riemannZeta _ (by simpa using criticalLinePoint_ne_one t)).continuousAt.comp
    (by unfold criticalLinePoint; fun_prop)

theorem centeredZetaDerivative_criticalLine_continuous (T : ℝ) (m : ℕ) :
    Continuous (fun t : ℝ => centeredZetaDerivative T m (criticalLinePoint t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (centeredZetaDerivative_analyticAt T m _ (criticalLinePoint_ne_one t)).continuousAt.comp
    (by unfold criticalLinePoint; fun_prop)

theorem zetaCp_continuous (T : ℝ) (p : ℝ[X]) :
    Continuous (fun t : ℝ => zetaCp T t p) := by
  unfold zetaCp zetaPolynomialDerivative Polynomial.sum
  apply continuous_finsetSum
  intro m _
  exact continuous_const.mul (centeredZetaDerivative_criticalLine_continuous T m)

theorem rawZetaTest_continuous (τ : TestType) {T : ℝ} (hT : 1<T)
    (a b : ℝ) (p : ℝ[X]) (f g : ℝ → ℝ)
    (hf : ∀ x, a<x → f x=0) (hg : ∀ x, b<x → g x=0) :
    Continuous (fun t : ℝ => rawZetaTest τ T t p f g) := by
  have hs : Continuous criticalLinePoint := by unfold criticalLinePoint; fun_prop
  have hsm : Continuous (fun t : ℝ => 1-criticalLinePoint t) := continuous_const.sub hs
  cases τ with
  | U =>
    exact ((criticalChi_continuous.mul (zetaCp_continuous T p)).mul
      ((profileDirichletSum_continuous hT a f hf).comp hs)).mul
        ((profileDirichletSum_continuous hT b g hg).comp hsm)
  | V =>
    exact ((zetaCp_continuous T p).mul
      ((profileDirichletSum_continuous hT a f hf).comp hs)).mul
        ((profileDirichletSum_continuous hT b g hg).comp hs)

theorem certificateActualProfiles_zero_above (n : ℕ) (hn : 0<n)
    (τ : TestType) (a : ℝ) :
    ∀ x, max a eta<x → certificateActualProfiles n τ a x=0 := by
  intro x hx
  cases τ with
  | U => exact uCertificateProfile_zero_above hn a ((le_max_left a eta).trans_lt hx)
  | V => exact vEndpointProfile_zero_above eta a n ((le_max_right a eta).trans_lt hx)

theorem certificateActualRawZetaTest_continuous (n : ℕ) (hn : 0<n)
    {T : ℝ} (hT : 1<T) :
    Continuous (certificateRawZetaTest (certificateActualProfiles n) T) := by
  unfold certificateRawZetaTest
  apply continuous_list_sum
  intro d _
  exact continuous_const.mul (rawZetaTest_continuous d.typ hT
    (max ((d.A:ℝ)/base) eta) (max ((d.B:ℝ)/base) eta) _ _ _
    (certificateActualProfiles_zero_above n hn d.typ _)
    (certificateActualProfiles_zero_above n hn d.typ _))

theorem certificateActualZetaTest_continuous (n : ℕ) (hn : 0<n)
    {T : ℝ} (hT : 1<T) :
    Continuous (certificateZetaTest (certificateActualProfiles n) T) := by
  unfold certificateZetaTest phaseProjection
  have hF := certificateActualRawZetaTest_continuous n hn hT
  exact (hF.add ((criticalChi_continuous.pow 3).mul hF.star)).div_const 2

theorem integral_cauchy_schwarz_of_memLp (F G : ℝ → ℂ)
    (hF : MemLp F 2) (hG : MemLp G 2) :
    ‖∫ t : ℝ, star (G t)*F t‖^2 ≤
      (∫ t : ℝ, ‖F t‖^2)*(∫ t : ℝ, ‖G t‖^2) := by
  have h := integral_cauchy_schwarz (hG.toLp G) (hF.toLp F)
  have hm : (∫ t : ℝ, star ((hG.toLp G) t)*(hF.toLp F) t) =
      ∫ t : ℝ, star (G t)*F t := by
    apply integral_congr_ae
    filter_upwards [hG.coeFn_toLp,hF.coeFn_toLp] with t htG htF
    rw [htG,htF]
  have hnF : (∫ t : ℝ, ‖(hF.toLp F) t‖^2) = ∫ t : ℝ, ‖F t‖^2 := by
    apply integral_congr_ae
    filter_upwards [hF.coeFn_toLp] with t ht
    rw [ht]
  have hnG : (∫ t : ℝ, ‖(hG.toLp G) t‖^2) = ∫ t : ℝ, ‖G t‖^2 := by
    apply integral_congr_ae
    filter_upwards [hG.coeFn_toLp] with t ht
    rw [ht]
  rw [hm,hnG,hnF] at h
  simpa only [mul_comm] using h

def dyadicWeightedL2Amplitude (T : ℝ) (Φ : ℝ → ℝ) (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Real.sqrt (Φ (t/T)):ℂ)*F t

theorem dyadicWeightedL2Amplitude_continuous (T : ℝ) (Φ : ℝ → ℝ) (F : ℝ → ℂ)
    (hΦ : Continuous Φ) (hF : Continuous F) :
    Continuous (dyadicWeightedL2Amplitude T Φ F) := by
  unfold dyadicWeightedL2Amplitude
  fun_prop

theorem dyadicWeightedL2Amplitude_hasCompactSupport {T : ℝ} (hT : 0<T)
    (Φ : ℝ → ℝ) (F : ℝ → ℂ) (hΦ : tsupport Φ ⊆ Icc 1 2) :
    HasCompactSupport (dyadicWeightedL2Amplitude T Φ F) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Icc T (2*T)))
  intro t ht
  by_contra hout
  have hx : t/T ∉ Icc (1:ℝ) 2 := by
    intro hx
    apply hout
    constructor
    · have h := (le_div_iff₀ hT).mp hx.1
      linarith
    · have h := (div_le_iff₀ hT).mp hx.2
      linarith
  have hz : Φ (t/T)=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hΦ h))
  simp [Function.mem_support,dyadicWeightedL2Amplitude,hz] at ht

theorem dyadicWeightedL2Amplitude_memLp {T : ℝ} (hT : 0<T)
    (Φ : ℝ → ℝ) (F : ℝ → ℂ) (hΦ : SmoothDyadicWeight Φ) (hF : Continuous F) :
    MemLp (dyadicWeightedL2Amplitude T Φ F) 2 :=
  (dyadicWeightedL2Amplitude_continuous T Φ F hΦ.1.continuous hF).memLp_of_hasCompactSupport
    (dyadicWeightedL2Amplitude_hasCompactSupport hT Φ F hΦ.2)

theorem dyadicWeightedL2Amplitude_norm_sq (T : ℝ) (Φ : ℝ → ℝ) (F : ℝ → ℂ)
    (hΦ : ∀ x, 0≤Φ x) (t : ℝ) :
    ‖dyadicWeightedL2Amplitude T Φ F t‖^2 = Φ (t/T)*‖F t‖^2 := by
  simp [dyadicWeightedL2Amplitude,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt (hΦ _)]

theorem weighted_norm_sq_integrable {T : ℝ} (hT : 0<T)
    (Φ : ℝ → ℝ) (F : ℝ → ℂ) (hΦ : SmoothDyadicWeight Φ)
    (hΦpos : ∀ x, 0≤Φ x) (hF : Continuous F) :
    Integrable (fun t : ℝ => Φ (t/T)*‖F t‖^2) := by
  have hm := dyadicWeightedL2Amplitude_memLp hT Φ F hΦ hF
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  simpa only [dyadicWeightedL2Amplitude_norm_sq T Φ F hΦpos] using hi

theorem dyadic_weighted_cauchy_schwarz {T : ℝ} (hT : 0<T)
    (Φ : ℝ → ℝ) (F G : ℝ → ℂ) (hΦ : SmoothDyadicWeight Φ)
    (hΦpos : ∀ x, 0≤Φ x) (hF : Continuous F) (hG : Continuous G) :
    ‖∫ t : ℝ, (Φ (t/T):ℂ)*F t*star (G t)‖^2 ≤
      (∫ t : ℝ, Φ (t/T)*‖F t‖^2)*(∫ t : ℝ, Φ (t/T)*‖G t‖^2) := by
  have h := integral_cauchy_schwarz_of_memLp
    (dyadicWeightedL2Amplitude T Φ F) (dyadicWeightedL2Amplitude T Φ G)
    (dyadicWeightedL2Amplitude_memLp hT Φ F hΦ hF)
    (dyadicWeightedL2Amplitude_memLp hT Φ G hΦ hG)
  have he (t : ℝ) : star (dyadicWeightedL2Amplitude T Φ G t)*
      dyadicWeightedL2Amplitude T Φ F t = (Φ (t/T):ℂ)*F t*star (G t) := by
    simp only [dyadicWeightedL2Amplitude,star_mul,Complex.star_def,conj_ofReal]
    calc
      _ = ((Real.sqrt (Φ (t/T)):ℂ)^2)*F t*conj (G t) := by ring
      _ = _ := by rw [← Complex.ofReal_pow,Real.sq_sqrt (hΦpos _)]
  simp_rw [he,dyadicWeightedL2Amplitude_norm_sq T Φ F hΦpos,
    dyadicWeightedL2Amplitude_norm_sq T Φ G hΦpos] at h
  exact h

def actualDyadicSixthMoment (T : ℝ) (Φ : ℝ → ℝ) : ℝ :=
  ∫ t : ℝ, Φ (t/T)*‖riemannZeta (criticalLinePoint t)‖^6

def actual250ProjectedGramMoment (n : ℕ) (T : ℝ) (Φ : ℝ → ℝ) : ℝ :=
  ∫ t : ℝ, Φ (t/T)*‖certificateZetaTest (certificateActualProfiles n) T t‖^2

theorem actualDyadicSixthMoment_integrable {T : ℝ} (hT : 0<T)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (hΦpos : ∀ x, 0≤Φ x) :
    Integrable (fun t : ℝ => Φ (t/T)*‖riemannZeta (criticalLinePoint t)‖^6) := by
  have h := weighted_norm_sq_integrable hT Φ
    (fun t => riemannZeta (criticalLinePoint t)^3) hΦ hΦpos
    (riemannZeta_criticalLine_continuous.pow 3)
  simpa only [norm_pow,← pow_mul] using h

theorem actual250ProjectedGramMoment_integrable (n : ℕ) (hn : 0<n)
    {T : ℝ} (hT : 1<T) (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ)
    (hΦpos : ∀ x, 0≤Φ x) :
    Integrable (fun t : ℝ => Φ (t/T)*
      ‖certificateZetaTest (certificateActualProfiles n) T t‖^2) :=
  weighted_norm_sq_integrable (zero_lt_one.trans hT) Φ _ hΦ hΦpos
    (certificateActualZetaTest_continuous n hn hT)

theorem actual250ProjectedMixedMoment_cauchy_schwarz (n : ℕ) (hn : 0<n)
    {T : ℝ} (hT : 1<T) (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ)
    (hΦpos : ∀ x, 0≤Φ x) :
    ‖actual250ProjectedMixedMoment n T Φ‖^2 ≤
      actualDyadicSixthMoment T Φ*actual250ProjectedGramMoment n T Φ := by
  have h := dyadic_weighted_cauchy_schwarz (zero_lt_one.trans hT) Φ
    (fun t => riemannZeta (criticalLinePoint t)^3)
    (certificateZetaTest (certificateActualProfiles n) T) hΦ hΦpos
    (riemannZeta_criticalLine_continuous.pow 3)
    (certificateActualZetaTest_continuous n hn hT)
  simpa only [actual250ProjectedMixedMoment,actualDyadicSixthMoment,
    actual250ProjectedGramMoment,norm_pow,← pow_mul] using h

theorem actualDyadicSixthMoment_nonneg (T : ℝ) (Φ : ℝ → ℝ)
    (hΦpos : ∀ x, 0≤Φ x) : 0≤actualDyadicSixthMoment T Φ :=
  integral_nonneg (fun _t => mul_nonneg (hΦpos _) (by positivity))

theorem actual250ProjectedGramMoment_nonneg (n : ℕ) (T : ℝ) (Φ : ℝ → ℝ)
    (hΦpos : ∀ x, 0≤Φ x) : 0≤actual250ProjectedGramMoment n T Φ :=
  integral_nonneg (fun _t => mul_nonneg (hΦpos _) (sq_nonneg _))

theorem actual250ProjectedGramMoment_pos_of_mixed_ne_zero (n : ℕ) (hn : 0<n)
    {T : ℝ} (hT : 1<T) (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ)
    (hΦpos : ∀ x, 0≤Φ x) (hm : actual250ProjectedMixedMoment n T Φ≠0) :
    0<actual250ProjectedGramMoment n T Φ := by
  by_contra! hg
  have hz := le_antisymm hg (actual250ProjectedGramMoment_nonneg n T Φ hΦpos)
  have hc := actual250ProjectedMixedMoment_cauchy_schwarz n hn hT Φ hΦ hΦpos
  rw [hz,mul_zero] at hc
  exact (not_le_of_gt (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hm))) hc

theorem actual250ProjectedMixedMoment_quotient_lower_bound (n : ℕ) (hn : 0<n)
    {T : ℝ} (hT : 1<T) (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ)
    (hΦpos : ∀ x, 0≤Φ x) (hg : 0<actual250ProjectedGramMoment n T Φ) :
    ‖actual250ProjectedMixedMoment n T Φ‖^2/actual250ProjectedGramMoment n T Φ ≤
      actualDyadicSixthMoment T Φ :=
  (div_le_iff₀ hg).mpr
    (actual250ProjectedMixedMoment_cauchy_schwarz n hn hT Φ hΦ hΦpos)

end
end SixthMoment
