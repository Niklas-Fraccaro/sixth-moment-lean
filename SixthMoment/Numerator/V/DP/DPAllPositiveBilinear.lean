import SixthMoment.Numerator.Polar.General.BilinearDP
import SixthMoment.Numerator.V.DP.DPAllPositiveCoincidence


namespace SixthMoment
open Complex MeasureTheory Set Filter
open scoped Topology BigOperators

set_option maxHeartbeats 1000000
noncomputable section

theorem allPositiveFourthProduct_continuous (α : MomentShifts)
    (hα : α ∈ momentRawShiftDomain) :
    Continuous (fun t : ℝ => allPositiveFourthProduct t α) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have h := (allPositiveFourthExtended_contDiffAt α t hα).continuousAt.comp
    (f := fun t : ℝ => (α,(t:ℂ))) (x := t) (by fun_prop)
  exact h

theorem allPositiveRawIntegrand_continuous {T : ℝ} (hT : 1 < T)
    (a b : ℝ) (α : MomentShifts) (f g Φ : ℝ → ℝ)
    (hα : α ∈ momentRawShiftDomain)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, b < x → g x=0)
    (hΦ : Continuous Φ) :
    Continuous (fun t => allPositiveRawIntegrand T t α f g Φ) := by
  have h := (allPositiveAmplitude_continuous hT a b f g Φ hf hg hΦ).mul
    (allPositiveFourthProduct_continuous α hα)
  apply h.congr
  intro t
  change allPositiveAmplitude T f g Φ t*allPositiveFourthProduct t α =
    allPositiveRawIntegrand T t α f g Φ
  unfold allPositiveRawIntegrand allPositiveAmplitude
  ring

theorem allPositiveRawIntegrand_hasCompactSupport {T : ℝ} (hT : 0 < T)
    (α : MomentShifts) (f g Φ : ℝ → ℝ) (hΦ : tsupport Φ ⊆ Icc 1 2) :
    HasCompactSupport (fun t => allPositiveRawIntegrand T t α f g Φ) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Icc T (2*T)))
  intro t ht
  by_contra hout
  have hx : t/T ∉ Icc (1 : ℝ) 2 := by
    intro hx
    apply hout
    constructor
    · have h := (le_div_iff₀ hT).mp hx.1
      linarith
    · have h := (div_le_iff₀ hT).mp hx.2
      linarith
  have hzero : Φ (t/T)=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hΦ h))
  simp [Function.mem_support,allPositiveRawIntegrand,hzero] at ht

theorem allPositiveRawIntegrand_integrable {T : ℝ} (hT : 1 < T)
    (a b : ℝ) (α : MomentShifts) (f g Φ : ℝ → ℝ)
    (hα : α ∈ momentRawShiftDomain)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, b < x → g x=0)
    (hΦ : SmoothDyadicWeight Φ) :
    Integrable (fun t => allPositiveRawIntegrand T t α f g Φ) :=
  (allPositiveRawIntegrand_continuous hT a b α f g Φ hα hf hg hΦ.1.continuous).integrable_of_hasCompactSupport
      (allPositiveRawIntegrand_hasCompactSupport (zero_lt_one.trans hT) α f g Φ hΦ.2)

theorem allPositiveRawIntegrand_polarization {T : ℝ} (hT : 1 < T)
    (a t : ℝ) (α : MomentShifts) (f g Φ : ℝ → ℝ)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, a < x → g x=0) :
    allPositiveRawIntegrand T t α f g Φ =
      (1/4:ℂ)*(allPositiveRawIntegrand T t α (f+g) (f+g) Φ-
        allPositiveRawIntegrand T t α (f-g) (f-g) Φ) := by
  simp only [allPositiveRawIntegrand,
    profileDirichletSum_add hT a f g hf hg,profileDirichletSum_sub hT a f g hf hg]
  ring

theorem allPositiveRawMoment_polarization {T : ℝ} (hT : 1 < T)
    (a : ℝ) (α : MomentShifts) (f g Φ : ℝ → ℝ)
    (hα : α ∈ momentRawShiftDomain)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, a < x → g x=0)
    (hΦ : SmoothDyadicWeight Φ) :
    allPositiveRawMoment T α f g Φ =
      (1/4:ℂ)*(allPositiveRawMoment T α (f+g) (f+g) Φ-
        allPositiveRawMoment T α (f-g) (f-g) Φ) := by
  have hadd : ∀ x, a < x → (f+g) x=0 := by intro x hx; simp [hf x hx,hg x hx]
  have hsub : ∀ x, a < x → (f-g) x=0 := by intro x hx; simp [hf x hx,hg x hx]
  have hip := allPositiveRawIntegrand_integrable hT a a α (f+g) (f+g) Φ hα hadd hadd hΦ
  have him := allPositiveRawIntegrand_integrable hT a a α (f-g) (f-g) Φ hα hsub hsub hΦ
  unfold allPositiveRawMoment
  rw [← integral_sub hip him,← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t =>
    allPositiveRawIntegrand_polarization hT a t α f g Φ hf hg)

def dpAllPositiveBilinearMoment (T η : ℝ) (P Q : Polynomial ℝ)
    (σ : MomentShifts) (Φ : ℝ → ℝ) : ℂ :=
  ∫ t : ℝ, dpAllPositiveIntegrand T t σ
    (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) Φ

theorem dpAllPositiveBilinearMoment_eq_raw (T η : ℝ) (P Q : Polynomial ℝ)
    (σ : MomentShifts) (Φ : ℝ → ℝ) :
    dpAllPositiveBilinearMoment T η P Q σ Φ =
      allPositiveRawMoment T (rawMomentShifts T σ)
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) Φ := rfl

theorem dpAllPositiveBilinearMoment_polarization {T : ℝ} (hT : 1 < T)
    (η : ℝ) (P Q : Polynomial ℝ) (σ : MomentShifts) (Φ : ℝ → ℝ)
    (hσ : σ ∈ momentNormalizedShiftDomain T) (hΦ : SmoothDyadicWeight Φ) :
    dpAllPositiveBilinearMoment T η P Q σ Φ =
      (1/4:ℂ)*(dpAllPositiveMoment T η (P+Q) σ Φ-
        dpAllPositiveMoment T η (P-Q) σ Φ) := by
  rw [dpAllPositiveBilinearMoment_eq_raw]
  have h := allPositiveRawMoment_polarization hT η (rawMomentShifts T σ)
    (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) Φ hσ
    (zeroExtendedPolynomialProfile_zero_above η P)
    (zeroExtendedPolynomialProfile_zero_above η Q) hΦ
  rw [← zeroExtendedPolynomialProfile_add,← zeroExtendedPolynomialProfile_sub] at h
  simpa only [dpAllPositiveMoment_eq_raw] using h

theorem polarPolynomialB_add (η : ℝ) (P Q : Polynomial ℝ) (z : ℂ) :
    polarPolynomialB η (P+Q) z = polarPolynomialB η P z+polarPolynomialB η Q z := by
  have hc (S : Polynomial ℝ) : Continuous (fun a : ℝ =>
      ((Polynomial.eval (1-a/η:ℝ) S:ℝ):ℂ)*polarB a z) := by unfold polarB; fun_prop
  unfold polarPolynomialB
  simp only [Polynomial.eval_add,Complex.ofReal_add,add_mul]
  exact intervalIntegral.integral_add ((hc P).intervalIntegrable _ _)
    ((hc Q).intervalIntegrable _ _)

theorem polarPolynomialB_sub (η : ℝ) (P Q : Polynomial ℝ) (z : ℂ) :
    polarPolynomialB η (P-Q) z = polarPolynomialB η P z-polarPolynomialB η Q z := by
  have hc (S : Polynomial ℝ) : Continuous (fun a : ℝ =>
      ((Polynomial.eval (1-a/η:ℝ) S:ℝ):ℂ)*polarB a z) := by unfold polarB; fun_prop
  unfold polarPolynomialB
  simp only [Polynomial.eval_sub,Complex.ofReal_sub,sub_mul]
  exact intervalIntegral.integral_sub ((hc P).intervalIntegrable _ _)
    ((hc Q).intervalIntegrable _ _)

theorem polarPolynomialC_add (η : ℝ) (P Q : Polynomial ℝ) (z : ℂ) :
    polarPolynomialC η (P+Q) z = polarPolynomialC η P z+polarPolynomialC η Q z := by
  have hc (S : Polynomial ℝ) : Continuous (fun a : ℝ =>
      ((Polynomial.eval (1-a/η:ℝ) S:ℝ):ℂ)*polarC a z) := by unfold polarC; fun_prop
  unfold polarPolynomialC
  simp only [Polynomial.eval_add,Complex.ofReal_add,add_mul]
  exact intervalIntegral.integral_add ((hc P).intervalIntegrable _ _)
    ((hc Q).intervalIntegrable _ _)

theorem polarPolynomialC_sub (η : ℝ) (P Q : Polynomial ℝ) (z : ℂ) :
    polarPolynomialC η (P-Q) z = polarPolynomialC η P z-polarPolynomialC η Q z := by
  have hc (S : Polynomial ℝ) : Continuous (fun a : ℝ =>
      ((Polynomial.eval (1-a/η:ℝ) S:ℝ):ℂ)*polarC a z) := by unfold polarC; fun_prop
  unfold polarPolynomialC
  simp only [Polynomial.eval_sub,Complex.ofReal_sub,sub_mul]
  exact intervalIntegral.integral_sub ((hc P).intervalIntegrable _ _)
    ((hc Q).intervalIntegrable _ _)

def polarPolynomialBilinearJ (η : ℝ) (P Q : Polynomial ℝ) (z : ℂ) : ℂ :=
  polarPolynomialB η P z*polarPolynomialB η Q z*polarH 2 z+
    (polarPolynomialB η P z*polarPolynomialC η Q z+
      polarPolynomialC η P z*polarPolynomialB η Q z)*polarH 1 z+
    polarPolynomialC η P z*polarPolynomialC η Q z*polarH 0 z

theorem polarPolynomialBilinearJ_polarization (η : ℝ) (P Q : Polynomial ℝ) (z : ℂ) :
    polarPolynomialBilinearJ η P Q z =
      (1/4:ℂ)*(polarPolynomialJ η (P+Q) z-polarPolynomialJ η (P-Q) z) := by
  unfold polarPolynomialBilinearJ polarPolynomialJ
  rw [polarPolynomialB_add,polarPolynomialB_sub,polarPolynomialC_add,polarPolynomialC_sub]
  ring

namespace Source

def dpAllPositiveBilinearRegularKernel (η : ℝ) (P Q : Polynomial ℝ)
    (σ : MomentShifts) : ℂ :=
  Complex.exp (σ 2+σ 3)*
    polarGeneralBilinearGeneratorContour η P Q (polarSourceKnots σ) 16 16

theorem dpAllPositiveBilinearRegularKernel_polarization (η : ℝ)
    (P Q : Polynomial ℝ) (σ : MomentShifts)
    (hσ : ∀ j, ‖polarSourceKnots σ j‖ < (16:ℝ)) :
    dpAllPositiveBilinearRegularKernel η P Q σ =
      (1/4:ℂ)*(dpAllPositiveRegularKernel η (P+Q) σ-
        dpAllPositiveRegularKernel η (P-Q) σ) := by
  unfold dpAllPositiveBilinearRegularKernel dpAllPositiveRegularKernel dpRegularKernel
  rw [polarGeneralBilinearGeneratorContour_polarization η P Q _ 16 16 hσ hσ]
  ring

theorem dpAllPositiveBilinearRegularKernel_coincident (η : ℝ)
    (P Q : Polynomial ℝ) (z : ℂ) (hz : ‖z‖ < (16:ℝ)) :
    dpAllPositiveBilinearRegularKernel η P Q (dpCoincidentShifts z) =
      polarPolynomialBilinearJ η P Q z := by
  have hR (j : Fin 4) : ‖polarSourceKnots (dpCoincidentShifts z) j‖ < (16:ℝ) := by
    fin_cases j <;> simp [polarSourceKnots,dpCoincidentShifts,hz]
  rw [dpAllPositiveBilinearRegularKernel_polarization η P Q _ hR,
    dpAllPositiveRegularKernel_coincident η (P+Q) z hz,
    dpAllPositiveRegularKernel_coincident η (P-Q) z hz,
    ← polarPolynomialBilinearJ_polarization]

theorem dpAllPositiveBilinearMoment_normalized_tendsto (hsource : DPv2SharpInput)
    (η : ℝ) (hη : 0 < η) (hηu : η < 1/4) (P Q : Polynomial ℝ)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (σ : MomentShifts)
    (hσ : σ ∈ rectangularClosedPolydisc dpCauchyRadii) :
    Tendsto (fun T : ℝ => dpAllPositiveBilinearMoment T η P Q σ Φ/
      ((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
        dpAllPositiveBilinearRegularKernel η P Q σ)) := by
  have hp := dpAllPositiveMoment_coincident_normalized_tendsto hsource η hη hηu
    (P+Q) Φ hΦ σ hσ
  have hm := dpAllPositiveMoment_coincident_normalized_tendsto hsource η hη hηu
    (P-Q) Φ hΦ σ hσ
  have ht := (hp.sub hm).const_mul (1/4:ℂ)
  have hk := dpAllPositiveBilinearRegularKernel_polarization η P Q σ
    (fun j => (dpCauchyPolydisc_knots_in_domain σ hσ j).1)
  have he : (1/4:ℂ)*
      ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*dpAllPositiveRegularKernel η (P+Q) σ-
        (arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*dpAllPositiveRegularKernel η (P-Q) σ) =
      (arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
        dpAllPositiveBilinearRegularKernel η P Q σ := by rw [hk]; ring
  rw [he] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16:ℝ))] with T hT hL
  have hR (j : Fin 4) : 2*dpCauchyRadii j < Real.log T := by
    have hj : dpCauchyRadii j ≤ (8:ℝ) := by fin_cases j <;> norm_num [dpCauchyRadii]
    linarith
  rw [dpAllPositiveBilinearMoment_polarization hT η P Q σ Φ
    (closedPolydisc_subset_momentNormalizedShiftDomain hT dpCauchyRadii hR hσ) hΦ]
  ring

theorem dpAllPositiveBilinearMoment_polarPolynomialBilinearJ_tendsto
    (hsource : DPv2SharpInput) (η : ℝ) (hη : 0 < η) (hηu : η < 1/4)
    (P Q : Polynomial ℝ) (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ)
    (z : ℂ) (hz : ‖z‖ ≤ (4:ℝ)) :
    Tendsto (fun T : ℝ => dpAllPositiveBilinearMoment T η P Q (dpCoincidentShifts z) Φ/
      ((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*polarPolynomialBilinearJ η P Q z)) := by
  have h := dpAllPositiveBilinearMoment_normalized_tendsto hsource η hη hηu P Q Φ hΦ
    (dpCoincidentShifts z) (dpCoincidentShifts_mem_polydisc hz)
  rw [dpAllPositiveBilinearRegularKernel_coincident η P Q z (by linarith)] at h
  exact h

end Source
end
end SixthMoment
