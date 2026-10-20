import Sechstmoment.Numerator.Shared.MomentHolomorphy
import Sechstmoment.Numerator.V.DP.CenteringRemainder


namespace Sechstmoment
open Complex Metric MeasureTheory Set
open scoped BigOperators Topology

set_option maxHeartbeats 1000000

noncomputable def allPositiveFourthExtended (p : MomentShifts × ℂ) : ℂ :=
  let s := (1/2 : ℂ)+p.2*Complex.I
  riemannZeta (s+p.1 0)*riemannZeta (s+p.1 1)*
    riemannZeta (s-p.1 2)*riemannZeta (s-p.1 3)

theorem allPositiveFourthExtended_contDiffAt (α : MomentShifts) (t : ℝ)
    (hα : α ∈ momentRawShiftDomain) :
    ContDiffAt ℂ 1 allPositiveFourthExtended (α,(t:ℂ)) := by
  have hn (j : Fin 4) : criticalLinePoint t+α j ≠ 1 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [add_re,criticalLinePoint_re,one_re] at hr
    linarith [(abs_lt.mp (hα j)).2]
  have hm (j : Fin 4) : criticalLinePoint t-α j ≠ 1 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [sub_re,criticalLinePoint_re,one_re] at hr
    linarith [(abs_lt.mp (hα j)).1]
  have hp (j : Fin 4) : ContDiffAt ℂ 1
      (fun p : MomentShifts × ℂ => riemannZeta ((1/2:ℂ)+p.2*Complex.I+p.1 j))
      (α,(t:ℂ)) :=
    (analyticOn_riemannZeta _ (by simpa [criticalLinePoint] using hn j)).contDiffAt.comp
      (α,(t:ℂ)) (by fun_prop)
  have hminus (j : Fin 4) : ContDiffAt ℂ 1
      (fun p : MomentShifts × ℂ => riemannZeta ((1/2:ℂ)+p.2*Complex.I-p.1 j))
      (α,(t:ℂ)) :=
    (analyticOn_riemannZeta _ (by simpa [criticalLinePoint] using hm j)).contDiffAt.comp
      (α,(t:ℂ)) (by fun_prop)
  exact (((hp 0).mul (hp 1)).mul (hminus 2)).mul (hminus 3)

noncomputable def allPositiveFourthFamily : ComplexIntegralFamily momentRawShiftDomain ℝ where
  value α t := allPositiveFourthExtended (α,(t:ℂ))
  derivative α t := complexFirstFDeriv allPositiveFourthExtended (α,(t:ℂ))
  continuous_value := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hm : Continuous (fun p : momentRawShiftDomain × ℝ => (p.1.1,(p.2:ℂ))) := by fun_prop
    exact (allPositiveFourthExtended_contDiffAt p.1.1 p.2 p.1.2).continuousAt.comp
      (f := fun p : momentRawShiftDomain × ℝ => (p.1.1,(p.2:ℂ))) (x := p) hm.continuousAt
  continuous_derivative := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hm : Continuous (fun p : momentRawShiftDomain × ℝ => (p.1.1,(p.2:ℂ))) := by fun_prop
    exact (complexFirstFDeriv_continuousAt _ _
      (allPositiveFourthExtended_contDiffAt p.1.1 p.2 p.1.2)).comp
      (f := fun p : momentRawShiftDomain × ℝ => (p.1.1,(p.2:ℂ))) (x := p) hm.continuousAt
  hasFDerivAt := by
    intro α hα t
    exact complexFirstFDeriv_hasFDerivAt _ _
      ((allPositiveFourthExtended_contDiffAt α t hα).differentiableAt (by norm_num))

noncomputable def allPositiveRawIntegrand (T t : ℝ) (α : MomentShifts)
    (f g Φ : ℝ → ℝ) : ℂ :=
  (Φ (t/T):ℂ)*zetaChi (1-criticalLinePoint t)*allPositiveFourthProduct t α*
    profileDirichletSum T f (1-criticalLinePoint t)*profileDirichletSum T g (1-criticalLinePoint t)

noncomputable def allPositiveRawMoment (T : ℝ) (α : MomentShifts) (f g Φ : ℝ → ℝ) : ℂ :=
  ∫ t : ℝ, allPositiveRawIntegrand T t α f g Φ

noncomputable def allPositiveAmplitude (T : ℝ) (f g Φ : ℝ → ℝ) (t : ℝ) : ℂ :=
  (Φ (t/T):ℂ)*zetaChi (1-criticalLinePoint t)*
    profileDirichletSum T f (1-criticalLinePoint t)*profileDirichletSum T g (1-criticalLinePoint t)

theorem allPositiveAmplitude_continuous {T : ℝ} (hT : 1 < T)
    (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, b < x → g x=0) (hΦ : Continuous Φ) :
    Continuous (allPositiveAmplitude T f g Φ) := by
  have hs : Continuous (fun t : ℝ => 1-criticalLinePoint t) := by
    unfold criticalLinePoint
    fun_prop
  have hχ : Continuous (fun t : ℝ => zetaChi (1-criticalLinePoint t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hc := zetaChi_analyticOnNhd_strip (1-criticalLinePoint t)
      (by norm_num [sub_re,criticalLinePoint_re])
    exact hc.continuousAt.comp (f := fun t : ℝ => 1-criticalLinePoint t) hs.continuousAt
  exact (((by fun_prop : Continuous (fun t : ℝ => (Φ (t/T):ℂ))).mul hχ).mul
    ((profileDirichletSum_continuous hT a f hf).comp hs)).mul
      ((profileDirichletSum_continuous hT b g hg).comp hs)

noncomputable def allPositiveMomentFamily {T : ℝ} (hT : 1 < T)
    (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, b < x → g x=0) (hΦ : Continuous Φ) :
    ComplexIntegralFamily momentRawShiftDomain Unit :=
  ((allPositiveFourthFamily.mulAux (allPositiveAmplitude T f g Φ)
    (allPositiveAmplitude_continuous hT a b f g Φ hf hg hΦ)).reindexAux
      (fun p : Unit × ℝ => p.2) continuous_snd).intervalIntegral
        momentRawShiftDomain_isOpen T (2*T) (by linarith)

theorem allPositiveRawMoment_eq_interval {T : ℝ} (hT : 0 < T)
    (α : MomentShifts) (f g Φ : ℝ → ℝ) (hΦ : tsupport Φ ⊆ Icc 1 2) :
    allPositiveRawMoment T α f g Φ =
      ∫ t in T..2*T, allPositiveRawIntegrand T t α f g Φ := by
  unfold allPositiveRawMoment
  rw [intervalIntegral.integral_of_le (by linarith : T ≤ 2*T),← integral_Icc_eq_integral_Ioc]
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
  intro t ht
  have hx : t/T ∉ Icc (1:ℝ) 2 := by
    intro hx
    apply ht
    constructor
    · have h := (le_div_iff₀ hT).mp hx.1
      linarith
    · have h := (div_le_iff₀ hT).mp hx.2
      linarith
  have hzero : Φ (t/T)=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hΦ h))
  simp only [allPositiveRawIntegrand,hzero,Complex.ofReal_zero,zero_mul]

theorem allPositiveMomentFamily_value {T : ℝ} (hT : 1 < T)
    (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, b < x → g x=0) (hΦ : SmoothDyadicWeight Φ)
    (α : MomentShifts) :
    (allPositiveMomentFamily hT a b f g Φ hf hg hΦ.1.continuous).value α () =
      allPositiveRawMoment T α f g Φ := by
  rw [allPositiveRawMoment_eq_interval (zero_lt_one.trans hT) α f g Φ hΦ.2]
  change (∫ t in T..2*T, allPositiveAmplitude T f g Φ t*allPositiveFourthExtended (α,(t:ℂ))) = _
  apply intervalIntegral.integral_congr
  intro t _
  unfold allPositiveAmplitude allPositiveFourthExtended allPositiveRawIntegrand allPositiveFourthProduct
    criticalLinePoint
  ring

attribute [irreducible] allPositiveMomentFamily

theorem allPositiveRawMoment_differentiableOn {T : ℝ} (hT : 1 < T)
    (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, b < x → g x=0) (hΦ : SmoothDyadicWeight Φ) :
    DifferentiableOn ℂ (fun α => allPositiveRawMoment T α f g Φ) momentRawShiftDomain := by
  intro α hα
  have h := ((allPositiveMomentFamily hT a b f g Φ hf hg hΦ.1.continuous).hasFDerivAt α hα ()).differentiableAt
  have heq : (fun α => (allPositiveMomentFamily hT a b f g Φ hf hg hΦ.1.continuous).value α ()) =
      (fun α => allPositiveRawMoment T α f g Φ) :=
    funext (fun α => allPositiveMomentFamily_value hT a b f g Φ hf hg hΦ α)
  rw [heq] at h
  exact h.differentiableWithinAt

theorem dpAllPositiveMoment_eq_raw (T η : ℝ) (P : Polynomial ℝ) (σ : MomentShifts) (Φ : ℝ → ℝ) :
    dpAllPositiveMoment T η P σ Φ = allPositiveRawMoment T (rawMomentShifts T σ)
      (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) Φ := rfl

theorem dpAllPositiveMoment_differentiableOn_normalized {T : ℝ} (hT : 1 < T)
    (η : ℝ) (P : Polynomial ℝ) (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    DifferentiableOn ℂ (fun σ => dpAllPositiveMoment T η P σ Φ)
      (momentNormalizedShiftDomain T) := by
  simp_rw [dpAllPositiveMoment_eq_raw]
  exact (allPositiveRawMoment_differentiableOn hT η η _ _ Φ
    (Source.dpProfile_zero_above η P) (Source.dpProfile_zero_above η P) hΦ).comp
      (rawMomentShifts_differentiable T).differentiableOn (fun _ h => h)

theorem dpAllPositiveMoment_differentiableOn_polydisc {T : ℝ} (hT : 1 < T)
    (R : Fin 4 → ℝ) (hR : ∀ j, 2*R j < Real.log T)
    (η : ℝ) (P : Polynomial ℝ) (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    DifferentiableOn ℂ (fun σ => dpAllPositiveMoment T η P σ Φ)
      (rectangularClosedPolydisc R) :=
  (dpAllPositiveMoment_differentiableOn_normalized hT η P Φ hΦ).mono
    (closedPolydisc_subset_momentNormalizedShiftDomain hT R hR)

end Sechstmoment
