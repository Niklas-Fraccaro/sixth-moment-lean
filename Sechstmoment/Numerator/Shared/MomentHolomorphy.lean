import Sechstmoment.Analysis.Complex.PartialDerivative
import Sechstmoment.Analysis.Complex.Polydisc
import Sechstmoment.Analysis.Integration.ComplexParameter
import Sechstmoment.Zeta.Moments.AnalyticMomentLinearity


namespace Sechstmoment
open Complex Metric MeasureTheory Set
open scoped BigOperators Topology

set_option maxHeartbeats 1000000

def momentRawShiftDomain : Set MomentShifts :=
  {α | ∀ j, |(α j).re| < 1/2}

theorem momentRawShiftDomain_isOpen : IsOpen momentRawShiftDomain := by
  unfold momentRawShiftDomain
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro j
  exact isOpen_lt ((Complex.continuous_re.comp (continuous_apply j)).abs) continuous_const

noncomputable def shiftedFourthExtended (p : MomentShifts × ℂ) : ℂ :=
  let s := (1/2 : ℂ)+p.2*Complex.I
  riemannZeta (s+p.1 0)*riemannZeta (s+p.1 1)*
    riemannZeta (1-s+p.1 2)*riemannZeta (1-s+p.1 3)

theorem shiftedFourthExtended_contDiffAt (α : MomentShifts) (t : ℝ)
    (hα : α ∈ momentRawShiftDomain) :
    ContDiffAt ℂ 1 shiftedFourthExtended (α,(t:ℂ)) := by
  have hn (j : Fin 4) : criticalLinePoint t+α j ≠ 1 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [add_re,criticalLinePoint_re,one_re] at hr
    linarith [(abs_lt.mp (hα j)).2]
  have hm (j : Fin 4) : 1-criticalLinePoint t+α j ≠ 1 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [add_re,sub_re,criticalLinePoint_re,one_re] at hr
    linarith [(abs_lt.mp (hα j)).2]
  have hp (j : Fin 4) : ContDiffAt ℂ 1
      (fun p : MomentShifts × ℂ => riemannZeta ((1/2:ℂ)+p.2*Complex.I+p.1 j))
      (α,(t:ℂ)) :=
    (analyticOn_riemannZeta _ (by simpa [criticalLinePoint] using hn j)).contDiffAt.comp
      (α,(t:ℂ)) (by fun_prop)
  have hminus (j : Fin 4) : ContDiffAt ℂ 1
      (fun p : MomentShifts × ℂ => riemannZeta (1-((1/2:ℂ)+p.2*Complex.I)+p.1 j))
      (α,(t:ℂ)) :=
    (analyticOn_riemannZeta _ (by simpa [criticalLinePoint] using hm j)).contDiffAt.comp
      (α,(t:ℂ)) (by fun_prop)
  exact (((hp 0).mul (hp 1)).mul (hminus 2)).mul (hminus 3)

noncomputable def shiftedFourthFamily : ComplexIntegralFamily momentRawShiftDomain ℝ where
  value α t := shiftedFourthExtended (α,(t:ℂ))
  derivative α t := complexFirstFDeriv shiftedFourthExtended (α,(t:ℂ))
  continuous_value := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hm : Continuous (fun p : momentRawShiftDomain × ℝ => (p.1.1,(p.2:ℂ))) := by fun_prop
    exact (shiftedFourthExtended_contDiffAt p.1.1 p.2 p.1.2).continuousAt.comp
      (f := fun p : momentRawShiftDomain × ℝ => (p.1.1,(p.2:ℂ))) (x := p) hm.continuousAt
  continuous_derivative := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hm : Continuous (fun p : momentRawShiftDomain × ℝ => (p.1.1,(p.2:ℂ))) := by fun_prop
    exact (complexFirstFDeriv_continuousAt _ _
      (shiftedFourthExtended_contDiffAt p.1.1 p.2 p.1.2)).comp
      (f := fun p : momentRawShiftDomain × ℝ => (p.1.1,(p.2:ℂ))) (x := p) hm.continuousAt
  hasFDerivAt := by
    intro α hα t
    exact complexFirstFDeriv_hasFDerivAt _ _
      ((shiftedFourthExtended_contDiffAt α t hα).differentiableAt (by norm_num))

noncomputable def chiMomentAmplitude (T : ℝ) (f g Φ : ℝ → ℝ) (t : ℝ) : ℂ :=
  (Φ (t/T):ℂ)*criticalChi t*profileDirichletSum T f (1-criticalLinePoint t)*
    profileDirichletSum T g (1-criticalLinePoint t)

theorem chiMomentAmplitude_continuous {T : ℝ} (hT : 1 < T)
    (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, b < x → g x=0) (hΦ : Continuous Φ) :
    Continuous (chiMomentAmplitude T f g Φ) := by
  have hs : Continuous (fun t : ℝ => 1-criticalLinePoint t) := by
    unfold criticalLinePoint
    fun_prop
  exact (((by fun_prop : Continuous (fun t : ℝ => (Φ (t/T):ℂ))).mul criticalChi_continuous).mul
    ((profileDirichletSum_continuous hT a f hf).comp hs)).mul
      ((profileDirichletSum_continuous hT b g hg).comp hs)

noncomputable def chiMomentFamily {T : ℝ} (hT : 1 < T)
    (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, b < x → g x=0) (hΦ : Continuous Φ) :
    ComplexIntegralFamily momentRawShiftDomain Unit :=
  ((shiftedFourthFamily.mulAux (chiMomentAmplitude T f g Φ)
    (chiMomentAmplitude_continuous hT a b f g Φ hf hg hΦ)).reindexAux
      (fun p : Unit × ℝ => p.2) continuous_snd).intervalIntegral
        momentRawShiftDomain_isOpen T (2*T) (by linarith)

theorem chiTwistedFourthMoment_eq_interval {T : ℝ} (hT : 0 < T)
    (α : MomentShifts) (f g Φ : ℝ → ℝ) (hΦ : tsupport Φ ⊆ Icc 1 2) :
    chiTwistedFourthMoment T α f g Φ =
      ∫ t in T..2*T, chiTwistedFourthIntegrand T t α f g Φ := by
  unfold chiTwistedFourthMoment
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
  simp only [chiTwistedFourthIntegrand,hzero,Complex.ofReal_zero,zero_mul]

theorem chiMomentFamily_value {T : ℝ} (hT : 1 < T)
    (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, b < x → g x=0) (hΦ : SmoothDyadicWeight Φ)
    (α : MomentShifts) :
    (chiMomentFamily hT a b f g Φ hf hg hΦ.1.continuous).value α () =
      chiTwistedFourthMoment T α f g Φ := by
  rw [chiTwistedFourthMoment_eq_interval (zero_lt_one.trans hT) α f g Φ hΦ.2]
  change (∫ t in T..2*T, chiMomentAmplitude T f g Φ t*shiftedFourthExtended (α,(t:ℂ))) = _
  apply intervalIntegral.integral_congr
  intro t _
  unfold chiMomentAmplitude shiftedFourthExtended chiTwistedFourthIntegrand shiftedFourthProduct
    criticalLinePoint
  ring

attribute [irreducible] chiMomentFamily

theorem chiTwistedFourthMoment_differentiableOn_raw {T : ℝ} (hT : 1 < T)
    (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, b < x → g x=0) (hΦ : SmoothDyadicWeight Φ) :
    DifferentiableOn ℂ (fun α => chiTwistedFourthMoment T α f g Φ) momentRawShiftDomain := by
  intro α hα
  have h := ((chiMomentFamily hT a b f g Φ hf hg hΦ.1.continuous).hasFDerivAt α hα ()).differentiableAt
  have heq : (fun α => (chiMomentFamily hT a b f g Φ hf hg hΦ.1.continuous).value α ()) =
      (fun α => chiTwistedFourthMoment T α f g Φ) :=
    funext (fun α => chiMomentFamily_value hT a b f g Φ hf hg hΦ α)
  rw [heq] at h
  exact h.differentiableWithinAt

def momentNormalizedShiftDomain (T : ℝ) : Set MomentShifts :=
  (rawMomentShifts T) ⁻¹' momentRawShiftDomain

theorem rawMomentShifts_differentiable (T : ℝ) : Differentiable ℂ (rawMomentShifts T) := by
  unfold rawMomentShifts
  fun_prop

theorem chiTwistedFourthMoment_differentiableOn_normalized {T : ℝ} (hT : 1 < T)
    (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, b < x → g x=0) (hΦ : SmoothDyadicWeight Φ) :
    DifferentiableOn ℂ (fun σ => chiTwistedFourthMoment T (rawMomentShifts T σ) f g Φ)
      (momentNormalizedShiftDomain T) :=
  (chiTwistedFourthMoment_differentiableOn_raw hT a b f g Φ hf hg hΦ).comp
    (rawMomentShifts_differentiable T).differentiableOn (fun _ h => h)

theorem closedPolydisc_subset_momentNormalizedShiftDomain {T : ℝ} (hT : 1 < T)
    (R : Fin 4 → ℝ) (hR : ∀ j, 2*R j < Real.log T) :
    rectangularClosedPolydisc R ⊆ momentNormalizedShiftDomain T := by
  intro σ hσ j
  change |(σ j/(Real.log T:ℂ)).re| < 1/2
  have hL := Real.log_pos hT
  rw [div_ofReal_re,abs_div,abs_of_pos hL]
  apply (div_lt_iff₀ hL).mpr
  have hre : |(σ j).re| ≤ ‖σ j‖ := Complex.abs_re_le_norm _
  have hb : ‖σ j‖ ≤ R j := hσ j
  have hr := hR j
  linarith

theorem chiTwistedFourthMoment_differentiableOn_polydisc {T : ℝ} (hT : 1 < T)
    (R : Fin 4 → ℝ) (hR : ∀ j, 2*R j < Real.log T)
    (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, b < x → g x=0) (hΦ : SmoothDyadicWeight Φ) :
    DifferentiableOn ℂ (fun σ => chiTwistedFourthMoment T (rawMomentShifts T σ) f g Φ)
      (rectangularClosedPolydisc R) :=
  (chiTwistedFourthMoment_differentiableOn_normalized hT a b f g Φ hf hg hΦ).mono
    (closedPolydisc_subset_momentNormalizedShiftDomain hT R hR)

end Sechstmoment
