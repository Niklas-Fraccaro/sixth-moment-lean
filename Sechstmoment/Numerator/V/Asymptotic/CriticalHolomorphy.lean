import Sechstmoment.Numerator.V.Asymptotic.CriticalSeparatedMain
import Sechstmoment.Numerator.V.DP.DPAllPositiveHolomorphy

/-! Joint holomorphy of the literal shifted-chi moment in all four zeta
shifts. The independent chi shift is retained in the actual amplitude. -/

namespace Sechstmoment.Source
open Complex Real Set MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

def noDPAllPositiveSigns (β : MomentShifts) : MomentShifts :=
  ![β 0,β 1,-β 2,-β 3]

theorem noDPAllPositiveSigns_differentiable : Differentiable ℂ noDPAllPositiveSigns := by
  apply differentiable_pi.mpr
  intro j
  fin_cases j
  · change Differentiable ℂ (fun β : MomentShifts => β 0)
    fun_prop
  · change Differentiable ℂ (fun β : MomentShifts => β 1)
    fun_prop
  · change Differentiable ℂ (fun β : MomentShifts => -β 2)
    fun_prop
  · change Differentiable ℂ (fun β : MomentShifts => -β 3)
    fun_prop

theorem noDPAllPositiveSigns_mem_domain {β : MomentShifts}
    (hβ : β ∈ momentRawShiftDomain) : noDPAllPositiveSigns β ∈ momentRawShiftDomain := by
  intro j
  fin_cases j
  · simpa [noDPAllPositiveSigns] using hβ 0
  · simpa [noDPAllPositiveSigns] using hβ 1
  · simpa [noDPAllPositiveSigns] using hβ 2
  · simpa [noDPAllPositiveSigns] using hβ 3

def noDPShiftedChiAmplitude (T : ℝ) (u : ℂ) (f g : ℝ → ℝ) (w : ℝ → ℂ)
    (t : ℝ) : ℂ :=
  w (t/T)*zetaChi (1-criticalLinePoint t+u)*
    profileDirichletSum T f (1-criticalLinePoint t)*
    profileDirichletSum T g (1-criticalLinePoint t)

theorem noDPShiftedChiAmplitude_continuous {T : ℝ} (hT : 1 < T)
    {u : ℂ} (hu : |u.re| < 1/2) (a b : ℝ) (f g : ℝ → ℝ) (w : ℝ → ℂ)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, b < x → g x=0) (hw : Continuous w) :
    Continuous (noDPShiftedChiAmplitude T u f g w) := by
  have hs : Continuous (fun t : ℝ => 1-criticalLinePoint t) := by
    unfold criticalLinePoint
    fun_prop
  have hχ : Continuous (fun t : ℝ => zetaChi (1-criticalLinePoint t+u)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hc := zetaChi_analyticOnNhd_strip (1-criticalLinePoint t+u) (by
      change 0 < (1-criticalLinePoint t+u).re ∧ (1-criticalLinePoint t+u).re < 1
      simp only [add_re,sub_re,one_re,criticalLinePoint_re]
      constructor <;> linarith [(abs_lt.mp hu).1,(abs_lt.mp hu).2])
    exact hc.continuousAt.comp (f := fun t : ℝ => 1-criticalLinePoint t+u)
      (hs.add continuous_const).continuousAt
  exact (((hw.comp (by fun_prop)).mul hχ).mul
    ((profileDirichletSum_continuous hT a f hf).comp hs)).mul
      ((profileDirichletSum_continuous hT b g hg).comp hs)

def noDPShiftedChiMomentFamily {T : ℝ} (hT : 1 < T) {u : ℂ} (hu : |u.re| < 1/2)
    (a b : ℝ) (f g : ℝ → ℝ) (w : ℝ → ℂ)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, b < x → g x=0) (hw : Continuous w) :
    ComplexIntegralFamily momentRawShiftDomain Unit :=
  ((allPositiveFourthFamily.mulAux (noDPShiftedChiAmplitude T u f g w)
    (noDPShiftedChiAmplitude_continuous hT hu a b f g w hf hg hw)).reindexAux
      (fun p : Unit × ℝ => p.2) continuous_snd).intervalIntegral
        momentRawShiftDomain_isOpen T (2*T) (by linarith)

def noDPShiftedChiRawMoment (T : ℝ) (u : ℂ) (f g : ℝ → ℝ) (w : ℝ → ℂ)
    (β : MomentShifts) : ℂ :=
  ∫ t : ℝ, shiftedChiProfileFactor T u β f g (criticalLinePoint t)*w (t/T)

theorem noDPShiftedChiRawMoment_eq_interval {T : ℝ} (hT : 0 < T)
    (u : ℂ) (f g : ℝ → ℝ) (w : ℝ → ℂ) (hw : tsupport w ⊆ Icc (1:ℝ) 2)
    (β : MomentShifts) :
    noDPShiftedChiRawMoment T u f g w β =
      ∫ t in T..2*T, shiftedChiProfileFactor T u β f g (criticalLinePoint t)*w (t/T) := by
  unfold noDPShiftedChiRawMoment
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
  have hzero : w (t/T)=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hw h))
  rw [hzero,mul_zero]

theorem noDPShiftedChiMomentFamily_value {T : ℝ} (hT : 1 < T)
    {u : ℂ} (hu : |u.re| < 1/2) (a b : ℝ) (f g : ℝ → ℝ) (w : ℝ → ℂ)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, b < x → g x=0)
    (hw : Continuous w) (hws : tsupport w ⊆ Icc (1:ℝ) 2) (β : MomentShifts) :
    (noDPShiftedChiMomentFamily hT hu a b f g w hf hg hw).value (noDPAllPositiveSigns β) () =
      noDPShiftedChiRawMoment T u f g w β := by
  rw [noDPShiftedChiRawMoment_eq_interval (zero_lt_one.trans hT) u f g w hws β]
  change (∫ t in T..2*T, noDPShiftedChiAmplitude T u f g w t*
    allPositiveFourthExtended (noDPAllPositiveSigns β,(t:ℂ))) = _
  apply intervalIntegral.integral_congr
  intro t _
  simp [noDPShiftedChiAmplitude,allPositiveFourthExtended,noDPAllPositiveSigns,
    shiftedChiProfileFactor,shiftedChiZetaFactor,criticalLinePoint,Fin.prod_univ_succ]
  ring

attribute [irreducible] noDPShiftedChiMomentFamily

theorem noDPShiftedChiRawMoment_differentiableOn {T : ℝ} (hT : 1 < T)
    {u : ℂ} (hu : |u.re| < 1/2) (a b : ℝ) (f g : ℝ → ℝ) (w : ℝ → ℂ)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, b < x → g x=0)
    (hw : Continuous w) (hws : tsupport w ⊆ Icc (1:ℝ) 2) :
    DifferentiableOn ℂ (noDPShiftedChiRawMoment T u f g w) momentRawShiftDomain := by
  intro β hβ
  have h := ((noDPShiftedChiMomentFamily hT hu a b f g w hf hg hw).hasFDerivAt
    (noDPAllPositiveSigns β) (noDPAllPositiveSigns_mem_domain hβ) ()).differentiableAt.comp
      β (noDPAllPositiveSigns_differentiable β)
  have heq : (fun β => (noDPShiftedChiMomentFamily hT hu a b f g w hf hg hw).value
      (noDPAllPositiveSigns β) ()) = noDPShiftedChiRawMoment T u f g w :=
    funext (fun β => noDPShiftedChiMomentFamily_value hT hu a b f g w hf hg hw hws β)
  change DifferentiableAt ℂ (fun β => (noDPShiftedChiMomentFamily
    hT hu a b f g w hf hg hw).value (noDPAllPositiveSigns β) ()) β at h
  rw [heq] at h
  exact h.differentiableWithinAt

theorem noDPCriticalPolynomialMoment_differentiableOn_polydisc {T : ℝ} (hT : 1 < T)
    {z : ℂ} (hz : |(z/(Real.log T:ℂ)).re| < 1/2)
    (R : Fin 4 → ℝ) (hR : ∀ j, 2*R j < Real.log T)
    (η : ℝ) (P Q : Polynomial ℝ) (w : ℝ → ℂ)
    (hw : Continuous w) (hws : tsupport w ⊆ Icc (1:ℝ) 2) :
    DifferentiableOn ℂ (fun σ => noDPCriticalPolynomialMoment w T η P Q σ z)
      (rectangularClosedPolydisc R) := by
  have h := (noDPShiftedChiRawMoment_differentiableOn hT hz η η
    (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) w
    (dpProfile_zero_above η P) (dpProfile_zero_above η Q) hw hws).comp
      (rawMomentShifts_differentiable T).differentiableOn (fun _ h => h)
  exact h.mono (closedPolydisc_subset_momentNormalizedShiftDomain hT R hR)

end
end Sechstmoment.Source
