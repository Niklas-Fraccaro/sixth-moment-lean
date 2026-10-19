import Sechstmoment.Denominator.Gram.PhaseError
import Sechstmoment.Denominator.Gram.PhaseModelBound
import Sechstmoment.Denominator.Unbalanced.ActualMomentRegularity

/-! Actual Bochner integrability justifies the subtraction between the
extreme shifted zeta moment and its complete one-sided model. -/
namespace Sechstmoment
open Complex Real Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

theorem d06ExtremeMinusShiftedIntegrand_continuousOn_of_norm_bound {T : ℝ}
    (hT : 1<T) (hL : 1≤Real.log T) (R : ℝ) (hRL : R≤Real.log T)
    (σ : Fin 2 → ℂ) (hσ : ∀ i,‖σ i‖≤R)
    (ρ : Fin 4 → ℝ → ℝ) (a : Fin 4 → ℝ)
    (hρs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) :
    ContinuousOn (fun t : ℝ => (Φ (t/T) : ℂ)*(criticalChi t)⁻¹*(criticalChi t)⁻¹*
      zetaCPlus T t (σ 0)*zetaCMinus T t (σ 1)*d06AllPositiveAmplifier T t ρ)
      (Icc T (2*T)) := by
  have hplus : ContinuousOn (fun t : ℝ => zetaCPlus T t (σ 0)) (Icc T (2*T)) := by
    intro t ht
    unfold zetaCPlus shiftedZetaGenerator
    have hs : 1< |(criticalLinePoint t).im| := by
      rw [criticalLinePoint_im,abs_of_pos (zero_lt_one.trans (hT.trans_le ht.1))]
      exact hT.trans_le ht.1
    have hz := (differentiableAt_riemannZeta
      (d04_shifted_zeta_nonpole_of_norm_le hL hs ((hσ 0).trans hRL))).continuousAt
    have hm : ContinuousWithinAt (fun u : ℝ => criticalLinePoint u+
        σ 0/(Real.log T : ℂ)) (Icc T (2*T)) t := by
      unfold criticalLinePoint
      fun_prop
    exact continuousWithinAt_const.mul
      (hz.comp_continuousWithinAt (f := fun u : ℝ => criticalLinePoint u+
        σ 0/(Real.log T : ℂ)) (x := t) hm)
  have hminus : ContinuousOn (fun t : ℝ => zetaCMinus T t (σ 1)) (Icc T (2*T)) := by
    intro t ht
    unfold zetaCMinus shiftedZetaGenerator
    have hs : 1< |(1-criticalLinePoint t).im| := by
      simp only [sub_im,one_im,criticalLinePoint_im,zero_sub,abs_neg]
      rw [abs_of_pos (zero_lt_one.trans (hT.trans_le ht.1))]
      exact hT.trans_le ht.1
    have hz := (differentiableAt_riemannZeta
      (d04_shifted_zeta_nonpole_of_norm_le hL hs ((hσ 1).trans hRL))).continuousAt
    have hm : ContinuousWithinAt (fun u : ℝ => 1-criticalLinePoint u+
        σ 1/(Real.log T : ℂ)) (Icc T (2*T)) t := by
      unfold criticalLinePoint
      fun_prop
    exact continuousWithinAt_const.mul
      (hz.comp_continuousWithinAt (f := fun u : ℝ => 1-criticalLinePoint u+
        σ 1/(Real.log T : ℂ)) (x := t) hm)
  have hcut : Continuous (fun t : ℝ => (Φ (t/T) : ℂ)*(criticalChi t)⁻¹*(criticalChi t)⁻¹) :=
    ((by fun_prop : Continuous (fun t : ℝ => (Φ (t/T) : ℂ))).mul
      d04_criticalChi_inv_continuous).mul d04_criticalChi_inv_continuous
  exact ((hcut.continuousOn.mul hplus).mul hminus).mul
    (d06AllPositiveAmplifier_continuous hT ρ a hρs).continuousOn

theorem d06ExtremeMinusShiftedIntegrand_integrable_of_norm_bound {T : ℝ}
    (hT : 1<T) (hL : 1≤Real.log T) (R : ℝ) (hRL : R≤Real.log T)
    (σ : Fin 2 → ℂ) (hσ : ∀ i,‖σ i‖≤R)
    (ρ : Fin 4 → ℝ → ℝ) (a : Fin 4 → ℝ)
    (hρs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ⊆Icc 1 2) :
    Integrable (fun t : ℝ => (Φ (t/T) : ℂ)*(criticalChi t)⁻¹*(criticalChi t)⁻¹*
      zetaCPlus T t (σ 0)*zetaCMinus T t (σ 1)*d06AllPositiveAmplifier T t ρ) := by
  have hc := d06ExtremeMinusShiftedIntegrand_continuousOn_of_norm_bound
    hT hL R hRL σ hσ ρ a hρs Φ hΦ
  have hci : IntegrableOn (fun t : ℝ => (Φ (t/T) : ℂ)*(criticalChi t)⁻¹*(criticalChi t)⁻¹*
      zetaCPlus T t (σ 0)*zetaCMinus T t (σ 1)*d06AllPositiveAmplifier T t ρ)
      (Icc T (2*T)) volume :=
    hc.integrableOn_compact (isCompact_Icc : IsCompact (Icc T (2*T)))
  have hi := hci.integrable_indicator measurableSet_Icc
  apply hi.congr
  filter_upwards [] with t
  by_cases ht : t∈Icc T (2*T)
  · simp only [indicator_of_mem ht]
  · simp only [indicator_of_notMem ht]
    have hzero : Φ (t/T)=0 := by
      by_contra hn
      have hx := hΦs (subset_tsupport Φ hn)
      apply ht
      constructor
      · simpa using (le_div_iff₀ (zero_lt_one.trans hT)).mp hx.1
      · exact (div_le_iff₀ (zero_lt_one.trans hT)).mp hx.2
    rw [hzero]
    simp

theorem d06ExtremeOneSidedIntegrand_integrable {T R : ℝ}
    (hT : 1<T) (hR : 0≤R) (hRL : 2*R≤Real.log T)
    (ρ : Fin 4 → ℝ → ℝ) (a : Fin 4 → ℝ)
    (hρs : ∀ j,tsupport (ρ j)⊆Icc 0 (a j))
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc (1:ℝ) 2)
    (σ : Fin 2 → ℂ) (hσ : ∀ j,‖σ j‖≤R) :
    Integrable (fun t : ℝ => (Φ (t/T) : ℂ)*(criticalChi t)⁻¹*
      d04CenteringPurePower T t (σ 0)*d04OneSidedCenteredPair T t σ*
        d06AllPositiveAmplifier T t ρ) := by
  have ht : 0<T := zero_lt_one.trans hT
  let τ : ℂ := -σ 0/(Real.log T : ℂ)
  let β : ℂ := d04CenteringPurePower T T (σ 0)
  let F : ℝ → ℂ := d06ChiTimePowerProfile T (fun y => (Φ y : ℂ)) τ
  have hΦC : ContDiff ℝ ∞ (fun y => (Φ y : ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ
  have hΦCs : tsupport (fun y => (Φ y : ℂ))⊆Icc (1:ℝ) 2 :=
    (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦs
  have hFI : Integrable F := d06ChiTimePowerProfile_integrable T hΦC hΦCs τ
  have hcap : ∀ j x,a j<x → ρ j x=0 := by
    intro j x hx
    by_contra hn
    exact (not_lt_of_ge (hρs j (subset_tsupport (ρ j) hn)).2) hx
  have hi := (d06OneSided_model_weighted_integrable hT hR hRL a ρ hcap σ hσ F hFI).const_mul β
  apply hi.congr
  exact Eventually.of_forall fun t => by
    dsimp only
    by_cases hz : Φ (t/T)=0
    · simp [F,d06ChiTimePowerProfile,a03ProfileProduct,hz]
    · have hyp : 0<t/T := zero_lt_one.trans_le (hΦs (subset_tsupport Φ hz)).1
      have he := d04CenteringPurePower_dyadic_factorization ht hyp (σ 0)
      rw [show T*(t/T)=t by field_simp] at he
      rw [he]
      dsimp [F,d06ChiTimePowerProfile,a03ProfileProduct,β,τ]
      rw [show T*(t/T)=t by field_simp]
      ring

theorem d06ExtremeMomentError_eventually_eq_difference
    (R : ℝ) (ρ : Fin 4 → ℝ → ℝ) (a : Fin 4 → ℝ)
    (hρs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2) :
    ∀ᶠ T : ℝ in atTop,∀ σ : Fin 2 → ℂ,(∀ i,‖σ i‖≤R) →
      d06ExtremeMomentError T σ ρ Φ=
        d06ExtremeMinusShiftedMoment T σ ρ Φ-d06ExtremeOneSidedMoment T σ ρ Φ := by
  filter_upwards [eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max 1 (max R (2*R))))] with T hT hL
  intro σ hσ
  have hR : 0≤R := (norm_nonneg (σ 0)).trans (hσ 0)
  have hactual := d06ExtremeMinusShiftedIntegrand_integrable_of_norm_bound hT
    ((le_max_left _ _).trans hL) R ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
    σ hσ ρ a hρs Φ hΦ.continuous hΦs
  have hmodel := d06ExtremeOneSidedIntegrand_integrable hT hR
    ((le_max_right _ _).trans ((le_max_right _ _).trans hL)) ρ a hρs Φ hΦ hΦs σ hσ
  unfold d06ExtremeMomentError d06ExtremeMinusShiftedMoment d06ExtremeOneSidedMoment
  rw [← integral_sub hactual hmodel]
  apply integral_congr_ae
  filter_upwards [] with t
  ring

end
end Sechstmoment
