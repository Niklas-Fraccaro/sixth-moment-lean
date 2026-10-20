import Sechstmoment.Denominator.Unbalanced.ActualCircleFubini

namespace Sechstmoment
open MeasureTheory Set Complex Polynomial Filter Metric
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 800000

theorem d04_shifted_zeta_nonpole_of_norm_le {T : ℝ} {s z : ℂ}
    (hL : 1 ≤ Real.log T) (hs : 1 < |s.im|) (hz : ‖z‖ ≤ Real.log T) :
    s + z / (Real.log T : ℂ) ≠ 1 := by
  have hLp : 0 < Real.log T := zero_lt_one.trans_le hL
  have hzim : |z.im| ≤ Real.log T := (Complex.abs_im_le_norm z).trans hz
  intro h
  have hi := congrArg Complex.im h
  simp only [add_im,Complex.div_ofReal_im,one_im] at hi
  have habs : |s.im| = |z.im| / Real.log T := by
    have he : s.im = -(z.im / Real.log T) := by linarith
    rw [he,abs_neg,abs_div,abs_of_pos hLp]
  have hdiv : |z.im| / Real.log T ≤ 1 :=
    (div_le_iff₀ hLp).mpr (by simpa using hzim)
  linarith

theorem d04UnbalancedShiftedIntegrand_continuousOn_of_norm_bound {T : ℝ}
    (hT : 1<T) (hL : 1≤Real.log T) (R : ℝ) (hRL : R≤Real.log T)
    (σ : Fin 2 → ℂ) (hσ : ∀ i, ‖σ i‖≤R)
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) :
    ContinuousOn (fun t : ℝ => (Φ (t/T) : ℂ) * (criticalChi t)⁻¹ *
      zetaCPlus T t (σ 0) * zetaCMinus T t (σ 1) * d04UnbalancedAmplifier T t ρ)
      (Icc T (2*T)) := by
  have hplus : ContinuousOn (fun t : ℝ => zetaCPlus T t (σ 0)) (Icc T (2*T)) := by
    intro t ht
    unfold zetaCPlus shiftedZetaGenerator
    have hs : 1 < |(criticalLinePoint t).im| := by
      rw [criticalLinePoint_im,abs_of_pos (zero_lt_one.trans (hT.trans_le ht.1))]
      exact hT.trans_le ht.1
    have hz := (differentiableAt_riemannZeta
      (d04_shifted_zeta_nonpole_of_norm_le hL hs ((hσ 0).trans hRL))).continuousAt
    have hm : ContinuousWithinAt (fun u : ℝ => criticalLinePoint u +
        σ 0/(Real.log T : ℂ)) (Icc T (2*T)) t := by
      unfold criticalLinePoint
      fun_prop
    exact continuousWithinAt_const.mul
      (hz.comp_continuousWithinAt (f := fun u : ℝ => criticalLinePoint u +
        σ 0/(Real.log T : ℂ)) (x := t) hm)
  have hminus : ContinuousOn (fun t : ℝ => zetaCMinus T t (σ 1)) (Icc T (2*T)) := by
    intro t ht
    unfold zetaCMinus shiftedZetaGenerator
    have hs : 1 < |(1-criticalLinePoint t).im| := by
      simp only [sub_im,one_im,criticalLinePoint_im,zero_sub,abs_neg]
      rw [abs_of_pos (zero_lt_one.trans (hT.trans_le ht.1))]
      exact hT.trans_le ht.1
    have hz := (differentiableAt_riemannZeta
      (d04_shifted_zeta_nonpole_of_norm_le hL hs ((hσ 1).trans hRL))).continuousAt
    have hm : ContinuousWithinAt (fun u : ℝ => 1-criticalLinePoint u +
        σ 1/(Real.log T : ℂ)) (Icc T (2*T)) t := by
      unfold criticalLinePoint
      fun_prop
    exact continuousWithinAt_const.mul
      (hz.comp_continuousWithinAt (f := fun u : ℝ => 1-criticalLinePoint u +
        σ 1/(Real.log T : ℂ)) (x := t) hm)
  have hcut : Continuous (fun t : ℝ => (Φ (t/T) : ℂ) * (criticalChi t)⁻¹) :=
    (by fun_prop : Continuous (fun t : ℝ => (Φ (t/T) : ℂ))).mul
      d04_criticalChi_inv_continuous
  exact ((hcut.continuousOn.mul hplus).mul hminus).mul
    (d04UnbalancedAmplifier_continuous hT ρ A hρsupport).continuousOn

theorem d04UnbalancedShiftedIntegrand_integrable_of_norm_bound {T : ℝ}
    (hT : 1<T) (hL : 1≤Real.log T) (R : ℝ) (hRL : R≤Real.log T)
    (σ : Fin 2 → ℂ) (hσ : ∀ i, ‖σ i‖≤R)
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc 1 2) :
    Integrable (fun t : ℝ => (Φ (t/T) : ℂ) * (criticalChi t)⁻¹ *
      zetaCPlus T t (σ 0) * zetaCMinus T t (σ 1) * d04UnbalancedAmplifier T t ρ) := by
  have hc := d04UnbalancedShiftedIntegrand_continuousOn_of_norm_bound
    hT hL R hRL σ hσ ρ A hρsupport Φ hΦ
  have hci : IntegrableOn (fun t : ℝ => (Φ (t/T) : ℂ) * (criticalChi t)⁻¹ *
      zetaCPlus T t (σ 0) * zetaCMinus T t (σ 1) * d04UnbalancedAmplifier T t ρ)
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

theorem d04UnbalancedShiftedIntegrand_eventually_integrable_on_shiftBox
    (R : ℝ) (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i))
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc 1 2) :
    ∀ᶠ T : ℝ in atTop, ∀ σ : Fin 2 → ℂ, (∀ i, ‖σ i‖≤R) →
      Integrable (fun t : ℝ => (Φ (t/T) : ℂ) * (criticalChi t)⁻¹ *
        zetaCPlus T t (σ 0) * zetaCMinus T t (σ 1) * d04UnbalancedAmplifier T t ρ) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 R))] with T hT hL
  intro σ hσ
  exact d04UnbalancedShiftedIntegrand_integrable_of_norm_bound hT
    ((le_max_left 1 R).trans hL) R ((le_max_right 1 R).trans hL)
    σ hσ ρ A hρsupport Φ hΦ.continuous hΦs

end
end Sechstmoment
