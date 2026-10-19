import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Sechstmoment.Numerator.U.Replacement.DualErrorGaussian

namespace Sechstmoment.Source
open Sechstmoment Complex Set Metric Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000

theorem bblrDualLeadingMultiplier_measurable (T : ℝ) (σ : MomentShifts) :
    Measurable (bblrDualLeadingMultiplier T σ) := by
  unfold bblrDualLeadingMultiplier
  simp_rw [Complex.cpow_def]
  apply Measurable.ite (by measurability)
  · exact measurable_const
  · fun_prop

theorem bblrDualLeadingMultiplier_time_measurable (T : ℝ) (σ : MomentShifts) :
    Measurable (fun t : ℝ => bblrDualLeadingMultiplier T σ (t/T)) :=
  (bblrDualLeadingMultiplier_measurable T σ).comp (by fun_prop)

theorem bblrDualLeadingMultiplier_time_eq {T : ℝ} (hT : T≠0)
    (σ : MomentShifts) (t : ℝ) :
    bblrDualLeadingMultiplier T σ (t/T)=
      (t/(2*Real.pi):ℂ)^(-∑ j : Fin 4, rawMomentShifts T σ j) := by
  unfold bblrDualLeadingMultiplier
  congr 1
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hT]

theorem bblrDualLeadingMultiplier_uniform_normalized_bound
    (K : Set MomentShifts) (hK : IsCompact K) :
    ∃ D : ℝ, 0<D ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ t∈Icc T (2*T),
      ‖bblrDualLeadingMultiplier T σ (t/T)‖≤D := by
  obtain ⟨B,hB⟩ := hK.isBounded.exists_norm_le
  let R := max B 0
  have hR : 0≤R := le_max_right _ _
  refine ⟨48*Real.exp (4*R),by positivity,?_⟩
  filter_upwards [a03DualPhaseReplacementError_uniform_complex_bound hR,
    bblrTimeDualMultiplier_uniform_complex_bound hR,
    eventually_gt_atTop (0:ℝ),eventually_ge_atTop (a03DualPhaseErrorConstant R)]
      with T herr hbound hT hC
  intro σ hσ t ht
  have hσR (j : Fin 4) : ‖σ j‖≤R := ((norm_le_pi_norm σ j).trans (hB σ hσ)).trans (le_max_left _ _)
  have hx : t/T∈Icc (1:ℝ) 2 :=
    ⟨(le_div_iff₀ hT).mpr (by simpa using ht.1), (div_le_iff₀ hT).mpr (by linarith [ht.2])⟩
  have he := herr σ hσR (t/T) hx ((t/T:ℝ):ℂ) (mem_closedBall_self (by norm_num : (0:ℝ)≤1/4))
  have hb := hbound σ hσR ((t/T:ℝ):ℂ) (by simpa using ⟨by linarith [hx.1],by linarith [hx.2]⟩) (by simp)
  have hn := norm_sub_le (bblrTimeDualMultiplier T σ ((t/T:ℝ):ℂ)) (a03DualPhaseReplacementError T σ ((t/T:ℝ):ℂ))
  have hid : bblrTimeDualMultiplier T σ ((t/T:ℝ):ℂ)-a03DualPhaseReplacementError T σ ((t/T:ℝ):ℂ)=
      bblrDualLeadingMultiplier T σ (t/T) := by
    unfold a03DualPhaseReplacementError
    rw [a03DualLeadingPhase_ofReal]
    unfold bblrDualLeadingMultiplier
    ring
  rw [hid] at hn
  have hsmall : a03DualPhaseErrorConstant R/T≤1 := (div_le_iff₀ hT).mpr (by simpa using hC)
  have hE : (32*Real.exp (4*R)*a03DualPhaseErrorConstant R)/T≤32*Real.exp (4*R) := by
    calc
      _=(32*Real.exp (4*R))*(a03DualPhaseErrorConstant R/T) := by ring
      _≤_ := by nlinarith [Real.exp_pos (4*R),hsmall]
  exact hn.trans (by linarith)

end
end Sechstmoment.Source
