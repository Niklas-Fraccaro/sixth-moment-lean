import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic
import Sechstmoment.Numerator.Polar.RemainderMajorant

/-!
# Uniform power decay of the actual left Mellin remainder

Bounded normalized shifts are eventually small in the genuine raw variables.
The actual log(T)^48 contour bound is absorbed by T^(δ/2), leaving a genuine
negative power uniformly for t≥T and all amplifier contour heights.
-/

namespace Sechstmoment

open Real Complex Filter Set
open scoped BigOperators Topology

noncomputable section

theorem rawMomentShifts_uniform_eventually_small {R ε : ℝ}
    (_hR : 0 ≤ R) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ σ : MomentShifts, (∀ j : Fin 4, ‖σ j‖ ≤ R) →
      ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ ε := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (R/ε))]
    with T hT hL σ hσ j
  have hLp : 0 < Real.log T := Real.log_pos hT
  rw [rawMomentShifts,norm_div,Complex.norm_real,Real.norm_of_nonneg hLp.le]
  apply (div_le_div_of_nonneg_right (hσ j) hLp.le).trans
  rw [div_le_iff₀ hLp]
  have h := (div_lt_iff₀ hε).mp hL
  linarith

theorem log_pow_48_eventually_le_rpow {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, (Real.log T)^48 ≤ T^(δ/2) := by
  have h := (isLittleO_log_rpow_rpow_atTop (48:ℝ)
    (show 0 < δ/2 by linarith)).bound (c := 1) (by norm_num)
  filter_upwards [h,eventually_gt_atTop (1:ℝ)] with T hT hpos
  simpa only [Real.rpow_ofNat,Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (Real.log T)^48),
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ T) (δ/2)),one_mul] using hT

theorem polarMellinRemainderIntegral_uniform_eventually_power_decay {R δ κ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 < δ) (hδ1 : δ < 1/4) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ σ : MomentShifts, (∀ j : Fin 4, ‖σ j‖ ≤ R) →
      (∀ k : PurePolarIndex, κ ≤ ‖Source.normalizedPurePolarRoot σ k‖) →
      ∀ (m : Fin 6) (u v : ℂ), δ ≤ u.re → δ ≤ v.re →
      ∀ t : ℝ, T ≤ t →
        ‖polarMellinRemainderIntegral T σ m u v (t/(2*Real.pi)) δ‖ ≤ C*T^(-δ/2) := by
  obtain ⟨B,hB0,hB⟩ := polarMellinRemainderIntegral_uniform_log_bound hδ hδ1 hκ
  refine ⟨B*(2*Real.pi)^δ,by positivity,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    rawMomentShifts_uniform_eventually_small hR (show 0 < δ/4 by linarith),
    log_pow_48_eventually_le_rpow hδ] with T hT hL hraw hlog
  intro σ hσ hgap m u v hu hv t ht
  have hTp : 0 < T := by linarith
  have htp : 0 < t := hTp.trans_le ht
  have hp : 0 < 2*Real.pi := by positivity
  have hscale : (t/(2*Real.pi))^(-δ) ≤ (T/(2*Real.pi))^(-δ) :=
    Real.rpow_le_rpow_of_nonpos (div_pos hTp hp)
      (div_le_div_of_nonneg_right ht hp.le) (by linarith)
  have he : (T/(2*Real.pi))^(-δ) = T^(-δ)*(2*Real.pi)^δ := by
    rw [Real.div_rpow hTp.le hp.le,Real.rpow_neg hp.le]
    simp only [div_eq_mul_inv,inv_inv]
  have hpow : T^(δ/2)*T^(-δ) = T^(-δ/2) := by
    rw [← Real.rpow_add hTp]
    congr 1
    ring
  calc
    _ ≤ B*(Real.log T)^48*(t/(2*Real.pi))^(-δ) :=
      hB T hT hL σ hgap (hraw σ hσ) m u v hu hv _ (div_pos htp hp)
    _ ≤ B*T^(δ/2)*(T/(2*Real.pi))^(-δ) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hlog hB0) hscale
        (Real.rpow_nonneg (div_nonneg htp.le hp.le) _) (by positivity)
    _ = _ := by
      rw [he]
      calc
        _ = (B*(2*Real.pi)^δ)*(T^(δ/2)*T^(-δ)) := by ac_rfl
        _ = _ := by rw [hpow]

end

end Sechstmoment
