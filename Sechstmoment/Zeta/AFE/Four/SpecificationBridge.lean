import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Sechstmoment.Zeta.AFE.Four.Specification


namespace Sechstmoment.Source
open Complex Set Filter
open scoped Topology
noncomputable section

theorem eventually_rawMomentShifts_norm_le_quarter
    (K : Set MomentShifts) (hK : IsCompact K) :
    ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ j : Fin 4,
      ‖rawMomentShifts T σ j‖ ≤ (1 / 4 : ℝ) := by
  obtain ⟨B, hB, hbound⟩ := hK.isBounded.exists_pos_norm_le
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (4 * B))] with T hlog
  intro σ hσ j
  have hlogpos : 0 < Real.log T := by linarith
  have hσj : ‖σ j‖ ≤ B := (norm_le_pi_norm σ j).trans (hbound σ hσ)
  change ‖σ j / (Real.log T : ℂ)‖ ≤ (1 / 4 : ℝ)
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hlogpos.le]
  apply (div_le_iff₀ hlogpos).mpr
  linarith

theorem bblrFixedAFE_of_uniform_smallShifts
    (hsmall : ∀ G : ℂ → ℂ, BBLREntireWeight G (fun _ => 0) →
      ∀ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ t : ℝ, 16 ≤ t → ∀ α : MomentShifts,
          (∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ)) →
          ‖bblrAFEDiscrepancy G α t‖ ≤ C * t ^ (-(A : ℝ))) :
    BBLRv1FixedApproximateFEInput := by
  intro G hG K hK A
  obtain ⟨C, hC, hbound⟩ := hsmall G hG A
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_rawMomentShifts_norm_le_quarter K hK,
    eventually_ge_atTop (16 : ℝ)] with T hshifts hT
  intro σ hσ t ht
  have ht16 : 16 ≤ t := hT.trans ht.1
  have hTpos : 0 < T := by linarith
  have hpower : t ^ (-(A : ℝ)) ≤ T ^ (-(A : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hTpos ht.1 (neg_nonpos.mpr (Nat.cast_nonneg A))
  exact (hbound t ht16 (rawMomentShifts T σ) (hshifts σ hσ)).trans
    (mul_le_mul_of_nonneg_left hpower hC)

end
end Sechstmoment.Source
