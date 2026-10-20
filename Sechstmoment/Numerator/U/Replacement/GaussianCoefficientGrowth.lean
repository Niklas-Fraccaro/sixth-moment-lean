import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Sechstmoment.Numerator.U.Replacement.GaussianBasis


namespace Sechstmoment.Source
open Complex
open scoped BigOperators
open Classical
noncomputable section

def normalizedPurePolarRoot (σ : MomentShifts) (k : PurePolarIndex) : ℂ :=
  -(bblrSixShifts σ k.1 (purePolarLeft k.2.1)+
    bblrSixShifts σ k.1 (purePolarRight k.2.2))/2

theorem bblrSixShifts_raw (T : ℝ) (σ : MomentShifts) (k : Fin 6) (j : Fin 4) :
    bblrSixShifts (rawMomentShifts T σ) k j =
      bblrSixShifts σ k j/(Real.log T : ℂ) := by
  fin_cases k <;> fin_cases j <;> simp [bblrSixShifts, rawMomentShifts] <;> ring

theorem purePolarRoot_normalized (T : ℝ) (σ : MomentShifts) (k : PurePolarIndex) :
    purePolarRoot T σ k = normalizedPurePolarRoot σ k/(Real.log T : ℂ) := by
  unfold purePolarRoot normalizedPurePolarRoot
  rw [bblrSixShifts_raw, bblrSixShifts_raw]
  ring

theorem purePolarRoot_inverse_sq_norm {T δ : ℝ} (hT : 1 < T) (hδ : 0 < δ)
    (σ : MomentShifts) (k : PurePolarIndex) (hρ : δ ≤ ‖normalizedPurePolarRoot σ k‖) :
    ‖((purePolarRoot T σ k)^2)⁻¹‖ ≤ (Real.log T)^2/δ^2 := by
  have hL : 0 < Real.log T := Real.log_pos hT
  have hρ0 : 0 < ‖normalizedPurePolarRoot σ k‖ := hδ.trans_le hρ
  rw [purePolarRoot_normalized, norm_inv, norm_pow, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  calc
    ((‖normalizedPurePolarRoot σ k‖/Real.log T)^2)⁻¹ =
        (Real.log T)^2/‖normalizedPurePolarRoot σ k‖^2 := by
      rw [div_pow, inv_div]
    _ ≤ (Real.log T)^2/δ^2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith

theorem polarPoleBasisWeights_log_growth {T δ : ℝ} (hT : 1 < T)
    (hL : 1 ≤ Real.log T) (hδ : 0 < δ) (σ : MomentShifts)
    (hρ : ∀ k : PurePolarIndex, δ ≤ ‖normalizedPurePolarRoot σ k‖) :
    ∑ i : Fin 25, ‖polarPoleBasisWeights T σ i‖ ≤
      (1+48*(1+1/δ^2)^24)*(Real.log T)^48 := by
  have hL0 : 0 ≤ Real.log T := (Real.log_pos hT).le
  have hLsq : 1 ≤ (Real.log T)^2 := by nlinarith
  have hp : ∏ k : PurePolarIndex, (1+‖((purePolarRoot T σ k)^2)⁻¹‖) ≤
      (1+1/δ^2)^24*(Real.log T)^48 := by
    calc
      _ ≤ ∏ _k : PurePolarIndex, ((1+1/δ^2)*(Real.log T)^2) := by
        apply Finset.prod_le_prod₀
        · intro k hk
          positivity
        · intro k hk
          have hi := purePolarRoot_inverse_sq_norm hT hδ σ k (hρ k)
          have he : (Real.log T)^2/δ^2 = (1/δ^2)*(Real.log T)^2 := by ring
          rw [he] at hi
          nlinarith
      _ = (1+1/δ^2)^24*(Real.log T)^48 := by
        simp [PurePolarIndex, mul_pow, ← pow_mul]
  have hLp : 1 ≤ (Real.log T)^48 := one_le_pow₀ hL
  apply (polarPoleBasisWeights_norm_sum_le T σ).trans
  nlinarith

end
end Sechstmoment.Source
