import Mathlib.Tactic
import SixthMoment.Numerator.Polar.GaussianControl
import SixthMoment.Numerator.U.Replacement.GaussianCoefficientGrowth


namespace SixthMoment

open Real Complex
open scoped BigOperators

noncomputable section

theorem polarKillingCoefficient_eq_inverse_sq (ρ : ℂ) :
    polarKillingCoefficient ρ = (ρ^2)⁻¹ := by
  unfold polarKillingCoefficient
  by_cases hρ : ρ = 0
  · simp [hρ]
  · simp only [ite_eq_right hρ]

theorem polarKillingCoefficient_product_log_growth {T κ : ℝ}
    (hT : 1 < T) (hL : 1 ≤ Real.log T) (hκ : 0 < κ) (σ : MomentShifts)
    (hρ : ∀ k : PurePolarIndex, κ ≤ ‖Source.normalizedPurePolarRoot σ k‖) :
    (∏ k : PurePolarIndex, (1+‖polarKillingCoefficient (purePolarRoot T σ k)‖)) ≤
      (1+1/κ^2)^24*(Real.log T)^48 := by
  have hLsq : 1 ≤ (Real.log T)^2 := by nlinarith
  calc
    _ ≤ ∏ _k : PurePolarIndex, ((1+1/κ^2)*(Real.log T)^2) := by
      apply Finset.prod_le_prod₀
      · intro k _
        positivity
      · intro k _
        rw [polarKillingCoefficient_eq_inverse_sq]
        have hi := Source.purePolarRoot_inverse_sq_norm hT hκ σ k (hρ k)
        have he : (Real.log T)^2/κ^2 = (1/κ^2)*(Real.log T)^2 := by ring
        rw [he] at hi
        nlinarith
    _ = _ := by simp [PurePolarIndex,mul_pow,← pow_mul]

theorem polarGaussianConstant_log_growth {T κ : ℝ}
    (hT : 1 < T) (hL : 1 ≤ Real.log T) (hκ : 0 < κ)
    (σ : MomentShifts) (c : ℝ)
    (hρ : ∀ k : PurePolarIndex, κ ≤ ‖Source.normalizedPurePolarRoot σ k‖) :
    polarGaussianConstant T σ c ≤
      (Real.exp (c^2)*(1+|c|)^48*(1+1/κ^2)^24)*(Real.log T)^48 := by
  unfold polarGaussianConstant
  calc
    _ ≤ (Real.exp (c^2)*(1+|c|)^48)*
        ((1+1/κ^2)^24*(Real.log T)^48) :=
      mul_le_mul_of_nonneg_left (polarKillingCoefficient_product_log_growth hT hL hκ σ hρ)
        (by positivity)
    _ = _ := by ac_rfl

end

end SixthMoment
