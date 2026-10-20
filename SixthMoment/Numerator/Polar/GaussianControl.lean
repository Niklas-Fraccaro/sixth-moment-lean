import Mathlib.Tactic
import SixthMoment.Analysis.Gaussian.Integrability
import SixthMoment.Numerator.Polar.PoleKiller


namespace SixthMoment

open Real Complex MeasureTheory
open scoped BigOperators Topology

noncomputable section

def polarKillingCoefficient (ρ : ℂ) : ℂ := if ρ = 0 then 0 else (ρ^2)⁻¹

theorem polarPoleKillingFactor_eq_linear_in_sq (ρ z : ℂ) :
    polarPoleKillingFactor ρ z = 1-polarKillingCoefficient ρ*z^2 := by
  by_cases hρ : ρ = 0
  · simp only [polarPoleKillingFactor, polarKillingCoefficient, hρ, ite_true, zero_mul, sub_zero]
  · simp only [polarPoleKillingFactor, polarKillingCoefficient, hρ, ite_false,
      div_eq_mul_inv]
    ring

theorem polarPoleKillingFactor_norm_polynomial_le (ρ z : ℂ) :
    ‖polarPoleKillingFactor ρ z‖ ≤
      (1+‖polarKillingCoefficient ρ‖)*(1+‖z‖)^2 := by
  rw [polarPoleKillingFactor_eq_linear_in_sq]
  calc
    _ ≤ ‖(1:ℂ)‖+‖polarKillingCoefficient ρ*z^2‖ := norm_sub_le _ _
    _ = 1+‖polarKillingCoefficient ρ‖*‖z‖^2 := by
      rw [norm_one, norm_mul, Complex.norm_pow]
    _ ≤ (1+‖polarKillingCoefficient ρ‖)*(1+‖z‖^2) := by
      nlinarith [norm_nonneg (polarKillingCoefficient ρ), sq_nonneg ‖z‖]
    _ ≤ _ := by
      gcongr
      nlinarith [norm_nonneg z]

def polarGaussianConstant (T : ℝ) (σ : MomentShifts) (c : ℝ) : ℝ :=
  Real.exp (c^2) * (1+|c|)^48 *
    ∏ k : PurePolarIndex, (1+‖polarKillingCoefficient (purePolarRoot T σ k)‖)

theorem polarGaussianConstant_nonneg (T : ℝ) (σ : MomentShifts) (c : ℝ) :
    0 ≤ polarGaussianConstant T σ c := by
  unfold polarGaussianConstant
  positivity

theorem polarPoleKiller_vertical_norm_le (T : ℝ) (σ : MomentShifts) (c v : ℝ) :
    ‖polarPoleKiller T σ ((c:ℂ)+(v:ℂ)*I)‖ ≤
      polarGaussianConstant T σ c * (1+|v|)^48 * Real.exp (-v^2) := by
  let z : ℂ := (c:ℂ)+(v:ℂ)*I
  have hz : ‖z‖ ≤ |c|+|v| := by
    exact (norm_add_le _ _).trans_eq (by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one])
  have hp : ‖∏ k : PurePolarIndex, polarPoleKillingFactor (purePolarRoot T σ k) z‖ ≤
      (∏ k : PurePolarIndex, (1+‖polarKillingCoefficient (purePolarRoot T σ k)‖)) *
        (1+‖z‖)^48 := by
    calc
      _ ≤ ∏ k : PurePolarIndex, ‖polarPoleKillingFactor (purePolarRoot T σ k) z‖ :=
        Finset.norm_prod_le _ _
      _ ≤ ∏ k : PurePolarIndex,
          ((1+‖polarKillingCoefficient (purePolarRoot T σ k)‖)*(1+‖z‖)^2) :=
        Finset.prod_le_prod₀ (fun k _ => norm_nonneg _)
          (fun k _ => polarPoleKillingFactor_norm_polynomial_le _ _)
      _ = _ := by
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
        rw [← pow_mul]
  have hpol : (1+‖z‖)^48 ≤ (1+|c|)^48*(1+|v|)^48 := by
    rw [← mul_pow]
    gcongr
    nlinarith [mul_nonneg (abs_nonneg c) (abs_nonneg v)]
  have he : ‖Complex.exp (z^2)‖ = Real.exp (c^2)*Real.exp (-v^2) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    congr 1
    simp [z, pow_two]
    ring
  unfold polarPoleKiller
  change ‖Complex.exp (z^2)*(∏ k : PurePolarIndex,
    polarPoleKillingFactor (purePolarRoot T σ k) z)‖ ≤ _
  rw [norm_mul, he]
  calc
    _ ≤ (Real.exp (c^2)*Real.exp (-v^2)) *
        ((∏ k : PurePolarIndex, (1+‖polarKillingCoefficient (purePolarRoot T σ k)‖)) *
          ((1+|c|)^48*(1+|v|)^48)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hp.trans (mul_le_mul_of_nonneg_left hpol (by positivity))
    _ = _ := by unfold polarGaussianConstant; ac_rfl

theorem polarPoleKiller_vertical_integrable (T : ℝ) (σ : MomentShifts) (c : ℝ) :
    Integrable (fun v : ℝ => polarPoleKiller T σ ((c:ℂ)+(v:ℂ)*I)) := by
  have hG := (gaussianPolynomialExponential_integrable 48 0).const_mul
    (polarGaussianConstant T σ c)
  apply hG.mono'
  · exact ((polarPoleKiller_differentiable T σ).continuous.comp (by fun_prop)).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro v
    simpa only [zero_mul, zero_sub, mul_assoc] using polarPoleKiller_vertical_norm_le T σ c v

end

end SixthMoment
