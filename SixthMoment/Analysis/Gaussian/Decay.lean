import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Tactic
import SixthMoment.Analysis.Gaussian.Integrability


namespace SixthMoment

open Real Complex Filter
open scoped Topology

noncomputable section

theorem gaussianPolynomialExponential_tendsto_zero (n : ℕ) (c : ℝ) :
    Tendsto (fun x : ℝ => (1+|x|)^n*Real.exp (c*|x|-x^2))
      (cocompact ℝ) (𝓝 0) := by
  have hG : Tendsto (fun x : ℝ => Real.exp (-(1/2)*x^2)) (cocompact ℝ) (𝓝 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (a := (1/2:ℝ)) (by norm_num) 0
  have hPG : Tendsto (fun x : ℝ => |x|^n*Real.exp (-(1/2)*x^2))
      (cocompact ℝ) (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (a := (1/2:ℝ)) (by norm_num) (n:ℝ)
  have hsum : Tendsto (fun x : ℝ => (1+|x|^n)*Real.exp (-(1/2)*x^2))
      (cocompact ℝ) (𝓝 0) := by
    simpa only [add_mul, one_mul, add_zero] using hG.add hPG
  have hlim : Tendsto (fun x : ℝ =>
      (2^n*Real.exp (c^2))*((1+|x|^n)*Real.exp (-(1/2)*x^2)))
      (cocompact ℝ) (𝓝 0) := by
    simpa only [mul_zero] using hsum.const_mul (2^n*Real.exp (c^2))
  apply squeeze_zero (fun x => by positivity) _ hlim
  intro x
  calc
    _ ≤ (2^n*(1+|x|^n)) * (Real.exp (c^2)*Real.exp (-(1/2)*x^2)) :=
      mul_le_mul (one_add_abs_pow_le n x) (linear_exp_gaussian_le c x)
        (Real.exp_pos _).le (by positivity)
    _ = _ := by ac_rfl

end

end SixthMoment
