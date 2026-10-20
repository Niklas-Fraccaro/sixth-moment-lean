import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic


namespace Sechstmoment

open Real Complex MeasureTheory
open scoped Topology

noncomputable section

theorem one_add_abs_pow_le (n : ℕ) (x : ℝ) :
    (1+|x|)^n ≤ 2^n*(1+|x|^n) := by
  by_cases hx : |x| ≤ 1
  · calc
      _ ≤ (2:ℝ)^n := by gcongr; linarith
      _ ≤ _ := by nlinarith [pow_nonneg (abs_nonneg x) n, pow_nonneg (by norm_num : (0:ℝ) ≤ 2) n]
  · calc
      _ ≤ (2*|x|)^n := by gcongr; linarith
      _ = 2^n*|x|^n := mul_pow _ _ _
      _ ≤ _ := by nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) n]

theorem linear_exp_gaussian_le (c x : ℝ) :
    Real.exp (c*|x|-x^2) ≤ Real.exp (c^2)*Real.exp (-(1/2)*x^2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (|x|-c), sq_nonneg c, sq_abs x]

theorem gaussianPolynomialExponential_integrable (n : ℕ) (c : ℝ) :
    Integrable (fun x : ℝ => (1+|x|)^n*Real.exp (c*|x|-x^2)) := by
  have hG := integrable_exp_neg_mul_sq (b := (1/2:ℝ)) (by norm_num)
  have hPG : Integrable (fun x : ℝ => |x|^n*Real.exp (-(1/2)*x^2)) := by
    have h := (integrable_rpow_mul_exp_neg_mul_sq (b := (1/2:ℝ)) (s := (n:ℝ))
      (by norm_num) (by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith)).norm
    simpa only [Real.rpow_natCast, Real.norm_eq_abs, abs_mul, abs_pow, Real.abs_exp] using h
  have hsum : Integrable (fun x : ℝ => (1+|x|^n)*Real.exp (-(1/2)*x^2)) := by
    convert hG.add hPG using 1
    ext x
    simp only [Pi.add_apply]
    ring
  apply (hsum.const_mul (2^n*Real.exp (c^2))).mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (2^n*(1+|x|^n)) * (Real.exp (c^2)*Real.exp (-(1/2)*x^2)) := by
      exact mul_le_mul (one_add_abs_pow_le n x) (linear_exp_gaussian_le c x)
        (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

end

end Sechstmoment
