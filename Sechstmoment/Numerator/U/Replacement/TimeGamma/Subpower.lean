import Sechstmoment.Numerator.U.Replacement.TimeGamma.Gaussian
import Sechstmoment.Numerator.U.Separation.LogarithmicMellinWeights

namespace Sechstmoment.Source
open Complex Set Metric Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

theorem bblrGaussianTimeAmplitude_uniform_subpower_derivatives
    {c ε κ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hε : 2*c < ε) (hκ : 0 < κ) :
    ∃ B : ℕ → ℝ, (∀ n, 0 ≤ B n) ∧
      ∀ (T A : ℝ) (σ α : MomentShifts) (v x : ℝ),
      1 < T → 1 ≤ Real.log T → 0 ≤ A → 8*(A+1) ≤ T →
      (∀ j, ‖α j‖ ≤ A) →
      (∀ k : PurePolarIndex, κ ≤ ‖normalizedPurePolarRoot σ k‖) →
      192*(‖(c : ℂ)+(v : ℂ)*I‖+‖(c : ℂ)+(v : ℂ)*I‖^2) < T →
      x ∈ Icc (1 : ℝ) 2 → ∀ n : ℕ,
      ‖iteratedDeriv n (bblrGaussianTimeAmplitude T σ α ((c : ℂ)+(v : ℂ)*I)) x‖ ≤
        B n*T^ε := by
  obtain ⟨D,hD,hd⟩ := bblrGaussianTimeAmplitude_uniform_derivative_bounds hc
  let L : ℝ := ((48 : ℕ).factorial : ℝ)/(ε-2*c)^48*Real.exp (ε-2*c)
  let H : ℝ := Real.exp (c^2)*(1+|c|)^48*(1+1/κ^2)^24
  let B : ℕ → ℝ := fun n => ((n.factorial : ℝ)/(1/4 : ℝ)^n)*D*4*H*L
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨B,fun n => by dsimp [B]; positivity,?_⟩
  intro T A σ α v x hT hlog hA hAT hα hroot hlarge hx n
  have hT0 : 0 < T := zero_lt_one.trans hT
  have hGC := polarGaussianConstant_nonneg T σ c
  have hpow : (2*T)^(2*c) ≤ 4*T^(2*c) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hT0.le]
    have h2 : (2 : ℝ)^(2*c) ≤ 4 := by
      calc
        _ ≤ (2 : ℝ)^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = _ := by norm_num
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have hg : polarGaussianConstant T σ c ≤ H*(Real.log T)^48 :=
    polarGaussianConstant_log_growth hT hlog hκ σ c hroot
  have hl : (Real.log T)^48 ≤ L*T^(ε-2*c) := by
    calc
      _ ≤ (1+Real.log T)^48 := pow_le_pow_left₀ (by linarith) (by linarith) 48
      _ ≤ _ := Sechstmoment.logarithmic_power_le_rpow (by linarith) hT.le 48
  have he : T^(2*c)*T^(ε-2*c) = T^ε := by
    rw [← Real.rpow_add hT0]
    congr 1
    ring
  calc
    _ ≤ ((n.factorial : ℝ)/(1/4 : ℝ)^n)*D*(2*T)^(2*c)*polarGaussianConstant T σ c :=
      hd n T A σ α v x hA hAT hα hlarge hx
    _ ≤ ((n.factorial : ℝ)/(1/4 : ℝ)^n)*D*(4*T^(2*c))*(H*(L*T^(ε-2*c))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hpow (by positivity)
      · exact hg.trans (mul_le_mul_of_nonneg_left hl hH)
      · exact hGC
      · positivity
    _ = B n*T^ε := by dsimp [B]; rw [show
        ((n.factorial : ℝ)/(1/4 : ℝ)^n)*D*(4*T^(2*c))*(H*(L*T^(ε-2*c))) =
        (((n.factorial : ℝ)/(1/4 : ℝ)^n)*D*4*H*L)*(T^(2*c)*T^(ε-2*c)) by ring,he]

end
end Sechstmoment.Source
