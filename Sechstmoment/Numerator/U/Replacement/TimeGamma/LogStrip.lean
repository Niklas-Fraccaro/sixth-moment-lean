import Sechstmoment.Numerator.U.Replacement.TimeGamma.Subpower

namespace Sechstmoment.Source
open Complex Set Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

private theorem eventually_constant_sqrt_lt (C : ℝ) (hC : 0 < C) :
    ∀ᶠ T : ℝ in atTop, C*T^(1/2 : ℝ) < T := by
  have hlim : Tendsto (fun T : ℝ => T^(1/2 : ℝ)/T) atTop (𝓝 0) := by
    have hh := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [show -(1/2 : ℝ) = 1/2-1 by ring,Real.rpow_sub hT,Real.rpow_one]
  filter_upwards [hlim.eventually_lt_const (one_div_pos.mpr hC),
    eventually_gt_atTop (0 : ℝ)] with T hT hTpos
  rw [div_lt_iff₀ hTpos] at hT
  have hh := mul_lt_mul_of_pos_left hT hC
  have he : C*(1/C*T)=T := by field_simp
  rw [he] at hh
  exact hh

theorem bblrGamma_logarithmic_strip_large {c θ : ℝ}
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hθ : 0 ≤ θ) :
    ∀ᶠ T : ℝ in atTop, ∀ v : ℝ, |v| ≤ θ*Real.log T →
      192*(‖(c : ℂ)+(v : ℂ)*I‖+‖(c : ℂ)+(v : ℂ)*I‖^2) < T := by
  let K : ℝ := 1+θ
  let L : ℝ := ((2 : ℕ).factorial : ℝ)/(1/2 : ℝ)^2*Real.exp (1/2)
  let C : ℝ := 192*(K+K^2)*L
  have hK : 0 < K := by dsimp [K]; linarith
  have hL : 0 < L := by dsimp [L]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  filter_upwards [eventually_constant_sqrt_lt C hC,eventually_ge_atTop (1 : ℝ)] with T hbound hT
  intro v hv
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  let z : ℂ := (c : ℂ)+(v : ℂ)*I
  have hz : ‖z‖ ≤ K*(1+Real.log T) := by
    calc
      _ ≤ c+|v| := by
        dsimp [z]
        exact (norm_add_le _ _).trans_eq (by
          simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
            Complex.norm_I,mul_one,abs_of_nonneg hc])
      _ ≤ K*(1+Real.log T) := by dsimp [K]; nlinarith
  have hz2 : ‖z‖^2 ≤ K^2*(1+Real.log T)^2 := by
    have hh := sq_le_sq₀ (norm_nonneg z) (by positivity : 0 ≤ K*(1+Real.log T)) |>.mpr hz
    simpa only [mul_pow] using hh
  have hz1 : ‖z‖ ≤ K*(1+Real.log T)^2 := by
    apply hz.trans
    exact mul_le_mul_of_nonneg_left (by nlinarith :
      1+Real.log T ≤ (1+Real.log T)^2) hK.le
  have hp : (1+Real.log T)^2 ≤ L*T^(1/2 : ℝ) :=
    Sechstmoment.logarithmic_power_le_rpow (by norm_num : (0 : ℝ) < 1/2) hT 2
  change 192*(‖z‖+‖z‖^2) < T
  calc
    _ ≤ 192*(K+K^2)*(1+Real.log T)^2 := by nlinarith
    _ ≤ 192*(K+K^2)*(L*T^(1/2 : ℝ)) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = C*T^(1/2 : ℝ) := by dsimp [C]; ring
    _ < T := hbound

theorem bblrGaussianTimeAmplitude_logarithmic_uniform_subpower_bounds
    {c ε κ θ A : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hε : 2*c < ε)
    (hκ : 0 < κ) (hθ : 0 ≤ θ) (hA : 0 ≤ A) :
    ∃ B : ℕ → ℝ, (∀ n, 0 ≤ B n) ∧
      ∀ᶠ T : ℝ in atTop, ∀ (σ α : MomentShifts),
      (∀ j, ‖α j‖ ≤ A) →
      (∀ k : PurePolarIndex, κ ≤ ‖normalizedPurePolarRoot σ k‖) →
      ∀ v : ℝ, |v| ≤ θ*Real.log T → ∀ x : ℝ, x ∈ Icc (1 : ℝ) 2 → ∀ n : ℕ,
      ‖iteratedDeriv n (bblrGaussianTimeAmplitude T σ α ((c : ℂ)+(v : ℂ)*I)) x‖ ≤
        B n*T^ε := by
  obtain ⟨B,hB,hb⟩ := bblrGaussianTimeAmplitude_uniform_subpower_derivatives hc hc1 hε hκ
  refine ⟨B,hB,?_⟩
  filter_upwards [bblrGamma_logarithmic_strip_large hc.le hc1 hθ,
    eventually_ge_atTop (8*(A+1)),eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with T hlarge hAT hT hlog
  intro σ α hα hroot v hv x hx n
  exact hb T A σ α v x hT hlog hA hAT hα hroot (hlarge v hv) hx n

end
end Sechstmoment.Source
