import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Sechstmoment.Analysis.Mellin.ProfileInversion


namespace Sechstmoment
open Complex Real MeasureTheory Set
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 1000000

def a03ProfileTimeFourier (Φ : ℝ → ℂ) (T ℓ : ℝ) : ℂ :=
  ∫ t : ℝ, Φ (t / T) * Complex.exp (((ℓ * t : ℝ) : ℂ) * I)

theorem a03_profile_frequency_power_bound {Φ : ℝ → ℂ}
    (hK : HasCompactSupport Φ) (hS : ContDiff ℝ ∞ Φ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ,
      |ξ| ^ N * ‖profileLaplaceTransform Φ ((ξ : ℂ) * I)‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := profileLaplaceTransform_vertical_decay hK hS 0 N
  let C := (2 * π) ^ N * max C₀ 0
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro ξ
  have hπ : 0 < 2 * π := by positivity
  have hfreq : |ξ| = (2 * π) * |-ξ / (2 * π)| := by
    rw [abs_div, abs_neg, abs_of_pos hπ]
    field_simp
  have hp : |ξ| ^ N ≤ (2 * π) ^ N * (1 + |-ξ / (2 * π)|) ^ N := by
    rw [hfreq, mul_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (by linarith) N) (by positivity)
  have hb : (1 + |-ξ / (2 * π)|) ^ N *
      ‖profileLaplaceTransform Φ ((ξ : ℂ) * I)‖ ≤ C₀ := by
    simpa only [Complex.ofReal_zero, zero_add] using hC₀ ξ
  calc
    _ ≤ ((2 * π) ^ N * (1 + |-ξ / (2 * π)|) ^ N) *
        ‖profileLaplaceTransform Φ ((ξ : ℂ) * I)‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = (2 * π) ^ N * ((1 + |-ξ / (2 * π)|) ^ N *
        ‖profileLaplaceTransform Φ ((ξ : ℂ) * I)‖) := by ring
    _ ≤ (2 * π) ^ N * C₀ := mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ C := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

theorem a03_profile_time_fourier_rescaling (Φ : ℝ → ℂ) {T : ℝ}
    (hT : 0 < T) (ℓ : ℝ) :
    a03ProfileTimeFourier Φ T ℓ =
      (T : ℂ) * profileLaplaceTransform Φ (((T * ℓ : ℝ) : ℂ) * I) := by
  let g : ℝ → ℂ := fun x => Φ x * Complex.exp (((T * ℓ : ℝ) : ℂ) * I * (x : ℂ))
  have he : a03ProfileTimeFourier Φ T ℓ = ∫ t : ℝ, g (t / T) := by
    unfold a03ProfileTimeFourier
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp [g]
    congr 2
    push_cast
    field_simp [show (T : ℂ) ≠ 0 by exact_mod_cast hT.ne']
  rw [he, Measure.integral_comp_div, abs_of_pos hT, Complex.real_smul]
  congr 1
  unfold profileLaplaceTransform
  apply integral_congr_ae
  filter_upwards [] with t
  dsimp [g]
  ring

theorem a03_profile_scaled_time_decay {Φ : ℝ → ℂ}
    (hK : HasCompactSupport Φ) (hS : ContDiff ℝ ∞ Φ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T → ∀ ℓ : ℝ, ℓ ≠ 0 →
      ‖a03ProfileTimeFourier Φ T ℓ‖ ≤ C * T / (T * |ℓ|) ^ N := by
  obtain ⟨C, hC, hb⟩ := a03_profile_frequency_power_bound hK hS N
  refine ⟨C, hC, ?_⟩
  intro T hT ℓ hℓ
  have hp : 0 < (T * |ℓ|) ^ N := pow_pos (mul_pos hT (abs_pos.mpr hℓ)) N
  have hh := hb (T * ℓ)
  rw [abs_mul, abs_of_pos hT] at hh
  have hn : ‖profileLaplaceTransform Φ (((T * ℓ : ℝ) : ℂ) * I)‖ ≤
      C / (T * |ℓ|) ^ N := (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hh)
  rw [a03_profile_time_fourier_rescaling Φ hT ℓ, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  calc
    _ ≤ T * (C / (T * |ℓ|) ^ N) := mul_le_mul_of_nonneg_left hn hT.le
    _ = _ := by ring

theorem a03_profile_polynomial_frequency_decay {Φ : ℝ → ℂ}
    (hK : HasCompactSupport Φ) (hS : ContDiff ℝ ∞ Φ) (N : ℕ) (σ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → ∀ ℓ : ℝ,
      T ^ σ ≤ T * |ℓ| →
      ‖a03ProfileTimeFourier Φ T ℓ‖ ≤ C * T ^ (1 - σ * (N : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := a03_profile_scaled_time_decay hK hS N
  refine ⟨C, hC, ?_⟩
  intro T hT ℓ hℓ
  have hTp : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hbase : 0 < T * |ℓ| := (Real.rpow_pos_of_pos hTp σ).trans_le hℓ
  have hne : ℓ ≠ 0 := by
    intro hz
    simp only [hz, abs_zero, mul_zero] at hbase
    exact lt_irrefl 0 hbase
  have hp : T ^ (σ * (N : ℝ)) ≤ (T * |ℓ|) ^ N := by
    rw [Real.rpow_mul hTp.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hTp.le _) hℓ N
  calc
    _ ≤ C * T / (T * |ℓ|) ^ N := hb T hTp ℓ hne
    _ ≤ C * T / T ^ (σ * (N : ℝ)) :=
      div_le_div_of_nonneg_left (mul_nonneg hC hTp.le)
        (Real.rpow_pos_of_pos hTp _) hp
    _ = C * T ^ (1 - σ * (N : ℝ)) := by
      rw [Real.rpow_sub hTp, Real.rpow_one]
      ring

theorem a03_profile_polynomial_cutoff_rapid {Φ : ℝ → ℂ}
    (hK : HasCompactSupport Φ) (hS : ContDiff ℝ ∞ Φ) {σ : ℝ} (hσ : 0 < σ)
    (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → ∀ ℓ : ℝ,
      T ^ σ ≤ T * |ℓ| → ‖a03ProfileTimeFourier Φ T ℓ‖ ≤ C * T ^ (-M) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((M + 1) / σ)
  have hexp : 1 - σ * (N : ℝ) ≤ -M := by
    have hn := (div_lt_iff₀ hσ).mp hN
    nlinarith
  obtain ⟨C, hC, hb⟩ := a03_profile_polynomial_frequency_decay hK hS N σ
  refine ⟨C, hC, ?_⟩
  intro T hT ℓ hℓ
  exact (hb T hT ℓ hℓ).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT hexp) hC)

end
end Sechstmoment
