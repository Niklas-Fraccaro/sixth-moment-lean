import Sechstmoment.Denominator.Gram.ChiFrequencySymbol
import Sechstmoment.Denominator.Gram.NonstationaryChiPhase
import Sechstmoment.Numerator.U.Separation.TimePowerProfileFourier

namespace Sechstmoment
open Complex Real Set Filter MeasureTheory
open scoped ContDiff BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem d06_time_power_profile_uniform_derivative_bounds {Φ : ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ ⊆ Icc (1 : ℝ) 2)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∀ τ : ℂ, ‖τ‖ ≤ R →
      ∀ j x, ‖iteratedDeriv j (a03ProfileProduct Φ (fun y : ℝ => (y : ℂ) ^ τ)) x‖ ≤ C j := by
  have hK : HasCompactSupport Φ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs
  obtain ⟨P, hP, hPd⟩ := a03_profile_derivative_bounds hK hΦ
  let B : ℕ → ℝ := fun j => ((j : ℝ) + 1) ^ j * (1 + R) ^ j * 2 ^ R
  have hB (j : ℕ) : 0 ≤ B j := by dsimp [B]; positivity
  refine ⟨fun j => a03ProfileProductDerivativeBudget P B j, ?_, ?_⟩
  · intro j
    unfold a03ProfileProductDerivativeBudget
    exact Finset.sum_nonneg (fun i _ => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (hP i)) (hB _))
  · intro τ hτ j x
    have hτre : τ.re ≤ R := (Complex.re_le_norm τ).trans hτ
    have hA (y : ℝ) (hy : y ∈ Icc (1 : ℝ) 2) :
        ContDiffAt ℝ ∞ (fun y : ℝ => (y : ℂ) ^ τ) y :=
      positive_cpow_contDiffAt τ (zero_lt_one.trans_le hy.1)
    have hd (n : ℕ) (y : ℝ) (hy : y ∈ Icc (1 : ℝ) 2) :
        ‖iteratedDeriv n (fun y : ℝ => (y : ℂ) ^ τ) y‖ ≤ B n * 1 := by
      have hyp : 0 < y := zero_lt_one.trans_le hy.1
      have hp : y ^ (τ.re - (n : ℝ)) ≤ 2 ^ R :=
        (Real.rpow_le_rpow_of_exponent_le hy.1
          (by linarith only [hτre, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])).trans
        (Real.rpow_le_rpow hyp.le hy.2 hR)
      rw [positive_cpow_iteratedDeriv n τ hyp, norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos hyp, Complex.sub_re, Complex.natCast_re]
      have hpow : (1 + ‖τ‖) ^ n ≤ (1 + R) ^ n :=
        pow_le_pow_left₀ (by positivity) (by linarith only [hτ]) n
      have hf := (mellinFallingCoefficient_norm_le n τ).trans
        (mul_le_mul_of_nonneg_left hpow (by positivity))
      exact (mul_le_mul hf hp (Real.rpow_nonneg hyp.le _) (by positivity)).trans_eq
        (by dsimp [B]; ring)
    simpa only [mul_one] using
      a03_profile_product_derivative_bound hΦ hs hA hP hB hPd zero_le_one hd j x

theorem d06_chi_time_power_profile_fourier_decay {Φ : ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ ⊆ Icc (1 : ℝ) 2)
    {R S : ℝ} (hR : 0 ≤ R) (hS : S < 1) (k : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ T : ℝ in atTop, ∀ τ : ℂ, ‖τ‖ ≤ R →
      ∀ ℓ : ℝ, -S * Real.log T ≤ ℓ →
        ‖a03ProfileTimeFourier
          (fun y => a03ProfileProduct Φ (fun y : ℝ => (y : ℂ) ^ τ) y *
            (criticalChi (T * y))⁻¹) T ℓ‖ ≤ D * T ^ (1 - (k : ℝ)) := by
  obtain ⟨C, hC, hCd⟩ := d06_time_power_profile_uniform_derivative_bounds hΦ hs hR
  let B : ℕ → ℝ := fun n => (Nat.factorial n : ℝ) / (1/4 : ℝ)^n
  have hB (n : ℕ) : 0 ≤ B n := by dsimp [B]; positivity
  let D := d06NonstationaryBudget C B k 0
  refine ⟨D, d06_nonstationary_budget_nonneg hC hB k 0, ?_⟩
  filter_upwards [d06ChiReciprocalSymbol_uniform_all_real_derivative_bounds hS,
    d06ChiReciprocalSymbol_uniform_real_contDiffAt hS,
    d06ChiFrequencyShift_uniform_nonzero hS, eventually_gt_atTop (0 : ℝ)]
    with T hrd hr hn hT
  intro τ hτ ℓ hℓ
  let A := a03ProfileProduct Φ (fun y : ℝ => (y : ℂ) ^ τ)
  let r : ℝ → ℂ := fun y => (I * ((ℓ + d06ChiFrequency (T * y) : ℝ) : ℂ))⁻¹
  let w : ℝ → ℂ := fun y => I * ((ℓ + d06ChiFrequency (T * y) : ℝ) : ℂ)
  have hAs : tsupport A ⊆ Icc (1 : ℝ) 2 := (a03_profile_product_tsupport _ _).trans hs
  have hA : ContDiff ℝ ∞ A := a03_profile_product_contDiff hΦ
    (fun y hy => positive_cpow_contDiffAt τ (zero_lt_one.trans_le (hs hy).1))
  have hinv (y : ℝ) (hy : y ∈ tsupport A) : r y * w y = 1 := by
    have hys := hAs hy
    have hyre : (y : ℂ).re ∈ Icc (3/4 : ℝ) (9/4) := by
      simp only [Complex.ofReal_re]
      constructor <;> linarith [hys.1, hys.2]
    have hh := hn ℓ hℓ (y : ℂ) hyre (by simp)
    rw [d06ComplexHeightPoint_ofReal, d06ComplexChiFrequency_criticalLine_real] at hh
    have hz : ((ℓ : ℂ) + (d06ChiFrequency (T * y) : ℂ)) ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at hh
      linarith
    exact inv_mul_cancel₀ (mul_ne_zero I_ne_zero (by simpa only [Complex.ofReal_add] using hz))
  have hb := d06_nonstationary_time_integral_bound hT hA hAs
    (fun y hy => hr ℓ hℓ y (hAs hy))
    (fun y _ => d06NonstationaryChiPhase_contDiffAt T ℓ y)
    (fun y _ => d06NonstationaryChiPhase_hasDerivAt T ℓ y)
    hinv (fun y _ => d06NonstationaryChiPhase_norm T ℓ y)
    hC hB (hCd τ hτ) (fun n y hy => hrd ℓ hℓ n y (hAs hy)) k
  have he : a03ProfileTimeFourier
      (fun y => A y * (criticalChi (T * y))⁻¹) T ℓ =
      ∫ t : ℝ, A (t / T) * d06NonstationaryChiPhase T ℓ (t / T) := by
    unfold a03ProfileTimeFourier
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp [d06NonstationaryChiPhase]
    rw [mul_assoc]
    congr 2
    push_cast
    field_simp [show (T : ℂ) ≠ 0 by exact_mod_cast hT.ne']
  rw [he]
  exact hb.trans_eq (by
    dsimp only [D]
    rw [Real.rpow_sub hT, Real.rpow_one, Real.rpow_natCast]
    ring)

end
end Sechstmoment
