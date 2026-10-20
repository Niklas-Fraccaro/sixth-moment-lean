import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

namespace Sechstmoment
open Complex Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 1000000

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem a03Compact_uniform_schwartz_seminorms {ι : Type*}
    (f : ι → V → ℂ)
    (hc : ∀ i, HasCompactSupport (f i))
    (hs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    {R : ℝ} (hR : 0 ≤ R)
    (hball : ∀ i x, x ∈ tsupport (f i) → ‖x‖ ≤ R)
    (hd : ∀ n : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ i x,
      ‖iteratedFDeriv ℝ n (f i) x‖ ≤ D) :
    ∀ k n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
      SchwartzMap.seminorm ℂ k n ((hc i).toSchwartzMap (hs i)) ≤ C := by
  intro k n
  obtain ⟨D, hD, hb⟩ := hd n
  refine ⟨R^k * D, mul_nonneg (pow_nonneg hR k) hD, ?_⟩
  intro i
  apply SchwartzMap.seminorm_le_bound ℂ k n _ (mul_nonneg (pow_nonneg hR k) hD)
  intro x
  change ‖x‖^k * ‖iteratedFDeriv ℝ n (f i) x‖ ≤ R^k * D
  by_cases hz : iteratedFDeriv ℝ n (f i) x = 0
  · rw [hz, norm_zero, mul_zero]
    exact mul_nonneg (pow_nonneg hR k) hD
  · have hx : x ∈ tsupport (f i) :=
      tsupport_iteratedFDeriv_subset n (subset_tsupport _ hz)
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg x) (hball i x hx) k)
      (hb i x) (norm_nonneg _) (pow_nonneg hR k)

end
end Sechstmoment
