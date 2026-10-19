import Sechstmoment.Numerator.U.Separation.Tensor.SixFourier

/-! Uniform Fourier rapid decay follows from a bounded family of Schwartz
seminorms by continuity of the genuine Fourier transform. -/

namespace Sechstmoment
open Complex Real Set MeasureTheory Bornology
open scoped BigOperators FourierTransform RealInnerProductSpace
noncomputable section
set_option maxHeartbeats 1000000

theorem a03SixTensor_fourier_uniform_seminorm_bounds {ι : Type*}
    (f : ι → SchwartzMap A03SixTensorSpace ℂ)
    (hf : ∀ k n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
      SchwartzMap.seminorm ℂ k n (f i) ≤ C) :
    ∀ k n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ i,
      SchwartzMap.seminorm ℂ k n (𝓕 (f i)) < C := by
  have hbounded : IsVonNBounded ℂ (Set.range f) := by
    apply (schwartz_withSeminorms ℂ A03SixTensorSpace ℂ).isVonNBounded_iff_seminorm_bounded.mpr
    intro p
    obtain ⟨C, hC, hb⟩ := hf p.1 p.2
    refine ⟨C + 1, by linarith, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact lt_of_le_of_lt (hb i) (by linarith)
  have htransformed := hbounded.image (SchwartzMap.fourierTransformCLM ℂ)
  have hb := (schwartz_withSeminorms ℂ A03SixTensorSpace ℂ).isVonNBounded_iff_seminorm_bounded.mp
    htransformed
  intro k n
  obtain ⟨C, hC, hc⟩ := hb (k, n)
  refine ⟨C, hC, ?_⟩
  intro i
  exact hc _ ⟨f i, ⟨i, rfl⟩, rfl⟩

theorem a03SixTensor_fourier_uniform_rapid_bounds {ι : Type*}
    (f : ι → SchwartzMap A03SixTensorSpace ℂ)
    (hf : ∀ k n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
      SchwartzMap.seminorm ℂ k n (f i) ≤ C) :
    ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i ν,
      ‖(𝓕 (f i)) ν‖ ≤ C * (1 + ‖ν‖)^(-(N : ℝ)) := by
  obtain ⟨C0, hC0, hc0⟩ := a03SixTensor_fourier_uniform_seminorm_bounds f hf 0 0
  intro N
  obtain ⟨CN, hCN, hcN⟩ := a03SixTensor_fourier_uniform_seminorm_bounds f hf N 0
  let C : ℝ := 2^(N-1) * (C0 + CN)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro i ν
  have hn0 : ‖(𝓕 (f i)) ν‖ ≤ C0 :=
    ((𝓕 (f i)).norm_le_seminorm ℂ ν).trans (hc0 i).le
  have hnN : ‖ν‖^N * ‖(𝓕 (f i)) ν‖ ≤ CN :=
    ((𝓕 (f i)).norm_pow_mul_le_seminorm ℂ N ν).trans (hcN i).le
  have hp : (1 + ‖ν‖)^N * ‖(𝓕 (f i)) ν‖ ≤ C := by
    calc
      _ ≤ (2^(N-1) * ((1 : ℝ)^N + ‖ν‖^N)) * ‖(𝓕 (f i)) ν‖ :=
        mul_le_mul_of_nonneg_right (add_pow_le zero_le_one (norm_nonneg ν) N) (norm_nonneg _)
      _ = 2^(N-1) * (‖(𝓕 (f i)) ν‖ + ‖ν‖^N * ‖(𝓕 (f i)) ν‖) := by
        rw [one_pow]
        ring
      _ ≤ 2^(N-1) * (C0 + CN) :=
        mul_le_mul_of_nonneg_left (add_le_add hn0 hnN) (by positivity)
  have hbpos : 0 < (1 + ‖ν‖)^N := by positivity
  have he : (1 + ‖ν‖)^(-(N : ℝ)) = ((1 + ‖ν‖)^N)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  rw [he, ← div_eq_mul_inv]
  apply (le_div_iff₀ hbpos).mpr
  simpa only [mul_comm] using hp

end
end Sechstmoment
