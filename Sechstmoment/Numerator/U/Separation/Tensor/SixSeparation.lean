import Sechstmoment.Numerator.U.Separation.Tensor.Normalizer
import Sechstmoment.Numerator.U.Separation.Tensor.SixFourierUniform


namespace Sechstmoment
open Complex Real Set MeasureTheory
open scoped BigOperators FourierTransform RealInnerProductSpace
noncomputable section
set_option maxHeartbeats 1000000

theorem a03SixTensor_uniform_separation {ι : Type*}
    (f : ι → SchwartzMap A03SixTensorSpace ℂ)
    (hf : ∀ k n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
      SchwartzMap.seminorm ℂ k n (f i) ≤ C) :
    ∃ a : A03SixTensorSpace → ℝ, ∃ B : ℕ → ℝ, ∃ K : ℝ,
      Measurable a ∧ (∀ ν, 0 < a ν) ∧ (∀ j, 0 ≤ B j) ∧ 0 ≤ K ∧
      (∀ ν j, RectangularComplexWeight (a03SixTensorWeight a ν j)) ∧
      (∀ j ν i x, ‖iteratedDeriv j (a03SixTensorWeight a ν i) x‖ ≤ B j) ∧
      (∀ i, Integrable (a03SixTensorCoefficient (f i) a) ∧
        (∫ ν, ‖a03SixTensorCoefficient (f i) a ν‖) ≤ K) ∧
      (∀ i (x : Fin 6 → ℝ), 0 < x 0 →
        (∏ j : Fin 5, (rectangularSmoothBlockWeight (x j.succ) : ℂ)) * f i (a03SixTensorLogPoint x) =
          ∫ ν, a03SixTensorCoefficient (f i) a ν *
            ((x 0 : ℂ)^a03SixTensorExponent ν 0 *
              (∏ j, a03SixTensorWeight a ν j (x j.succ)))) := by
  have hrapid : ∀ n : ℕ, ∃ C : ℝ, ∀ i ν,
      ‖(𝓕 (f i)) ν‖ ≤ C * (1 + ‖ν‖)^(-(n : ℝ)) := by
    intro n
    obtain ⟨C, _hC, hc⟩ := a03SixTensor_fourier_uniform_rapid_bounds f hf n
    exact ⟨C, hc⟩
  obtain ⟨a, hm, ha, hr, K, hK, hc⟩ :=
    a03_uniform_rapid_tensor_normalizer_exists
      (fun i ν => (𝓕 (f i)) ν) (fun i => (𝓕 (f i)).continuous.measurable)
      hrapid (μ := volume)
  obtain ⟨B, hB, hb⟩ := a03SixTensorWeight_uniform_derivative_bounds a
    (fun ν => (ha ν).le) hr
  refine ⟨a, B, K, hm, ha, hB, hK,
    a03SixTensorWeight_complexWeight a, hb, ?_, ?_⟩
  · intro i
    change Integrable (fun ν => (𝓕 (f i)) ν / (a ν : ℂ)^5) ∧ _
    simpa only [a03SixTensorCoefficient, Complex.ofReal_pow] using hc i
  · exact fun i x hx0 => a03SixTensor_exact_separation_all_real (f i) a ha x hx0

end
end Sechstmoment
