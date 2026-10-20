import Sechstmoment.Numerator.U.Separation.ActualAmplifierCoefficients
import Sechstmoment.Numerator.U.Separation.Tensor.SixFourier

namespace Sechstmoment
open Complex Real Source Set
open scoped BigOperators FourierTransform RealInnerProductSpace
noncomputable section
set_option maxHeartbeats 1000000

def a03SixTensorBeta (ν : A03SixTensorSpace) (B : ℝ)
    (β : ℕ → ℂ) (n : ℕ) : ℂ :=
  β n * (((n : ℝ)/B : ℝ) : ℂ)^a03SixTensorExponent ν 0

theorem a03SixTensor_character_norm (ν : A03SixTensorSpace) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ)^a03SixTensorExponent ν 0‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, a03SixTensorExponent_re, Real.rpow_zero]

theorem a03SixTensorBeta_support (ν : A03SixTensorSpace) (B : ℝ) (β : ℕ → ℂ)
    (hβ : ∀ n : ℕ, (n : ℝ) ∉ Icc B (2*B) → β n = 0) :
    ∀ n : ℕ, (n : ℝ) ∉ Icc B (2*B) → a03SixTensorBeta ν B β n = 0 := by
  intro n hn
  simp [a03SixTensorBeta, hβ n hn]

theorem a03SixTensorBeta_norm (ν : A03SixTensorSpace) {B : ℝ} (hB : 0 < B)
    (β : ℕ → ℂ) (hβ : ∀ n : ℕ, (n : ℝ) ∉ Icc B (2*B) → β n = 0) (n : ℕ) :
    ‖a03SixTensorBeta ν B β n‖ = ‖β n‖ := by
  by_cases hn : n = 0
  · subst n
    have hz : β 0 = 0 := hβ 0 (by simp only [Nat.cast_zero, Set.mem_Icc]; intro h; linarith)
    simp [a03SixTensorBeta, hz]
  · have hnp : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    unfold a03SixTensorBeta
    rw [norm_mul, a03SixTensor_character_norm ν (div_pos hnp hB), mul_one]

theorem a03SixTensorBeta_actual_uniform {b : ℝ} (g : ℝ → ℝ)
    (hg : SmoothInteriorProfile b g) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ T B : ℝ, 0 < B → ∀ ν : A03SixTensorSpace,
      (∀ n : ℕ, (n : ℝ) ∉ Icc B (2*B) →
        a03SixTensorBeta ν B (phaseActualAmplifierCoefficient T g B) n = 0) ∧
      (∀ n : ℕ, ‖a03SixTensorBeta ν B (phaseActualAmplifierCoefficient T g B) n‖ ≤ F) := by
  obtain ⟨F, hF, hf⟩ := phaseActualAmplifierCoefficient_uniform g hg
  refine ⟨F, hF, ?_⟩
  intro T B hB ν
  refine ⟨a03SixTensorBeta_support ν B _ (hf T B hB).1, ?_⟩
  intro n
  rw [a03SixTensorBeta_norm ν hB _ (hf T B hB).1]
  exact (hf T B hB).2 n

end
end Sechstmoment
