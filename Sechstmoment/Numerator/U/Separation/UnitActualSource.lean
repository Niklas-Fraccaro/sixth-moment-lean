import Sechstmoment.Numerator.U.Separation.ActualAmplifierCoefficients
import Sechstmoment.Numerator.U.Separation.UnitActualScales

namespace Sechstmoment
open Complex Source Set
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def boundaryActualAlpha (T A : ℝ) (f : ℝ → ℝ) (k : Fin 4 → ℕ) : ℕ → ℂ :=
  boundaryEmbeddedAlpha (boundaryActualFlags k) (phaseActualAmplifierCoefficient T f A)
def boundaryActualBeta (T A B H : ℝ) (g : ℝ → ℝ) (k : Fin 4 → ℕ) (l : ℕ) : ℕ → ℂ :=
  boundaryEmbeddedBeta (boundaryActualFlags k)
    (phaseAdjustedBeta (phaseActualScales A B H k) (phaseActualAmplifierCoefficient T g B) l)

theorem boundaryActual_scales_pos (A B H : ℝ) (k : Fin 4 → ℕ)
    (hA : 0<A) (hB : 0<B) (hH : 0<H) :
    ∀ j, 0<(phaseActualScales A B H k).size j := by
  intro j
  fin_cases j <;> simp [phaseActualScales, QuadraticScales.size]
  all_goals first | exact hA | exact hB | exact hH | exact boundaryActual_scale_pos _

theorem boundaryActual_alpha_support (T A B H : ℝ) (f : ℝ → ℝ) (k : Fin 4 → ℕ)
    (hA : 0<A) : ∀ n : ℕ,
    (n : ℝ)∉Icc (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).A
      (2*(boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).A) →
      boundaryActualAlpha T A f k n=0 :=
  boundaryEmbedded_alpha_support (boundaryActualFlags k) (phaseActualScales A B H k)
    (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient_support T f hA)

theorem boundaryActual_beta_support (T A B H : ℝ) (g : ℝ → ℝ) (k : Fin 4 → ℕ)
    (hB : 0<B) (l : ℕ) : ∀ n : ℕ,
    (n : ℝ)∉Icc (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).B
      (2*(boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).B) →
      boundaryActualBeta T A B H g k l n=0 :=
  boundaryEmbedded_beta_support (boundaryActualFlags k) (phaseActualScales A B H k)
    (phaseAdjustedBeta (phaseActualScales A B H k) (phaseActualAmplifierCoefficient T g B) l)
    (phaseAdjustedBeta_support _ _ (phaseActualAmplifierCoefficient_support T g hB) l)

theorem boundaryActual_alpha_norm (T A : ℝ) (f : ℝ → ℝ) (k : Fin 4 → ℕ)
    {F : ℝ} (hA : 0<A) (hF : 0≤F) (hf : ∀ x, ‖f x‖≤F) (n : ℕ) :
    ‖boundaryActualAlpha T A f k n‖≤F := by
  exact rectangular_unit_coefficient_bound _ hF
    (fun m => rectangular_unit_coefficient_bound _ hF
      (phaseActualAmplifierCoefficient_norm_le T f hA hF hf) m) n

theorem boundaryActual_beta_norm (T A B H : ℝ) (g : ℝ → ℝ) (k : Fin 4 → ℕ)
    {G : ℝ} (hB : 0<B) (hG : 0≤G) (hg : ∀ x, ‖g x‖≤G) (l n : ℕ) :
    ‖boundaryActualBeta T A B H g k l n‖≤G := by
  have hb (m : ℕ) :
      ‖phaseAdjustedBeta (phaseActualScales A B H k) (phaseActualAmplifierCoefficient T g B) l m‖≤G :=
    (phaseAdjustedBeta_norm_le _ hB _ (phaseActualAmplifierCoefficient_support T g hB) l m).trans
      (phaseActualAmplifierCoefficient_norm_le T g hB hG hg m)
  exact rectangular_unit_coefficient_bound _ hG
    (fun m => rectangular_unit_coefficient_bound _ hG hb m) n

theorem boundaryActual_coefficient_families {a b : ℝ} (f g : ℝ → ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∃ F G : ℝ, 0≤F ∧ 0≤G ∧ ∀ T A B H : ℝ, 0<A → 0<B →
      ∀ k : Fin 4 → ℕ, ∀ l n : ℕ,
      ‖boundaryActualAlpha T A f k n‖≤F ∧ ‖boundaryActualBeta T A B H g k l n‖≤G := by
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgb⟩ := rectangular_supported_profile_bounded g hg
  exact ⟨F,G,hF,hG,fun T A B H hA hB k l n =>
    ⟨boundaryActual_alpha_norm T A f k hA hF hfb n,
      boundaryActual_beta_norm T A B H g k hB hG hgb l n⟩⟩

theorem boundaryActual_source_sum (positive : Bool) (T A B H : ℝ) (f g : ℝ → ℝ)
    (k : Fin 4 → ℕ) (α : MomentShifts) (z : ℂ) (l : ℕ)
    (hA : 0<A) (hB : 0<B) (hH : 0<H) :
    rectangularComplexQuadraticSum positive (phaseActualScales A B H k)
      (phaseActualAmplifierCoefficient T f A)
      (phaseAdjustedBeta (phaseActualScales A B H k) (phaseActualAmplifierCoefficient T g B) l)
      (phaseFiveWeights α z l) = rectangularComplexQuadraticSum positive
      (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k))
      (boundaryActualAlpha T A f k) (boundaryActualBeta T A B H g k l) (phaseFiveWeights α z l) :=
  boundaryEmbedded_signed_sum (boundaryActualFlags k) positive (phaseActualScales A B H k)
    (boundaryActual_scales_pos A B H k hA hB hH) _ _ _ (phaseFiveWeights_complexWeight α z l)
    (boundaryActual_flags_low A B H k)

theorem boundaryActual_source_discrepancy (positive : Bool) (T A B H : ℝ) (f g : ℝ → ℝ)
    (k : Fin 4 → ℕ) (α : MomentShifts) (z : ℂ) (l : ℕ)
    (hA : 0<A) (hB : 0<B) (hH : 0<H) :
    rectangularComplexQuadraticSum positive (phaseActualScales A B H k)
      (phaseActualAmplifierCoefficient T f A)
      (phaseAdjustedBeta (phaseActualScales A B H k) (phaseActualAmplifierCoefficient T g B) l)
      (phaseFiveWeights α z l) - rectangularComplexZeroMode
        (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k))
        (boundaryActualAlpha T A f k) (boundaryActualBeta T A B H g k l) (phaseFiveWeights α z l) =
      rectangularComplexDiscrepancy positive
        (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k))
        (boundaryActualAlpha T A f k) (boundaryActualBeta T A B H g k l) (phaseFiveWeights α z l) := by
  rw [boundaryActual_source_sum positive T A B H f g k α z l hA hB hH]
  rfl

end
end Sechstmoment
