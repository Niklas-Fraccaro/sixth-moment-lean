import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic

namespace Sechstmoment
open Set
noncomputable section
set_option maxHeartbeats 1000000

theorem phase_composition_frequency_cancellation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {g : F → G} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (n : ℕ) (x : E) {R C D : ℝ} (hR : 0 < R)
    (houter : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C/R^n)
    (hinner : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ (D*R)^i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ (n.factorial:ℝ)*C*D^n := by
  have h := norm_iteratedFDeriv_comp_le hg hf (by simp) x houter hinner
  apply h.trans_eq
  rw [mul_pow]
  field_simp

theorem phase_composition_frequency_cancellation_on
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {g : F → G} {s : Set E} {t : Set F}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g t)
    (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t) (hm : MapsTo f s t)
    (n : ℕ) {x : E} (hx : x∈s) {R C D : ℝ} (hR : 0 < R)
    (houter : ∀ i, i ≤ n → ‖iteratedFDerivWithin ℝ i g t (f x)‖ ≤ C/R^n)
    (hinner : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDerivWithin ℝ i f s x‖ ≤ (D*R)^i) :
    ‖iteratedFDerivWithin ℝ n (g ∘ f) s x‖ ≤ (n.factorial:ℝ)*C*D^n := by
  have h := norm_iteratedFDerivWithin_comp_le hg hf (by simp) ht hs hm hx houter hinner
  apply h.trans_eq
  rw [mul_pow]
  field_simp

theorem phase_linear_derivative_growth_to_geometric {R D : ℝ}
    (hR : 1 ≤ R) (hD : 1 ≤ D) {i : ℕ} (hi : 1 ≤ i) {v : ℝ}
    (hv : v ≤ D*R) : v ≤ (D*R)^i := by
  apply hv.trans
  exact le_self_pow₀ (one_le_mul_of_one_le_of_one_le hD hR) (by omega)

end
end Sechstmoment
