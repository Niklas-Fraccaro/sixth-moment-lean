import SixthMoment.Numerator.U.Separation.ActualSeparatedGap
import SixthMoment.Numerator.U.Separation.BoundaryDilation

namespace SixthMoment
open Complex Source Set
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def boundaryActualFlags (k : Fin 4 → ℕ) : Fin 4 → Bool := fun j => decide (k j=0)
def boundaryActualZetaScale (k : ℕ) : ℝ :=
  rectangularUnitFactor (decide (k=0))*rectangularAFESmoothScale k

theorem boundaryActual_scale_pos (k : ℕ) : 0<rectangularAFESmoothScale k := by
  unfold rectangularAFESmoothScale
  positivity

theorem boundaryActual_scale_ge_two_thirds (k : ℕ) :
    2/3≤rectangularAFESmoothScale k := by
  unfold rectangularAFESmoothScale
  have h : (1 : ℝ)≤(3/2 : ℝ)^k := one_le_pow₀ (by norm_num)
  apply (le_div_iff₀ (by norm_num : (0 : ℝ)<3/2)).mpr
  norm_num
  exact h

theorem boundaryActual_scale_ge_three_halves {k : ℕ} (hk : 2≤k) :
    3/2≤rectangularAFESmoothScale k := by
  unfold rectangularAFESmoothScale
  have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤3/2) hk
  apply (le_div_iff₀ (by norm_num : (0 : ℝ)<3/2)).mpr
  norm_num at h ⊢
  exact h

theorem boundaryActual_one_scale : rectangularAFESmoothScale 1=1 := by
  norm_num [rectangularAFESmoothScale]

theorem boundaryActual_one_weight_zero (n : ℕ) :
    rectangularSmoothBlockWeight ((n : ℝ)/rectangularAFESmoothScale 1)=0 := by
  rw [boundaryActual_one_scale, div_one]
  by_cases hn : n≤1
  · apply rectangularSmoothBlockWeight_zero_le
    exact_mod_cast hn
  · apply rectangularSmoothBlockWeight_zero_ge
    exact_mod_cast (show 2≤n by omega)

theorem boundaryActual_one_block_zero (k n : Fin 4 → ℕ) (j : Fin 4)
    (hk : k j=1) : rectangularAFESmoothWeight k n=0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rw [hk]
  have he : (3/2 : ℝ)*(n j+1)/(3/2)^1=(n j+1 : ℝ) := by ring
  rw [he]
  simpa [boundaryActual_one_scale] using boundaryActual_one_weight_zero (n j+1)

theorem boundaryActual_active_indices (k n : Fin 4 → ℕ)
    (hn : rectangularAFESmoothWeight k n≠0) : ∀ j, k j≠1 := by
  intro j hj
  exact hn (boundaryActual_one_block_zero k n j hj)

theorem boundaryActual_flags_low (A B H : ℝ) (k : Fin 4 → ℕ) :
    ∀ j, boundaryActualFlags k j=true →
      (phaseActualScales A B H k).size (rectangularUnitCoordinate j)=2/3 := by
  intro j hj
  have hk : k j=0 := by simpa [boundaryActualFlags] using hj
  have hs : rectangularAFESmoothScale (k j)=2/3 := by rw [hk, rectangular_AFE_smooth_low_scale]
  fin_cases j <;> simpa [phaseActualScales, QuadraticScales.size, rectangularUnitCoordinate] using hs

theorem boundaryActual_embedded_low_scale : boundaryActualZetaScale 0=4/3 := by
  norm_num [boundaryActualZetaScale, rectangularUnitFactor, rectangularAFESmoothScale]

theorem boundaryActual_embedded_nonzero_scale {k : ℕ} (hk : k≠0) :
    boundaryActualZetaScale k=rectangularAFESmoothScale k := by
  simp [boundaryActualZetaScale, rectangularUnitFactor, hk]

theorem boundaryActual_embedded_scale_ge_one (k : ℕ) : 1≤boundaryActualZetaScale k := by
  by_cases hk : k=0
  · rw [hk, boundaryActual_embedded_low_scale]
    norm_num
  · rw [boundaryActual_embedded_nonzero_scale hk]
    exact rectangular_AFE_smooth_scale_ge_one (by omega)

theorem boundaryActual_embedded_scale_order {k l : ℕ} (hkl : k≤l)
    (_hk : k≠1) (hl : l≠1) : boundaryActualZetaScale k≤boundaryActualZetaScale l := by
  by_cases hk0 : k=0
  · rw [hk0, boundaryActual_embedded_low_scale]
    by_cases hl0 : l=0
    · rw [hl0, boundaryActual_embedded_low_scale]
    · rw [boundaryActual_embedded_nonzero_scale hl0]
      have h := boundaryActual_scale_ge_three_halves (show 2≤l by omega)
      linarith
  · have hl0 : l≠0 := by omega
    rw [boundaryActual_embedded_nonzero_scale hk0, boundaryActual_embedded_nonzero_scale hl0]
    unfold rectangularAFESmoothScale
    exact div_le_div_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤3/2) hkl) (by norm_num)

theorem boundaryActual_embedded_lower_bounds (A B H : ℝ) (k : Fin 4 → ℕ)
    (hA : 2/3≤A) (hB : 2/3≤B) (hH : 2/3≤H) :
    ∀ j, 1≤(boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).size j := by
  have h (j : Fin 4) : if boundaryActualFlags k j then
      rectangularAFESmoothScale (k j)=2/3 else 1≤rectangularAFESmoothScale (k j) := by
    by_cases hj : k j=0
    · simp [boundaryActualFlags, hj, rectangular_AFE_smooth_low_scale]
    · simp only [boundaryActualFlags, decide_eq_true_eq, hj, ↓reduceIte]
      exact rectangular_AFE_smooth_scale_ge_one (by omega)
  exact boundaryEmbedded_lower_bound (boundaryActualFlags k) (phaseActualScales A B H k)
    hA hB hH (h 0) (h 1) (h 2) (h 3)

end
end SixthMoment
