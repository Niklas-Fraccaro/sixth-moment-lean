import SixthMoment.Numerator.U.Separation.ActualDoubleUnitExclusion
import SixthMoment.Numerator.U.ZeroModes.CommonDilationZeroMode
import SixthMoment.Numerator.U.ZeroModes.SideOrientation


namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def phasePairSwapUnitFlags (m n : Bool) (f : Fin 4 → Bool) : Fin 4 → Bool :=
  ![if m then f 1 else f 0,if m then f 0 else f 1,
    if n then f 3 else f 2,if n then f 2 else f 3]

theorem phase_pair_swap_unit_products (m n : Bool) (f : Fin 4 → Bool) :
    rectangularUnitMFactor (phasePairSwapUnitFlags m n f)=rectangularUnitMFactor f ∧
      rectangularUnitNFactor (phasePairSwapUnitFlags m n f)=rectangularUnitNFactor f := by
  cases m <;> cases n <;>
    simp [phasePairSwapUnitFlags,rectangularUnitMFactor,rectangularUnitNFactor,mul_comm]

theorem boundaryEmbedded_pair_swap_scales (m n : Bool) (f : Fin 4 → Bool)
    (q : QuadraticScales) :
    phasePairSwapScales m n (boundaryEmbeddedScales f q)=
      boundaryEmbeddedScales (phasePairSwapUnitFlags m n f) (phasePairSwapScales m n q) := by
  cases m <;> cases n <;>
    simp [phasePairSwapScales,boundaryEmbeddedScales,boundaryCommonScales,
      rectangularUnitScales,phasePairSwapUnitFlags,rectangularUnitMFactor,
      rectangularUnitNFactor,mul_comm]

theorem boundaryEmbedded_discrete_complex_zero_mode (f : Fin 4 → Bool)
    (hm : f 1=false) (hn : f 3=false) (q : QuadraticScales)
    (hq : ∀ j, 0 < q.size j) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℂ)
    (hW : ∀ i, RectangularComplexWeight (W i))
    (hm₁ : f 0=true → q.M₁=2/3) (hn₁ : f 2=true → q.N₁=2/3) :
    rectangularComplexZeroMode q α β W=
      rectangularComplexZeroMode (boundaryEmbeddedScales f q)
        (boundaryEmbeddedAlpha f α) (boundaryEmbeddedBeta f β) W := by
  rw [rectangular_unit_discrete_complex_zero_mode f hm hn q hq α β W hW hm₁ hn₁]
  exact boundaryCommon_complex_zero_mode (by norm_num : (0:ℕ)<2)
    (rectangularUnitScales f q)
    (fun j => by
      rw [rectangular_unit_scales_size]
      exact mul_pos (by exact_mod_cast rectangular_unit_factors_pos f j) (hq j))
    (rectangularUnitCoefficient (rectangularUnitNFactor f) α)
    (rectangularUnitCoefficient (rectangularUnitMFactor f) β) W hW

theorem boundaryActual_sorted_larger_unit_flag_false (k l : ℕ)
    (hk : k≠1) (hl : l≠1) (hunit : ¬ (k=0 ∧ l=0)) :
    (if decide (boundaryActualZetaScale l < boundaryActualZetaScale k)
      then decide (k=0) else decide (l=0))=false := by
  by_cases hk₀ : k=0
  · have hl₀ : l≠0 := by intro h; exact hunit ⟨hk₀,h⟩
    have hscale : 3/2≤boundaryActualZetaScale l := by
      rw [boundaryActual_embedded_nonzero_scale hl₀]
      exact boundaryActual_scale_ge_three_halves (by omega)
    have hnot : ¬ boundaryActualZetaScale l < boundaryActualZetaScale k := by
      rw [hk₀,boundaryActual_embedded_low_scale]
      linarith
    simp [hnot,hl₀]
  · by_cases hl₀ : l=0
    · have hscale : 3/2≤boundaryActualZetaScale k := by
        rw [boundaryActual_embedded_nonzero_scale hk₀]
        exact boundaryActual_scale_ge_three_halves (by omega)
      have hlt : boundaryActualZetaScale l < boundaryActualZetaScale k := by
        rw [hl₀,boundaryActual_embedded_low_scale]
        linarith
      simp [hlt,hk₀]
    · simp [hk₀,hl₀]

theorem boundaryActual_sorted_unit_flags_discrete (A B H : ℝ) (k : Fin 4 → ℕ)
    (hidx : ∀ j, k j≠1) (hm : ¬ (k 0=0 ∧ k 1=0))
    (hn : ¬ (k 2=0 ∧ k 3=0)) :
    let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
    let fs := phasePairSwapUnitFlags (decide (q.M₂<q.M₁)) (decide (q.N₂<q.N₁))
      (boundaryActualFlags k)
    fs 1=false ∧ fs 3=false := by
  dsimp only
  constructor
  · change (if decide (boundaryActualZetaScale (k 1)<boundaryActualZetaScale (k 0))
      then decide (k 0=0) else decide (k 1=0))=false
    exact boundaryActual_sorted_larger_unit_flag_false (k 0) (k 1) (hidx 0) (hidx 1) hm
  · change (if decide (boundaryActualZetaScale (k 3)<boundaryActualZetaScale (k 2))
      then decide (k 2=0) else decide (k 3=0))=false
    exact boundaryActual_sorted_larger_unit_flag_false (k 2) (k 3) (hidx 2) (hidx 3) hn

theorem boundaryActual_normalized_zero_mode_eq_native_sorted
    (A B H : ℝ) (k : Fin 4 → ℕ) (hA : 0 < A) (hB : 0 < B) (hH : 0 < H)
    (hidx : ∀ j, k j≠1) (hm : ¬ (k 0=0 ∧ k 1=0)) (hn : ¬ (k 2=0 ∧ k 3=0))
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℂ) (hW : ∀ i, RectangularComplexWeight (W i)) :
    let q := phaseActualScales A B H k
    let q' := boundaryEmbeddedScales (boundaryActualFlags k) q
    let m := decide (q'.M₂<q'.M₁)
    let n := decide (q'.N₂<q'.N₁)
    rectangularComplexZeroMode (phaseNormalizedScales q')
      (phaseNormalizedAlpha q' (boundaryEmbeddedAlpha (boundaryActualFlags k) α)
        (boundaryEmbeddedBeta (boundaryActualFlags k) β))
      (phaseNormalizedBeta q' (boundaryEmbeddedAlpha (boundaryActualFlags k) α)
        (boundaryEmbeddedBeta (boundaryActualFlags k) β))
      (phaseNormalizedWeights q' W)=
      rectangularComplexZeroMode (phasePairSwapScales m n q) α β (phasePairSwapWeights m n W) := by
  dsimp only
  let q := phaseActualScales A B H k
  let q' := boundaryEmbeddedScales (boundaryActualFlags k) q
  let m := decide (q'.M₂<q'.M₁)
  let n := decide (q'.N₂<q'.N₁)
  let fs := phasePairSwapUnitFlags m n (boundaryActualFlags k)
  let qs := phasePairSwapScales m n q
  let Ws := phasePairSwapWeights m n W
  have hfs := boundaryActual_sorted_unit_flags_discrete A B H k hidx hm hn
  change fs 1=false ∧ fs 3=false at hfs
  have hqs : ∀ j, 0 < qs.size j := by
    have hq := boundaryActual_scales_pos A B H k hA hB hH
    intro j
    cases hm : m <;> cases hn : n <;> fin_cases j <;>
      simp only [qs,phasePairSwapScales,hm,hn,Bool.false_eq_true,ite_false,ite_true,
        QuadraticScales.size]
    all_goals dsimp
    all_goals first
      | exact hq 0
      | exact hq 1
      | exact hq 2
      | exact hq 3
      | exact hq 4
      | exact hq 5
      | exact hq 6
  have hWs : ∀ i, RectangularComplexWeight (Ws i) := by
    intro i
    cases hm : m <;> cases hn : n <;> fin_cases i <;>
      simp only [Ws,phasePairSwapWeights,hm,hn,Bool.false_eq_true,ite_false,ite_true]
    all_goals dsimp
    all_goals first
      | exact hW 0
      | exact hW 1
      | exact hW 2
      | exact hW 3
      | exact hW 4
  have hlow := boundaryActual_flags_low A B H k
  have hm₁ : fs 0=true → qs.M₁=2/3 := by
    cases hm : m <;> simp only [fs,qs,phasePairSwapUnitFlags,phasePairSwapScales,hm,
      Bool.false_eq_true,ite_false,ite_true]
    all_goals dsimp
    · intro hf
      simpa [q,phaseActualScales,QuadraticScales.size,rectangularUnitCoordinate]
        using hlow 0 hf
    · intro hf
      simpa [q,phaseActualScales,QuadraticScales.size,rectangularUnitCoordinate]
        using hlow 1 hf
  have hn₁ : fs 2=true → qs.N₁=2/3 := by
    cases hn : n <;> simp only [fs,qs,phasePairSwapUnitFlags,phasePairSwapScales,hn,
      Bool.false_eq_true,ite_false,ite_true]
    all_goals dsimp
    · intro hf
      simpa [q,phaseActualScales,QuadraticScales.size,rectangularUnitCoordinate]
        using hlow 2 hf
    · intro hf
      simpa [q,phaseActualScales,QuadraticScales.size,rectangularUnitCoordinate]
        using hlow 3 hf
  have hprod := phase_pair_swap_unit_products m n (boundaryActualFlags k)
  change rectangularUnitMFactor fs=rectangularUnitMFactor (boundaryActualFlags k) ∧
    rectangularUnitNFactor fs=rectangularUnitNFactor (boundaryActualFlags k) at hprod
  have he := boundaryEmbedded_discrete_complex_zero_mode fs hfs.1 hfs.2 qs hqs α β Ws hWs hm₁ hn₁
  have hsc := boundaryEmbedded_pair_swap_scales m n (boundaryActualFlags k) q
  change phasePairSwapScales m n q'=boundaryEmbeddedScales fs qs at hsc
  rw [phase_normalized_complex_zero_mode_eq_sorted]
  change rectangularComplexZeroMode (phasePairSwapScales m n q')
    (boundaryEmbeddedAlpha (boundaryActualFlags k) α)
    (boundaryEmbeddedBeta (boundaryActualFlags k) β) Ws=rectangularComplexZeroMode qs α β Ws
  rw [hsc]
  simpa only [boundaryEmbeddedAlpha,boundaryEmbeddedBeta,hprod.1,hprod.2] using he.symm

theorem phase_actual_active_near_zero_mode_back_transport
    {a b s : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hlen : 3*a+5*b < 2) (hs : s < 1/2)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 0 < A → 0 < B → 0 < H →
      ∀ k : Fin 4 → ℕ, phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
      ∀ α β : ℕ → ℂ, ∀ W : Fin 5 → ℝ → ℂ, (∀ i, RectangularComplexWeight (W i)) →
      let q := phaseActualScales A B H k
      let q' := boundaryEmbeddedScales (boundaryActualFlags k) q
      let m := decide (q'.M₂<q'.M₁)
      let n := decide (q'.N₂<q'.N₁)
      rectangularComplexZeroMode (phaseNormalizedScales q')
        (phaseNormalizedAlpha q' (boundaryEmbeddedAlpha (boundaryActualFlags k) α)
          (boundaryEmbeddedBeta (boundaryActualFlags k) β))
        (phaseNormalizedBeta q' (boundaryEmbeddedAlpha (boundaryActualFlags k) α)
          (boundaryEmbeddedBeta (boundaryActualFlags k) β))
        (phaseNormalizedWeights q' W)=
        rectangularComplexZeroMode (phasePairSwapScales m n q) α β (phasePairSwapWeights m n W) := by
  filter_upwards [phase_actual_source_near_double_unit_blocks_excluded ha hab hlen hs f g hf hg]
    with T hunits
  intro A B H hA hB hH k hactive α β W hW
  have hu := hunits A B H hA hB hH k hactive
  obtain ⟨p,q,h,n,positive,hp,hq,hw,hh,hrel,hnear⟩ := hactive
  exact boundaryActual_normalized_zero_mode_eq_native_sorted A B H k hA hB hH
    (boundaryActual_active_indices k n hw) hu.1 hu.2 α β W hW

end
end SixthMoment
