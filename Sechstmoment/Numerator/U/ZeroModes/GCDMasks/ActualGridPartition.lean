import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.DyadicPartition

namespace Sechstmoment
open Complex Real Source Set MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem a03NativeGCDSevenWeight_nonzero_scale_lower (w : Fin 5→ℕ) (X : ℝ)
    (k : Fin 7→ℕ) (hw : a03NativeGCDSevenWeight w X k≠0) (j : Fin 7) :
    rectangularAFESmoothScale (k j)≤a03NativeGCDSevenCoordinates w X j := by
  have hz := (Finset.prod_ne_zero_iff.mp hw) j (Finset.mem_univ j)
  have hs := rectangularSmoothBlockWeight_tsupport (subset_tsupport _ hz)
  exact (by simpa only [one_mul] using (le_div_iff₀ (boundaryActual_scale_pos _)).mp hs.1)

theorem a03NativeGCDSevenWeight_nonzero_actual_grid
    {A B H P : ℝ} (hA : 0<A) (hB : 0<B) (hH : 0<H) (hP : 0<P)
    (w : Fin 5→ℕ) (hw : ∀ j,1≤w j) (X : ℝ)
    (ha : (w 0:ℝ)≤A) (hb : (w 1:ℝ)≤B)
    (hh : (Nat.gcd (w 0*w 2) (w 1*w 3):ℝ)*w 4≤H)
    (hprod : X^2/((w 0:ℝ)*w 1)≤P)
    (k : Fin 7→ℕ) (hk : a03NativeGCDSevenWeight w X k≠0) :
    a03GCDScaleBlock k∈a03ActualSourceBlockGrid A B H P := by
  have hs := a03NativeGCDSevenWeight_nonzero_scale_lower w X k hk
  unfold a03ActualSourceBlockGrid
  apply Finset.mem_product.mpr
  constructor
  · apply Fintype.mem_piFinset.mpr
    intro j
    fin_cases j
    · exact a03SourceScaleGrid_mem_of_scale_le hA _ ((hs 0).trans ha)
    · exact a03SourceScaleGrid_mem_of_scale_le hB _ ((hs 1).trans hb)
    · exact a03SourceScaleGrid_mem_of_scale_le hH _ ((hs 2).trans hh)
  · rw [rectangular_AFE_product_scale_grid_mem_iff hP]
    have hp (j : Fin 4) : rectangularAFESmoothScale ((a03GCDScaleBlock k).2 j)≤a03NativeGCDCoordinateQuad w X j := by
      fin_cases j
      · exact hs 3
      · exact hs 4
      · exact hs 5
      · exact hs 6
    have hm : (∏ j : Fin 4,rectangularAFESmoothScale ((a03GCDScaleBlock k).2 j))≤∏ j : Fin 4,a03NativeGCDCoordinateQuad w X j := Finset.prod_le_prod₀ (fun j _ => (boundaryActual_scale_pos _).le) (fun j _ => hp j)
    exact hm.trans ((a03NativeGCDCoordinateQuad_product w hw X).trans_le hprod)

theorem a03NativeGCDSevenWeight_hasSum_one (w : Fin 5→ℕ) (hw : ∀ j,1≤w j)
    (X : ℝ) (hM₂ : 1≤X/((w 0:ℝ)*w 2)) (hN₂ : 1≤X/((w 1:ℝ)*w 3)) :
    HasSum (a03NativeGCDSevenWeight w X) 1 := by
  have hcoords : ∀ j : Fin 7,1≤a03NativeGCDSevenCoordinates w X j := by
    have hd : (1:ℝ)≤Nat.gcd (w 0*w 2) (w 1*w 3) := by
      exact_mod_cast (show 1≤Nat.gcd (w 0*w 2) (w 1*w 3) by
        have hd := Nat.gcd_pos_of_pos_left (w 1*w 3)
          (Nat.mul_pos (show 0<w 0 by have := hw 0; omega) (show 0<w 2 by have := hw 2; omega))
        omega)
    intro j
    fin_cases j
    · change (1:ℝ)≤w 0
      exact_mod_cast hw 0
    · change (1:ℝ)≤w 1
      exact_mod_cast hw 1
    · have hh : (1:ℝ)≤w 4 := by exact_mod_cast hw 4
      exact one_le_mul_of_one_le_of_one_le hd hh
    · change (1:ℝ)≤w 2
      exact_mod_cast hw 2
    · exact hM₂
    · change (1:ℝ)≤w 3
      exact_mod_cast hw 3
    · exact hN₂
  have hs := rectangular_finitePi_hasSum_prod_nonneg 7
    (fun j k => rectangularSmoothBlockWeight (a03NativeGCDSevenCoordinates w X j/rectangularAFESmoothScale k))
    (fun _ => (1:ℝ)) (fun _ _ => rectangularSmoothBlockWeight_nonneg _) (fun j => by
      have ht := (a03_smooth_scale_weight_summable (a03NativeGCDSevenCoordinates w X j)).hasSum
      have he : (∑' k : ℕ,rectangularSmoothBlockWeight (a03NativeGCDSevenCoordinates w X j/rectangularAFESmoothScale k))=1 := by
        simp_rw [a03_smooth_scale_weight_argument]
        exact rectangularSmoothBlockWeight_tsum (hcoords j)
      rwa [he] at ht)
  convert hs using 1
  · rfl
  · simp only [Finset.prod_const_one]

theorem a03_native_GCD_actual_grid_partition
    {A B H P : ℝ} (hA : 0<A) (hB : 0<B) (hH : 0<H) (hP : 0<P)
    (w : Fin 5→ℕ) (hw : ∀ j,1≤w j) (X : ℝ)
    (ha : (w 0:ℝ)≤A) (hb : (w 1:ℝ)≤B)
    (hh : (Nat.gcd (w 0*w 2) (w 1*w 3):ℝ)*w 4≤H)
    (hprod : X^2/((w 0:ℝ)*w 1)≤P)
    (hM₂ : 1≤X/((w 0:ℝ)*w 2)) (hN₂ : 1≤X/((w 1:ℝ)*w 3)) :
    (∑ i∈a03ActualSourceBlockGrid A B H P,a03NativeGCDAllDyadicWeight
      (phaseActualScales (rectangularAFESmoothScale (i.1 0)) (rectangularAFESmoothScale (i.1 1))
        (rectangularAFESmoothScale (i.1 2)) i.2) w X)=1 := by
  let S := a03ActualSourceBlockGrid A B H P
  have hs := a03NativeGCDSevenWeight_hasSum_one w hw X hM₂ hN₂
  have hz (k : Fin 7→ℕ) (hk : k∉S.image a03GCDScaleTuple) : a03NativeGCDSevenWeight w X k=0 := by
    by_contra h
    have hi := a03NativeGCDSevenWeight_nonzero_actual_grid hA hB hH hP w hw X ha hb hh hprod k h
    exact hk (Finset.mem_image.mpr ⟨a03GCDScaleBlock k,hi,a03GCDScaleTuple_block k⟩)
  have he : (∑' k : Fin 7→ℕ,a03NativeGCDSevenWeight w X k)=∑ k∈S.image a03GCDScaleTuple,a03NativeGCDSevenWeight w X k := tsum_eq_sum hz
  rw [hs.tsum_eq] at he
  rw [he]
  simp_rw [a03_native_GCD_all_weight_eq_seven_weight _ w hw X]
  apply Finset.sum_bij (fun i _ => a03GCDScaleTuple i)
  · intro i hi
    exact Finset.mem_image.mpr ⟨i,hi,rfl⟩
  · intro i _ j _ hij
    have h := congrArg a03GCDScaleBlock hij
    simpa only [a03GCDScaleBlock_tuple] using h
  · intro k hk
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hk
    exact ⟨i,hi,he⟩
  · intro i _
    rfl

end
end Sechstmoment
