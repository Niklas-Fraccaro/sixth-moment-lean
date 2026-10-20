import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.DyadicSupport

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem a03_smooth_block_tsum_real (x : ℝ) :
    (∑' k : ℕ,rectangularSmoothBlockWeight ((3/2)*x/(3/2)^k))=
      1-rectangularSmoothCutoff ((3/2)^2*x) := by
  obtain ⟨N,hN⟩ := rectangularSmoothBlockWeight_eventually_zero x
  have ht : Tendsto (fun n : ℕ => (3/2)*x/(3/2)^n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  obtain ⟨M,hM⟩ := eventually_atTop.1
    (ht.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<3/2)))
  have hz (k : ℕ) (hk : k∉Finset.range (max N M+1)) :
      rectangularSmoothBlockWeight ((3/2)*x/(3/2)^k)=0 := by
    apply hN k
    have h := Nat.le_of_not_gt (fun hl => hk (Finset.mem_range.mpr hl))
    exact (le_max_left N M).trans ((Nat.le_succ _).trans h)
  rw [tsum_eq_sum hz,rectangularSmoothBlockWeight_sum,
    rectangularSmoothCutoff_one (hM _ (le_max_right _ _))]

theorem a03_smooth_scale_weight_argument (x : ℝ) (k : ℕ) :
    x/rectangularAFESmoothScale k=(3/2)*x/(3/2)^k := by
  unfold rectangularAFESmoothScale
  field_simp

theorem a03_smooth_scale_weight_summable (x : ℝ) :
    Summable (fun k : ℕ => rectangularSmoothBlockWeight (x/rectangularAFESmoothScale k)) := by
  simp_rw [a03_smooth_scale_weight_argument]
  exact rectangularSmoothBlockWeight_summable x

theorem a03_smooth_scale_weight_tsum_bounds (x : ℝ) :
    0≤(∑' k : ℕ,rectangularSmoothBlockWeight (x/rectangularAFESmoothScale k)) ∧
      (∑' k : ℕ,rectangularSmoothBlockWeight (x/rectangularAFESmoothScale k))≤1 := by
  refine ⟨tsum_nonneg (fun _ => rectangularSmoothBlockWeight_nonneg _),?_⟩
  simp_rw [a03_smooth_scale_weight_argument]
  rw [a03_smooth_block_tsum_real]
  unfold rectangularSmoothCutoff
  linarith [Real.smoothTransition.le_one (2*((3/2)^2*x)-3)]

def a03GCDScaleTuple (i : (Fin 3→ℕ)×(Fin 4→ℕ)) : Fin 7→ℕ :=
  ![i.1 0,i.1 1,i.1 2,i.2 0,i.2 1,i.2 2,i.2 3]

def a03GCDScaleBlock (k : Fin 7→ℕ) : (Fin 3→ℕ)×(Fin 4→ℕ) :=
  (![k 0,k 1,k 2],![k 3,k 4,k 5,k 6])

@[simp] theorem a03GCDScaleBlock_tuple (i : (Fin 3→ℕ)×(Fin 4→ℕ)) :
    a03GCDScaleBlock (a03GCDScaleTuple i)=i := by
  apply Prod.ext
  · ext j; fin_cases j <;> rfl
  · ext j; fin_cases j <;> rfl

@[simp] theorem a03GCDScaleTuple_block (k : Fin 7→ℕ) :
    a03GCDScaleTuple (a03GCDScaleBlock k)=k := by
  ext j; fin_cases j <;> rfl

def a03NativeGCDSevenCoordinates (w : Fin 5→ℕ) (X : ℝ) : Fin 7→ℝ :=
  ![(w 0:ℝ),(w 1:ℝ),(Nat.gcd (w 0*w 2) (w 1*w 3):ℝ)*w 4,
    (w 2:ℝ),X/((w 0:ℝ)*w 2),(w 3:ℝ),X/((w 1:ℝ)*w 3)]

def a03NativeGCDSevenWeight (w : Fin 5→ℕ) (X : ℝ) (k : Fin 7→ℕ) : ℝ :=
  ∏ j : Fin 7,rectangularSmoothBlockWeight
    (a03NativeGCDSevenCoordinates w X j/rectangularAFESmoothScale (k j))

theorem a03_native_GCD_seven_weight_total (w : Fin 5→ℕ) (X : ℝ) :
    Summable (a03NativeGCDSevenWeight w X) ∧
      (∑' k : Fin 7→ℕ,a03NativeGCDSevenWeight w X k)≤1 := by
  let f := fun j : Fin 7 => fun k : ℕ => rectangularSmoothBlockWeight
    (a03NativeGCDSevenCoordinates w X j/rectangularAFESmoothScale k)
  let totals := fun j : Fin 7 => ∑' k : ℕ,f j k
  have hs := rectangular_finitePi_hasSum_prod_nonneg 7 f totals
    (fun _ _ => rectangularSmoothBlockWeight_nonneg _) (fun j => (a03_smooth_scale_weight_summable _).hasSum)
  refine ⟨hs.summable,?_⟩
  change (∑' k : Fin 7→ℕ,∏ j,f j (k j))≤1
  rw [hs.tsum_eq]
  exact (Finset.prod_le_prod₀ (fun j _ => (a03_smooth_scale_weight_tsum_bounds _).1)
    (fun j _ => (a03_smooth_scale_weight_tsum_bounds _).2)).trans_eq Finset.prod_const_one

theorem a03_native_GCD_seven_weight_partial_le_one (w : Fin 5→ℕ) (X : ℝ)
    (S : Finset (Fin 7→ℕ)) : (∑ k∈S,a03NativeGCDSevenWeight w X k)≤1 := by
  obtain ⟨hs,hbound⟩ := a03_native_GCD_seven_weight_total w X
  exact (hs.sum_le_tsum S (fun _ _ => Finset.prod_nonneg
    (fun _ _ => rectangularSmoothBlockWeight_nonneg _))).trans hbound

theorem a03_native_GCD_all_weight_eq_seven_weight
    (i : (Fin 3→ℕ)×(Fin 4→ℕ)) (w : Fin 5→ℕ) (hw : ∀ j,1≤w j) (X : ℝ) :
    a03NativeGCDAllDyadicWeight
      (phaseActualScales (rectangularAFESmoothScale (i.1 0)) (rectangularAFESmoothScale (i.1 1))
        (rectangularAFESmoothScale (i.1 2)) i.2) w X=
      a03NativeGCDSevenWeight w X (a03GCDScaleTuple i) := by
  let q := phaseActualScales (rectangularAFESmoothScale (i.1 0)) (rectangularAFESmoothScale (i.1 1))
    (rectangularAFESmoothScale (i.1 2)) i.2
  have hc := a03NativeGCDCoordinateArguments_quad q w hw X
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  norm_num [q,a03ZeroModeQuadScales,phaseActualScales] at h0 h1 h2 h3
  change a03NativeGCDAllDyadicWeight q w X=_
  norm_num [a03NativeGCDAllDyadicWeight,a03NativeGCDSevenWeight,a03NativeGCDSevenCoordinates,
    a03GCDScaleTuple,Fin.prod_univ_succ]
  rw [a03NativeGCDCoordinateArguments_gap]
  erw [h0,h1,h2,h3]
  simp [q,phaseActualScales,a03NativeGCDCoordinateQuad]
  ring

theorem a03_native_GCD_selected_grid_weight_bounds
    (S : Finset ((Fin 3→ℕ)×(Fin 4→ℕ))) (P : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop)
    (w : Fin 5→ℕ) (hw : ∀ j,1≤w j) (X : ℝ) :
    0≤(∑ i∈S,if P i then a03NativeGCDAllDyadicWeight
      (phaseActualScales (rectangularAFESmoothScale (i.1 0)) (rectangularAFESmoothScale (i.1 1))
        (rectangularAFESmoothScale (i.1 2)) i.2) w X else 0) ∧
    (∑ i∈S,if P i then a03NativeGCDAllDyadicWeight
      (phaseActualScales (rectangularAFESmoothScale (i.1 0)) (rectangularAFESmoothScale (i.1 1))
        (rectangularAFESmoothScale (i.1 2)) i.2) w X else 0)≤1 := by
  simp_rw [a03_native_GCD_all_weight_eq_seven_weight _ w hw X]
  have hnn (i : (Fin 3→ℕ)×(Fin 4→ℕ)) : 0≤a03NativeGCDSevenWeight w X (a03GCDScaleTuple i) :=
    Finset.prod_nonneg (fun _ _ => rectangularSmoothBlockWeight_nonneg _)
  refine ⟨Finset.sum_nonneg (fun i _ => by split_ifs; exact hnn i; exact le_rfl),?_⟩
  apply (Finset.sum_le_sum (fun i _ => by split_ifs; exact le_rfl; exact hnn i)).trans
  have he : (∑ i∈S,a03NativeGCDSevenWeight w X (a03GCDScaleTuple i))=
      ∑ k∈S.image a03GCDScaleTuple,a03NativeGCDSevenWeight w X k := by
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
  rw [he]
  exact a03_native_GCD_seven_weight_partial_le_one w X _

end
end Sechstmoment
