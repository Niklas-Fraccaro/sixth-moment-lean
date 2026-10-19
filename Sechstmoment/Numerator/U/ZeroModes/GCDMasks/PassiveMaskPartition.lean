import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.SoftMaskGeometry

/-! Exact passive completion of the literal finite seven dyadic weights
on the interior region. Its complement consists of actual spatial/gap,
soft-ratio and integrated-unit boundary regions. -/
namespace Sechstmoment
open Complex Real Source Set
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def a03NativeGCDSelectedDyadicMask (select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop)
    (T a b s u ε : ℝ) (f g : ℝ→ℝ) (w : Fin 5→ℕ) (X : ℝ) : ℝ :=
  ∑ i∈a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u)),
    if select i ∧ a03ActualPassiveRatioSourceGoodBlock T s ε f g i then
      a03NativeGCDAllDyadicWeight
        (phaseActualScales (rectangularAFESmoothScale (i.1 0)) (rectangularAFESmoothScale (i.1 1))
          (rectangularAFESmoothScale (i.1 2)) i.2) w X else 0

theorem a03NativeGCDSelectedDyadicMask_bounds
    (select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop) (T a b s u ε : ℝ)
    (f g : ℝ→ℝ) (w : Fin 5→ℕ) (hw : ∀ j,1≤w j) (X : ℝ) :
    0≤a03NativeGCDSelectedDyadicMask select T a b s u ε f g w X ∧
      a03NativeGCDSelectedDyadicMask select T a b s u ε f g w X≤1 := by
  unfold a03NativeGCDSelectedDyadicMask
  have h := a03_native_GCD_selected_grid_weight_bounds
    (a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u)))
    (fun i => select i ∧ a03ActualPassiveRatioSourceGoodBlock T s ε f g i) w hw X
  constructor
  · convert h.1 using 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hs : select i <;>
      by_cases hg : a03ActualPassiveRatioSourceGoodBlock T s ε f g i <;> simp [hs,hg]
  · convert h.2 using 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hs : select i <;>
      by_cases hg : a03ActualPassiveRatioSourceGoodBlock T s ε f g i <;> simp [hs,hg]

theorem a03NativeGCDSevenWeight_continuous (w : Fin 5→ℕ) (k : Fin 7→ℕ) :
    Continuous (fun X : ℝ => a03NativeGCDSevenWeight w X k) := by
  unfold a03NativeGCDSevenWeight
  apply continuous_finsetProd
  intro j _
  apply rectangularSmoothBlockWeight_contDiff.continuous.comp
  apply Continuous.div_const
  fin_cases j <;> dsimp [a03NativeGCDSevenCoordinates] <;> fun_prop

theorem a03NativeGCDSelectedDyadicMask_continuous
    (select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop) (T a b s u ε : ℝ)
    (f g : ℝ→ℝ) (w : Fin 5→ℕ) (hw : ∀ j,1≤w j) :
    Continuous (fun X : ℝ => a03NativeGCDSelectedDyadicMask select T a b s u ε f g w X) := by
  unfold a03NativeGCDSelectedDyadicMask
  apply continuous_finsetSum
  intro i _
  by_cases hP : select i ∧ a03ActualPassiveRatioSourceGoodBlock T s ε f g i
  · simp only [hP]
    convert a03NativeGCDSevenWeight_continuous w (a03GCDScaleTuple i) using 1
    funext X
    exact a03_native_GCD_all_weight_eq_seven_weight i w hw X
  · simp only [hP]
    exact continuous_const

theorem a03_native_GCD_interior_weight_passive_good
    (T s ε : ℝ) (hε : 0≤ε) (f g : ℝ→ℝ)
    (w : Fin 5→ℕ) (X : ℝ) (hX : 0<X)
    (hf : f (Real.log (w 0:ℝ)/Real.log T)≠0)
    (hg : g (Real.log (w 1:ℝ)/Real.log T)≠0)
    (hlow : a03NativeGCDCoordinateGap w≤T^(s-1)*X)
    (hM₂ : 4/3<X/((w 0:ℝ)*w 2)) (hN₂ : 4/3<X/((w 1:ℝ)*w 3))
    (hMratio : (w 0:ℝ)*(w 2:ℝ)^2/X<((X^2/64)^ε)/64)
    (hNratio : (w 1:ℝ)*(w 3:ℝ)^2/X<((X^2/64)^ε)/64)
    (i : (Fin 3→ℕ)×(Fin 4→ℕ))
    (hi : a03NativeGCDAllDyadicWeight
      (phaseActualScales (rectangularAFESmoothScale (i.1 0)) (rectangularAFESmoothScale (i.1 1))
        (rectangularAFESmoothScale (i.1 2)) i.2) w X≠0) :
    a03ActualPassiveRatioSourceGoodBlock T s ε f g i := by
  let A := rectangularAFESmoothScale (i.1 0)
  let B := rectangularAFESmoothScale (i.1 1)
  let H := rectangularAFESmoothScale (i.1 2)
  have hA : 0<A := boundaryActual_scale_pos _
  have hB : 0<B := boundaryActual_scale_pos _
  have hH : 0<H := boundaryActual_scale_pos _
  obtain ⟨p,hpw,hpX⟩ := a03_native_GCD_low_gap_nonzero_weight_witness T A B H (T^(s-1)) f g i.2
    hA hB hH w X hX hi hf hg hlow
  let q := phaseActualScales A B H i.2
  let qe := boundaryEmbeddedScales (boundaryActualFlags i.2) q
  have hm : X^2≤64*q.mass := by simpa only [hpX] using p.mass_product_bound hA hB
  have hmass : X^2/64≤qe.mass := by
    have hn : 0≤q.mass := (a03_actual_scales_mass_pos hA hB i.2).le
    exact (by linarith only [hm] : X^2/64≤q.mass).trans (boundaryEmbedded_mass_le _ _ hn)
  have hp : (X^2/64)^ε≤qe.mass^ε := Real.rpow_le_rpow (by positivity) hmass hε
  have hM : qe.M₁≤qe.M₂*qe.mass^ε := by
    by_contra hb
    have h := p.bad_soft_M_ratio hA hB hH hb
    rw [hpw,hpX] at h
    exact (not_lt_of_ge ((div_le_div_of_nonneg_right hp (by norm_num)).trans h)) hMratio
  have hN : qe.N₁≤qe.N₂*qe.mass^ε := by
    by_contra hb
    have h := p.bad_soft_N_ratio hA hB hH hb
    rw [hpw,hpX] at h
    exact (not_lt_of_ge ((div_le_div_of_nonneg_right hp (by norm_num)).trans h)) hNratio
  have hkM : i.2 1≠0 := by
    intro hk
    have h := p.integrated_unit_bounds.1 hk
    rw [hpw,hpX] at h
    exact (not_lt_of_ge h) hM₂
  have hkN : i.2 3≠0 := by
    intro hk
    have h := p.integrated_unit_bounds.2 hk
    rw [hpw,hpX] at h
    exact (not_lt_of_ge h) hN₂
  exact ⟨⟨p⟩,hM,hN,hkM,hkN⟩

/-- The actual passive seven-grid mask equals one wherever the actual
point caps, near-gap bound, nonunit real scales and small-ratio conditions hold. -/
theorem a03_native_GCD_passive_mask_partition
    {T : ℝ} (hT : 0<T) (a b s u ε : ℝ) (hε : 0≤ε) (f g : ℝ→ℝ)
    (w : Fin 5→ℕ) (hw : ∀ j,1≤w j) (X : ℝ) (hX : 0<X)
    (hf : f (Real.log (w 0:ℝ)/Real.log T)≠0)
    (hg : g (Real.log (w 1:ℝ)/Real.log T)≠0)
    (ha : (w 0:ℝ)≤T^a) (hb : (w 1:ℝ)≤T^b)
    (hh : a03NativeGCDCoordinateGap w≤8*T^((a+b)/2+s+u/2))
    (hprod : X^2/((w 0:ℝ)*w 1)≤T^(2+u))
    (hlow : a03NativeGCDCoordinateGap w≤T^(s-1)*X)
    (hM₂ : 4/3<X/((w 0:ℝ)*w 2)) (hN₂ : 4/3<X/((w 1:ℝ)*w 3))
    (hMratio : (w 0:ℝ)*(w 2:ℝ)^2/X<((X^2/64)^ε)/64)
    (hNratio : (w 1:ℝ)*(w 3:ℝ)^2/X<((X^2/64)^ε)/64) :
    a03NativeGCDSelectedDyadicMask (fun _ => True) T a b s u ε f g w X=1 := by
  unfold a03NativeGCDSelectedDyadicMask
  have he := a03_native_GCD_actual_grid_partition
    (Real.rpow_pos_of_pos hT a) (Real.rpow_pos_of_pos hT b)
    (by positivity : 0<8*T^((a+b)/2+s+u/2)) (Real.rpow_pos_of_pos hT (2+u))
    w hw X ha hb hh hprod (by linarith) (by linarith)
  apply Eq.trans _ he
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : a03NativeGCDAllDyadicWeight
      (phaseActualScales (rectangularAFESmoothScale (i.1 0)) (rectangularAFESmoothScale (i.1 1))
        (rectangularAFESmoothScale (i.1 2)) i.2) w X=0
  · simp only [hi,ite_self]
  · have hgood := a03_native_GCD_interior_weight_passive_good T s ε hε f g w X hX hf hg hlow hM₂ hN₂ hMratio hNratio i hi
    simp only [hgood,and_self,ite_true]


/-- Failure of the literal passive mask belongs to an actual omitted
spatial/gap, real-unit or large-ratio region. -/
theorem a03_native_GCD_passive_mask_complement
    {T : ℝ} (hT : 0<T) (a b s u ε : ℝ) (hε : 0≤ε) (f g : ℝ→ℝ)
    (w : Fin 5→ℕ) (hw : ∀ j,1≤w j) (X : ℝ) (hX : 0<X)
    (hf : f (Real.log (w 0:ℝ)/Real.log T)≠0)
    (hg : g (Real.log (w 1:ℝ)/Real.log T)≠0)
    (ha : (w 0:ℝ)≤T^a) (hb : (w 1:ℝ)≤T^b)
    (hmask : a03NativeGCDSelectedDyadicMask (fun _ => True) T a b s u ε f g w X≠1) :
    T^(2+u)<X^2/((w 0:ℝ)*w 1) ∨
      8*T^((a+b)/2+s+u/2)<a03NativeGCDCoordinateGap w ∨
      T^(s-1)*X<a03NativeGCDCoordinateGap w ∨
      X/((w 0:ℝ)*w 2)≤4/3 ∨ X/((w 1:ℝ)*w 3)≤4/3 ∨
      ((X^2/64)^ε)/64≤(w 0:ℝ)*(w 2:ℝ)^2/X ∨
      ((X^2/64)^ε)/64≤(w 1:ℝ)*(w 3:ℝ)^2/X := by
  by_contra h
  push Not at h
  rcases h with ⟨hp,hh,hgap,hM₂,hN₂,hM,hN⟩
  exact hmask (a03_native_GCD_passive_mask_partition hT a b s u ε hε f g w hw X hX hf hg ha hb hh hp hgap hM₂ hN₂ hM hN)

end
end Sechstmoment
