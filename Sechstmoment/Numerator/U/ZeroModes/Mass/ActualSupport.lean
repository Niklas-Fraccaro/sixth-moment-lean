import Sechstmoment.Numerator.U.ZeroModes.Mass.Denominator

/-! Actual native sorted zero-mode masks force all four physical real
variables to be at least one and supply their genuine product cutoff. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def a03ZeroModePhysicalQuad (_q : QuadraticScales) (v : Fin 5→ℕ) (x : ℝ) : Fin 4→ℝ :=
  let d : ℝ := Nat.gcd (v 0*v 2) (v 1*v 3)
  ![(v 2:ℝ),(v 1:ℝ)*v 3/d*x,(v 3:ℝ),(v 0:ℝ)*v 2/d*x]

def a03ZeroModeQuadScales (q : QuadraticScales) : Fin 4→ℝ := ![q.M₁,q.M₂,q.N₁,q.N₂]

/-- The literal source GCD physical fourfold product gives the exact
sixfold reciprocal square-root density, including both amplifier variables. -/
theorem a03ZeroModePhysicalQuad_six_density (q : QuadraticScales)
    (v : Fin 5→ℕ) (hv : ∀ j,1≤v j) {x : ℝ} (hx : 0<x) :
    1/Real.sqrt ((v 0:ℝ)*v 1*(∏ j : Fin 4,a03ZeroModePhysicalQuad q v x j))=
      (Nat.gcd (v 0*v 2) (v 1*v 3):ℝ)/((v 0:ℝ)*v 1*v 2*v 3*x) := by
  have hp (j : Fin 5) : 0<v j := by have := hv j; omega
  have he := a03ZeroModeSixDensity_gcd_eq (hp 0) (hp 1) (hp 2) (hp 3) hx
  convert he using 1
  unfold a03ZeroModeSixDensity a03ZeroModeContinuousM₂ a03ZeroModeContinuousN₂ a03ZeroModePhysicalQuad
  simp only [Fin.prod_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  congr 2
  ring

theorem a03ZeroModePhysicalQuad_normalized (q : QuadraticScales) (v : Fin 5→ℕ) (x : ℝ) (j : Fin 4) :
    rectangularZeroArguments q v x j.succ=
      a03ZeroModePhysicalQuad q v x j/a03ZeroModeQuadScales q j := by
  fin_cases j <;> simp [a03ZeroModePhysicalQuad,a03ZeroModeQuadScales,rectangularZeroArguments,
    div_eq_mul_inv,mul_inv_rev,mul_comm,mul_left_comm,mul_assoc]

theorem a03ZeroModePhysicalQuad_nonzero_mask_bounds (q : QuadraticScales)
    (hq : ∀ j,0<q.size j) (hM₂ : 1≤q.M₂) (hN₂ : 1≤q.N₂)
    (v : Fin 5→ℕ) (hv : v∈quadraticMainIndexSet q) (x : ℝ)
    (hw : (∏ i : Fin 5,rectangularSmoothBlockWeight (rectangularZeroArguments q v x i))≠0) :
    (∀ j,1≤a03ZeroModePhysicalQuad q v x j) ∧
      (∏ j : Fin 4,a03ZeroModePhysicalQuad q v x j)≤16*(q.M*q.N) := by
  have hscale (j : Fin 4) : 0<a03ZeroModeQuadScales q j := by
    fin_cases j <;> simp [a03ZeroModeQuadScales]
    · simpa [QuadraticScales.size] using hq 2
    · simpa [QuadraticScales.size] using hq 3
    · simpa [QuadraticScales.size] using hq 4
    · simpa [QuadraticScales.size] using hq 5
  have hmask (i : Fin 5) : rectangularZeroArguments q v x i∈Icc (1:ℝ) 2 := by
    have hi : rectangularSmoothBlockWeight (rectangularZeroArguments q v x i)≠0 := by
      intro hz
      exact hw (Finset.prod_eq_zero (Finset.mem_univ i) hz)
    exact rectangularSmoothBlockWeight_tsupport (subset_tsupport _ hi)
  have hb (j : Fin 4) : a03ZeroModeQuadScales q j≤a03ZeroModePhysicalQuad q v x j ∧
      a03ZeroModePhysicalQuad q v x j≤2*a03ZeroModeQuadScales q j := by
    have hh := hmask j.succ
    rw [a03ZeroModePhysicalQuad_normalized] at hh
    exact ⟨by simpa only [one_mul] using (le_div_iff₀ (hscale j)).mp hh.1,
      (div_le_iff₀ (hscale j)).mp hh.2⟩
  have hn (j : Fin 5) : 1≤(v j:ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hv j)).1
  have hlower (j : Fin 4) : 1≤a03ZeroModePhysicalQuad q v x j := by
    fin_cases j
    · exact hn 2
    · exact hM₂.trans (hb 1).1
    · exact hn 3
    · exact hN₂.trans (hb 3).1
  refine ⟨hlower,?_⟩
  calc
    _≤∏ j : Fin 4,2*a03ZeroModeQuadScales q j := Finset.prod_le_prod₀
      (fun j _ => (zero_le_one.trans (hlower j))) (fun j _ => (hb j).2)
    _=16*(q.M*q.N) := by
      simp [Fin.prod_univ_four,a03ZeroModeQuadScales,QuadraticScales.M,QuadraticScales.N]
      ring

theorem a03_actual_sorted_integrated_scales_ge_one (A B H : ℝ) (k : Fin 4→ℕ)
    (hidx : ∀ j,k j≠1) (hm : ¬(k 0=0 ∧ k 1=0)) (hn : ¬(k 2=0 ∧ k 3=0)) :
    let q := phaseActualScales A B H k
    let q' := boundaryEmbeddedScales (boundaryActualFlags k) q
    let m := decide (q'.M₂<q'.M₁)
    let n := decide (q'.N₂<q'.N₁)
    1≤(phasePairSwapScales m n q).M₂ ∧ 1≤(phasePairSwapScales m n q).N₂ := by
  have hflags := boundaryActual_sorted_unit_flags_discrete A B H k hidx hm hn
  dsimp only at hflags ⊢
  constructor
  · generalize decide ((boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).M₂<
        (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).M₁)=m at hflags ⊢
    cases m
    · have hzero : k 1≠0 := by simpa [phasePairSwapUnitFlags,boundaryActualFlags] using hflags.1
      exact rectangular_AFE_smooth_scale_ge_one (by omega)
    · have hzero : k 0≠0 := by simpa [phasePairSwapUnitFlags,boundaryActualFlags] using hflags.1
      exact rectangular_AFE_smooth_scale_ge_one (by omega)
  · generalize decide ((boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).N₂<
        (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).N₁)=n at hflags ⊢
    cases n
    · have hzero : k 3≠0 := by simpa [phasePairSwapUnitFlags,boundaryActualFlags] using hflags.2
      exact rectangular_AFE_smooth_scale_ge_one (by omega)
    · have hzero : k 2≠0 := by simpa [phasePairSwapUnitFlags,boundaryActualFlags] using hflags.2
      exact rectangular_AFE_smooth_scale_ge_one (by omega)

private theorem pairSwap_scales_positive (q : QuadraticScales) (hq : ∀ j,0<q.size j) (m n : Bool) :
    ∀ j,0<(phasePairSwapScales m n q).size j := by
  intro j
  cases m <;> cases n <;> fin_cases j <;>
    simp only [phasePairSwapScales,QuadraticScales.size,Bool.false_eq_true,ite_false,ite_true] <;>
      first | exact hq 0 | exact hq 1 | exact hq 2 | exact hq 3 | exact hq 4 | exact hq 5 | exact hq 6

theorem a03_actual_sorted_zero_real_denominator_bound
    {T R η : ℝ} (hT : 0<T) (hlog : 1≤Real.log T) (hR : 0≤R)
    (A B H : ℝ) (hA : 0<A) (hB : 0<B) (hH : 0<H) (k : Fin 4→ℕ)
    (hk : k∈rectangularAFEProductScaleGrid (T^(2+η))) (hidx : ∀ j,k j≠1)
    (hm : ¬(k 0=0 ∧ k 1=0)) (hn : ¬(k 2=0 ∧ k 3=0))
    (σ : MomentShifts) (hσ : ∀ j,‖σ j‖≤R) (l : Fin 6) (z : ℂ) (hz : 0≤z.re) :
    let q := phaseActualScales A B H k
    let q' := boundaryEmbeddedScales (boundaryActualFlags k) q
    let m := decide (q'.M₂<q'.M₁)
    let n := decide (q'.N₂<q'.N₁)
    let qs := phasePairSwapScales m n q
    ∀ v : Fin 5→ℕ,v∈quadraticMainIndexSet qs → ∀ x : ℝ,
      (∏ i : Fin 5,rectangularSmoothBlockWeight (rectangularZeroArguments qs v x i))≠0 →
      ‖(a03ZeroModeRealQuadDenominator (bblrSixShifts (rawMomentShifts T σ) l) z
        (a03ZeroModePhysicalQuad qs v x))⁻¹‖≤
          Real.exp (R*(Real.log 16+(2+η)))/Real.sqrt (∏ j : Fin 4,a03ZeroModePhysicalQuad qs v x j) := by
  dsimp only
  let q := phaseActualScales A B H k
  let q' := boundaryEmbeddedScales (boundaryActualFlags k) q
  let m := decide (q'.M₂<q'.M₁)
  let n := decide (q'.N₂<q'.N₁)
  let qs := phasePairSwapScales m n q
  have hscale := a03_actual_sorted_integrated_scales_ge_one A B H k hidx hm hn
  have hqs : ∀ j,0<qs.size j :=
    pairSwap_scales_positive q (boundaryActual_scales_pos A B H k hA hB hH) m n
  have hcut : qs.M*qs.N≤T^(2+η) := by
    rw [(phase_pair_swap_products m n q).1,(phase_pair_swap_products m n q).2.1]
    simpa [q,phaseActualScales,QuadraticScales.M,QuadraticScales.N,Fin.prod_univ_four,mul_assoc]
      using (Finset.mem_filter.mp hk).2
  intro v hv x hw
  have hb := a03ZeroModePhysicalQuad_nonzero_mask_bounds qs hqs hscale.1 hscale.2 v hv x hw
  exact a03ZeroModeRealQuadDenominator_raw_inv_norm_le hT hlog (by norm_num : (1:ℝ)≤16) hR
    σ hσ l z hz _ hb.1 (hb.2.trans (mul_le_mul_of_nonneg_left hcut (by norm_num)))

end
end Sechstmoment
