import Sechstmoment.Numerator.U.ZeroModes.NativeRatioGCD

/-! A genuine supported continuous native GCD zero point in the low gap
range. This predicate does not assert an integer quadratic source relation. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03NativeGCDCoordinateGap (w : Fin 5→ℕ) : ℝ :=
  (Nat.gcd (w 0*w 2) (w 1*w 3):ℝ)*(w 4:ℝ)

structure A03PassiveNativeZeroWitness (T A B H η : ℝ) (f g : ℝ→ℝ) (k : Fin 4→ℕ) where
  w : Fin 5→ℕ
  mem : w∈quadraticMainIndexSet (phaseActualScales A B H k)
  X : ℝ
  X_pos : 0<X
  alpha_nonzero : phaseActualAmplifierCoefficient T f A (w 0)≠0
  beta_nonzero : phaseActualAmplifierCoefficient T g B (w 1)≠0
  mask_nonzero : (∏ j : Fin 5,rectangularSmoothBlockWeight
    (a03NativeGCDCoordinateArguments false false (phaseActualScales A B H k) w X j.succ))≠0
  low_gap : a03NativeGCDCoordinateGap w≤η*X

def A03ActualPassiveNearZeroBlock (T A B H η : ℝ) (f g : ℝ→ℝ) (k : Fin 4→ℕ) : Prop :=
  Nonempty (A03PassiveNativeZeroWitness T A B H η f g k)

theorem A03PassiveNativeZeroWitness.integer_pos {T A B H η : ℝ} {f g : ℝ→ℝ} {k : Fin 4→ℕ}
    (p : A03PassiveNativeZeroWitness T A B H η f g k) (j : Fin 5) : 1≤p.w j :=
  (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp p.mem j)).1

theorem A03PassiveNativeZeroWitness.mask_support {T A B H η : ℝ} {f g : ℝ→ℝ} {k : Fin 4→ℕ}
    (p : A03PassiveNativeZeroWitness T A B H η f g k) (j : Fin 5) :
    a03NativeGCDCoordinateArguments false false (phaseActualScales A B H k) p.w p.X j.succ∈Icc (1:ℝ) 2 := by
  have hn : rectangularSmoothBlockWeight
      (a03NativeGCDCoordinateArguments false false (phaseActualScales A B H k) p.w p.X j.succ)≠0 :=
    (Finset.prod_ne_zero_iff.mp p.mask_nonzero) j (Finset.mem_univ j)
  exact rectangularSmoothBlockWeight_tsupport (subset_tsupport _ hn)

theorem A03PassiveNativeZeroWitness.amplifier_support {T A B H η : ℝ} {f g : ℝ→ℝ} {k : Fin 4→ℕ}
    (p : A03PassiveNativeZeroWitness T A B H η f g k) (hA : 0<A) (hB : 0<B) :
    (p.w 0:ℝ)∈Icc A (2*A) ∧ (p.w 1:ℝ)∈Icc B (2*B) := by
  constructor
  · by_contra hn
    exact p.alpha_nonzero (phaseActualAmplifierCoefficient_support T f hA (p.w 0) hn)
  · by_contra hn
    exact p.beta_nonzero (phaseActualAmplifierCoefficient_support T g hB (p.w 1) hn)

theorem A03PassiveNativeZeroWitness.quad_support {T A B H η : ℝ} {f g : ℝ→ℝ} {k : Fin 4→ℕ}
    (p : A03PassiveNativeZeroWitness T A B H η f g k) (j : Fin 4) :
    a03NativeGCDCoordinateQuad p.w p.X j∈Icc (rectangularAFESmoothScale (k j)) (2*rectangularAFESmoothScale (k j)) := by
  have hs := p.mask_support j.succ
  rw [a03NativeGCDCoordinateArguments_quad _ p.w p.integer_pos p.X j] at hs
  have hj : a03ZeroModeQuadScales (phaseActualScales A B H k) j=rectangularAFESmoothScale (k j) := by
    fin_cases j <;> rfl
  rw [hj] at hs
  exact ⟨by simpa only [one_mul] using (le_div_iff₀ (boundaryActual_scale_pos _)).mp hs.1,
    (div_le_iff₀ (boundaryActual_scale_pos _)).mp hs.2⟩

theorem A03PassiveNativeZeroWitness.gap_support {T A B H η : ℝ} {f g : ℝ→ℝ} {k : Fin 4→ℕ}
    (p : A03PassiveNativeZeroWitness T A B H η f g k) (hH : 0<H) :
    a03NativeGCDCoordinateGap p.w∈Icc H (2*H) := by
  have hs := p.mask_support 0
  change a03NativeGCDCoordinateGap p.w/H∈Icc (1:ℝ) 2 at hs
  exact ⟨by simpa only [one_mul] using (le_div_iff₀ hH).mp hs.1,(div_le_iff₀ hH).mp hs.2⟩

theorem A03PassiveNativeZeroWitness.gap_ge_one {T A B H η : ℝ} {f g : ℝ→ℝ} {k : Fin 4→ℕ}
    (p : A03PassiveNativeZeroWitness T A B H η f g k) : 1≤a03NativeGCDCoordinateGap p.w := by
  have hd : 0<Nat.gcd (p.w 0*p.w 2) (p.w 1*p.w 3) :=
    Nat.gcd_pos_of_pos_left _ (Nat.mul_pos (by have := p.integer_pos 0; omega) (by have := p.integer_pos 2; omega))
  have hdn : (1:ℝ)≤Nat.gcd (p.w 0*p.w 2) (p.w 1*p.w 3) := by exact_mod_cast hd
  have hhn : (1:ℝ)≤p.w 4 := by exact_mod_cast p.integer_pos 4
  simpa only [a03NativeGCDCoordinateGap,one_mul] using mul_le_mul hdn hhn zero_le_one (by positivity)

theorem A03PassiveNativeZeroWitness.left_product_bounds {T A B H η : ℝ} {f g : ℝ→ℝ} {k : Fin 4→ℕ}
    (p : A03PassiveNativeZeroWitness T A B H η f g k) (hA : 0<A) (hB : 0<B) :
    A*(rectangularAFESmoothScale (k 0)*rectangularAFESmoothScale (k 1))≤p.X ∧
      p.X≤8*A*(rectangularAFESmoothScale (k 0)*rectangularAFESmoothScale (k 1)) := by
  have ha := (p.amplifier_support hA hB).1
  have hm := p.quad_support 0
  have hm2 := p.quad_support 1
  have hp0 : (p.w 0:ℝ)≠0 := by exact_mod_cast (show p.w 0≠0 by have := p.integer_pos 0; omega)
  have hp2 : (p.w 2:ℝ)≠0 := by exact_mod_cast (show p.w 2≠0 by have := p.integer_pos 2; omega)
  have he : (p.w 0:ℝ)*a03NativeGCDCoordinateQuad p.w p.X 0*a03NativeGCDCoordinateQuad p.w p.X 1=p.X := by
    change (p.w 0:ℝ)*(p.w 2:ℝ)*(p.X/((p.w 0:ℝ)*(p.w 2:ℝ)))=p.X
    exact mul_div_cancel₀ p.X (mul_ne_zero hp0 hp2)
  constructor
  · rw [←he]
    have hl := mul_le_mul (mul_le_mul ha.1 hm.1 (boundaryActual_scale_pos _).le (Nat.cast_nonneg (p.w 0))) hm2.1
      (boundaryActual_scale_pos _).le (mul_nonneg (by positivity) (a03NativeGCDCoordinateQuad_pos p.w p.integer_pos p.X_pos 0).le)
    convert hl using 1; ring
  · rw [←he]
    have hu := mul_le_mul (mul_le_mul ha.2 hm.2 (a03NativeGCDCoordinateQuad_pos p.w p.integer_pos p.X_pos 0).le (by positivity)) hm2.2
      (a03NativeGCDCoordinateQuad_pos p.w p.integer_pos p.X_pos 1).le (mul_nonneg (mul_nonneg (by norm_num) hA.le) (mul_nonneg (by norm_num) (boundaryActual_scale_pos (k 0)).le))
    convert hu using 1; ring

theorem A03PassiveNativeZeroWitness.right_product_bounds {T A B H η : ℝ} {f g : ℝ→ℝ} {k : Fin 4→ℕ}
    (p : A03PassiveNativeZeroWitness T A B H η f g k) (hA : 0<A) (hB : 0<B) :
    B*(rectangularAFESmoothScale (k 2)*rectangularAFESmoothScale (k 3))≤p.X ∧
      p.X≤8*B*(rectangularAFESmoothScale (k 2)*rectangularAFESmoothScale (k 3)) := by
  have hb := (p.amplifier_support hA hB).2
  have hn := p.quad_support 2
  have hn2 := p.quad_support 3
  have hp1 : (p.w 1:ℝ)≠0 := by exact_mod_cast (show p.w 1≠0 by have := p.integer_pos 1; omega)
  have hp3 : (p.w 3:ℝ)≠0 := by exact_mod_cast (show p.w 3≠0 by have := p.integer_pos 3; omega)
  have he : (p.w 1:ℝ)*a03NativeGCDCoordinateQuad p.w p.X 2*a03NativeGCDCoordinateQuad p.w p.X 3=p.X := by
    change (p.w 1:ℝ)*(p.w 3:ℝ)*(p.X/((p.w 1:ℝ)*(p.w 3:ℝ)))=p.X
    exact mul_div_cancel₀ p.X (mul_ne_zero hp1 hp3)
  constructor
  · rw [←he]
    have hl := mul_le_mul (mul_le_mul hb.1 hn.1 (boundaryActual_scale_pos _).le (Nat.cast_nonneg (p.w 1))) hn2.1
      (boundaryActual_scale_pos _).le (mul_nonneg (by positivity) (a03NativeGCDCoordinateQuad_pos p.w p.integer_pos p.X_pos 2).le)
    convert hl using 1; ring
  · rw [←he]
    have hu := mul_le_mul (mul_le_mul hb.2 hn.2 (a03NativeGCDCoordinateQuad_pos p.w p.integer_pos p.X_pos 2).le (by positivity)) hn2.2
      (a03NativeGCDCoordinateQuad_pos p.w p.integer_pos p.X_pos 3).le (mul_nonneg (mul_nonneg (by norm_num) hB.le) (mul_nonneg (by norm_num) (boundaryActual_scale_pos (k 2)).le))
    convert hu using 1; ring

theorem A03PassiveNativeZeroWitness.eta_pos {T A B H η : ℝ} {f g : ℝ→ℝ} {k : Fin 4→ℕ}
    (p : A03PassiveNativeZeroWitness T A B H η f g k) : 0<η := by
  have h := p.low_gap
  have hg := p.gap_ge_one
  nlinarith [p.X_pos]

theorem A03PassiveNativeZeroWitness.relative_gap_bound {T A B H η : ℝ} {f g : ℝ→ℝ} {k : Fin 4→ℕ}
    (p : A03PassiveNativeZeroWitness T A B H η f g k) (hA : 0<A) (hB : 0<B) (hH : 0<H) :
    H/(B*(rectangularAFESmoothScale (k 2)*rectangularAFESmoothScale (k 3)))≤8*η := by
  have hHlow := (p.gap_support hH).1.trans p.low_gap
  have hX := (p.right_product_bounds hA hB).2
  apply (div_le_iff₀ (mul_pos hB (mul_pos (boundaryActual_scale_pos _) (boundaryActual_scale_pos _)))).mpr
  calc
    _≤η*p.X := hHlow
    _≤η*(8*B*(rectangularAFESmoothScale (k 2)*rectangularAFESmoothScale (k 3))) := mul_le_mul_of_nonneg_left hX p.eta_pos.le
    _=_ := by ring

end
end Sechstmoment
