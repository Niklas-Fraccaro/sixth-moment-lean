import Sechstmoment.Numerator.U.Replacement.ActualUnrestrictedRatioGCDVStar

namespace Sechstmoment
open Complex Real Source Set MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem a03NativeGCDCoordinateArguments_gap (q : QuadraticScales) (w : Fin 5→ℕ) (X : ℝ) :
    a03NativeGCDCoordinateArguments false false q w X 1=
      (Nat.gcd (w 0*w 2) (w 1*w 3):ℝ)*w 4/q.H := rfl

theorem a03NativeGCDCoordinateArguments_M₁ (q : QuadraticScales) (w : Fin 5→ℕ) (X : ℝ) :
    a03NativeGCDCoordinateArguments false false q w X 2=(w 2:ℝ)/q.M₁ := rfl

theorem a03NativeGCDCoordinateArguments_N₁ (q : QuadraticScales) (w : Fin 5→ℕ) (X : ℝ) :
    a03NativeGCDCoordinateArguments false false q w X 4=(w 3:ℝ)/q.N₁ := rfl

theorem a03NativeGCDAllDyadicWeight_nonzero_positive (q : QuadraticScales) (w : Fin 5→ℕ) (X : ℝ)
    (hw : a03NativeGCDAllDyadicWeight q w X≠0) : ∀ j,1≤w j := by
  intro j
  by_contra hj
  have hz : w j=0 := by omega
  have hpart := hw
  simp only [a03NativeGCDAllDyadicWeight,mul_ne_zero_iff] at hpart
  have hzW : rectangularSmoothBlockWeight 0=0 := rectangularSmoothBlockWeight_zero_le (by norm_num)
  fin_cases j
  · change w 0=0 at hz
    exact hpart.1.1 (by simp only [hz,Nat.cast_zero,zero_div,hzW])
  · change w 1=0 at hz
    exact hpart.1.2 (by simp only [hz,Nat.cast_zero,zero_div,hzW])
  · change w 2=0 at hz
    have hc := (Finset.prod_ne_zero_iff.mp hpart.2) (1:Fin 5) (Finset.mem_univ _)
    change rectangularSmoothBlockWeight (a03NativeGCDCoordinateArguments false false q w X 2)≠0 at hc
    rw [a03NativeGCDCoordinateArguments_M₁] at hc
    exact hc (by simp only [hz,Nat.cast_zero,zero_div,hzW])
  · change w 3=0 at hz
    have hc := (Finset.prod_ne_zero_iff.mp hpart.2) (3:Fin 5) (Finset.mem_univ _)
    change rectangularSmoothBlockWeight (a03NativeGCDCoordinateArguments false false q w X 4)≠0 at hc
    rw [a03NativeGCDCoordinateArguments_N₁] at hc
    exact hc (by simp only [hz,Nat.cast_zero,zero_div,hzW])
  · change w 4=0 at hz
    have hc := (Finset.prod_ne_zero_iff.mp hpart.2) (0:Fin 5) (Finset.mem_univ _)
    change rectangularSmoothBlockWeight (a03NativeGCDCoordinateArguments false false q w X 1)≠0 at hc
    rw [a03NativeGCDCoordinateArguments_gap] at hc
    exact hc (by simp only [hz,Nat.cast_zero,mul_zero,zero_div,hzW])

theorem a03NativeGCDAllDyadicWeight_nonzero_index (q : QuadraticScales)
    (hq : ∀ j,0<q.size j) (w : Fin 5→ℕ) (X : ℝ)
    (hw : a03NativeGCDAllDyadicWeight q w X≠0) : w∈quadraticMainIndexSet q := by
  have hp := a03NativeGCDAllDyadicWeight_nonzero_positive q w X hw
  have hA : 0<q.A := by simpa [QuadraticScales.size] using hq 0
  have hB : 0<q.B := by simpa [QuadraticScales.size] using hq 1
  have hM : 0<q.M₁ := by simpa [QuadraticScales.size] using hq 2
  have hN : 0<q.N₁ := by simpa [QuadraticScales.size] using hq 4
  have hH : 0<q.H := by simpa [QuadraticScales.size] using hq 6
  have hd : (1:ℝ)≤Nat.gcd (w 0*w 2) (w 1*w 3) := by
    exact_mod_cast (show 1≤Nat.gcd (w 0*w 2) (w 1*w 3) by
      have hd := Nat.gcd_pos_of_pos_left (w 1*w 3)
        (Nat.mul_pos (show 0<w 0 by have := hp 0; omega) (show 0<w 2 by have := hp 2; omega))
      omega)
  have hpart := hw
  simp only [a03NativeGCDAllDyadicWeight,mul_ne_zero_iff] at hpart
  have hs {x S : ℝ} (hS : 0<S) (hz : rectangularSmoothBlockWeight (x/S)≠0) : x≤2*S :=
    (div_le_iff₀ hS).mp (rectangularSmoothBlockWeight_tsupport (subset_tsupport _ hz)).2
  have h0 := hs hA hpart.1.1
  have h1 := hs hB hpart.1.2
  have h2 := (Finset.prod_ne_zero_iff.mp hpart.2) (1:Fin 5) (Finset.mem_univ _)
  have h3 := (Finset.prod_ne_zero_iff.mp hpart.2) (3:Fin 5) (Finset.mem_univ _)
  have h4 := (Finset.prod_ne_zero_iff.mp hpart.2) (0:Fin 5) (Finset.mem_univ _)
  change rectangularSmoothBlockWeight (a03NativeGCDCoordinateArguments false false q w X 2)≠0 at h2
  change rectangularSmoothBlockWeight (a03NativeGCDCoordinateArguments false false q w X 4)≠0 at h3
  change rectangularSmoothBlockWeight (a03NativeGCDCoordinateArguments false false q w X 1)≠0 at h4
  rw [a03NativeGCDCoordinateArguments_M₁] at h2
  rw [a03NativeGCDCoordinateArguments_N₁] at h3
  rw [a03NativeGCDCoordinateArguments_gap] at h4
  have h2 := hs hM h2
  have h3 := hs hN h3
  have h4' := hs hH h4
  have h4 : (w 4:ℝ)≤2*q.H := by
    have hh := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg (w 4))
    nlinarith
  apply Fintype.mem_piFinset.mpr
  intro j
  apply Finset.mem_Icc.mpr
  refine ⟨hp j,Nat.le_floor ?_⟩
  fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem a03NativeGCDAllDyadicWeight_zero_outside_main (q : QuadraticScales)
    (hq : ∀ j,0<q.size j) (w : Fin 5→ℕ) (hw : w∉quadraticMainIndexSet q) (X : ℝ) :
    a03NativeGCDAllDyadicWeight q w X=0 := by
  by_contra h
  exact hw (a03NativeGCDAllDyadicWeight_nonzero_index q hq w X h)

theorem a03_native_GCD_dyadic_tsum_eq_finite (q : QuadraticScales)
    (hq : ∀ j,0<q.size j) (X : ℝ) (F : (Fin 5→ℕ)→ℂ) :
    (∑' w : Fin 5→ℕ,(a03NativeGCDAllDyadicWeight q w X:ℂ)*F w)=
      ∑ w∈quadraticMainIndexSet q,(a03NativeGCDAllDyadicWeight q w X:ℂ)*F w := by
  apply tsum_eq_sum
  intro w hw
  rw [a03NativeGCDAllDyadicWeight_zero_outside_main q hq w hw X,Complex.ofReal_zero,zero_mul]

end
end Sechstmoment
