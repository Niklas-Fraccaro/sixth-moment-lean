import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.HighFrequencyAggregate
import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.MaskedReindex
import Sechstmoment.Numerator.U.ZeroModes.Ratio.FiniteGCDVStarJoin

/-! Exact active retained seven-grid regrouping into the literal collapsed
native physical sum.  The actual discrete SourceGood mask remains intact. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03ActualActiveMaskedRatioGCDVStar (dual : Bool) (Φ : ℝ→ℂ)
    (T a b s u ε : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  (T:ℂ)*∑positive : Bool,∑z∈Finset.range ⌊T^a⌋₊,∑v∈Finset.range ⌊T^b⌋₊,
    ∑'m : ℕ,∑'n : ℕ,∑'h : ℕ,∫X : ℝ in Ioi 0,
      (a03NativeGCDSelectedGridMask
        (a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u)))
        (a03ActualRatioSourceGoodBlock T s ε f g) (a03NativeGCDNatTuple z v m n h) X:ℂ)*
          a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v m n h X

theorem a03_actual_active_retained_GCD_eq_masked_of_integrable
    (dual : Bool) (Φ : ℝ→ℂ) {T : ℝ} (hT : 1<T) (a b s u ε : ℝ)
    (σ α : MomentShifts) (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hFI : ∀positive : Bool,∀z v m n h,IntegrableOn
      (a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v m n h) (Ioi 0)) :
    a03ActualRetainedRatioGCDVStarFinite dual Φ T a b s u ε σ α f g=
      a03ActualActiveMaskedRatioGCDVStar dual Φ T a b s u ε σ α f g := by
  let S := a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u))
  let P := a03ActualRatioSourceGoodBlock T s ε f g
  let J := S.biUnion (fun i => quadraticMainIndexSet (a03NativeGCDActualScales i))
  let D := a03NativeGCDDensity dual
  have hJ (w : Fin 5→ℕ) (hw : w∈J) : ∀j,1≤w j := by
    obtain ⟨i,_,hwi⟩ := Finset.mem_biUnion.mp hw
    intro j
    exact (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hwi j)).1
  have hBlock (positive : Bool) (i : (Fin 3→ℕ)×(Fin 4→ℕ)) :
      a03ActualRetainedRatioGCDVStarBlock dual positive Φ T s ε σ α f g i=
      (T:ℂ)*(if P i then ∑w∈quadraticMainIndexSet (a03NativeGCDActualScales i),∫X : ℝ in Ioi 0,
        (a03NativeGCDAllDyadicWeight (a03NativeGCDActualScales i) w X:ℂ)*
          a03NativeGCDDensity dual positive Φ T σ α f g w X else 0) := by
    unfold a03ActualRetainedRatioGCDVStarBlock
    dsimp only []
    by_cases hP : P i
    · simp only [show a03ActualRatioSourceGoodBlock T s ε f g i from hP,ite_true,P]
      change (T:ℂ)*a03RetainedRatioGCDVStarZeroMode dual Φ T σ α (rectangularGapSign positive)
        (a03NativeGCDActualScales i)
        (phaseActualAmplifierCoefficient T f (a03NativeGCDActualScales i).A)
        (phaseActualAmplifierCoefficient T g (a03NativeGCDActualScales i).B)=_
      rw [a03_actual_retained_ratio_GCD_VStar_eq_expanded dual Φ T σ α (rectangularGapSign positive)
        (a03NativeGCDActualScales i) f g,a03_retained_ratio_GCD_expanded_eq_native]
    · have hPn : ¬a03ActualRatioSourceGoodBlock T s ε f g i := hP
      simp only [hPn,ite_false,P,mul_zero]
  calc
    _=(T:ℂ)*∑positive : Bool,∑i∈S,if P i then
        ∑w∈quadraticMainIndexSet (a03NativeGCDActualScales i),∫X : ℝ in Ioi 0,
          (a03NativeGCDAllDyadicWeight (a03NativeGCDActualScales i) w X:ℂ)*
            a03NativeGCDDensity dual positive Φ T σ α f g w X else 0 := by
      unfold a03ActualRetainedRatioGCDVStarFinite
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro positive _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => hBlock positive i)
    _=(T:ℂ)*∑positive : Bool,∑w∈J,∫X : ℝ in Ioi 0,
        (a03NativeGCDSelectedGridMask S P w X:ℂ)*a03NativeGCDDensity dual positive Φ T σ α f g w X := by
      apply congrArg (fun z : ℂ => (T:ℂ)*z)
      apply Finset.sum_congr rfl
      intro positive _
      exact a03_native_GCD_selected_grid_integral_reindex S P dual positive Φ T σ α f g (hFI positive)
    _=(T:ℂ)*∑positive : Bool,∑'z : ℕ,∑'v : ℕ,∑'m : ℕ,∑'n : ℕ,∑'h : ℕ,
        ∫X : ℝ in Ioi 0,(a03NativeGCDSelectedGridMask S P (a03NativeGCDNatTuple z v m n h) X:ℂ)*
          a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v m n h X := by
      apply congrArg (fun z : ℂ => (T:ℂ)*z)
      apply Finset.sum_congr rfl
      intro positive _
      rw [a03_native_GCD_finite_positive_sum_eq_nested_tsum J hJ]
      · rfl
      · intro w hw
        simp only [a03NativeGCDSelectedGridMask_zero_outside S P w hw,Complex.ofReal_zero,zero_mul,integral_zero]
    _=_ := by
      unfold a03ActualActiveMaskedRatioGCDVStar
      apply congrArg (fun z : ℂ => (T:ℂ)*z)
      apply Finset.sum_congr rfl
      intro positive _
      rw [tsum_eq_sum (s:=Finset.range ⌊T^a⌋₊)]
      · apply Finset.sum_congr rfl
        intro z _
        apply tsum_eq_sum
        intro v hv
        have hz := a03NativeGCD_actual_profile_zero_outside hT g hg v hv
        simp [a03UnrestrictedRatioGCDVStarIntegrand,hz]
      · intro z hz
        have he := a03NativeGCD_actual_profile_zero_outside hT f hf z hz
        simp [a03UnrestrictedRatioGCDVStarIntegrand,he]

theorem a03_actual_active_retained_GCD_eq_physical_masked
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (a b s u ε : ℝ) (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∀ᶠ T : ℝ in atTop,∀ σ∈K,(∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ α : MomentShifts,(∀ j : Fin 4,‖α j‖≤1/4) →∀ dual : Bool,
      a03ActualRetainedRatioGCDVStarFinite dual Φ T a b s u ε σ α f g=
        a03NativeGCDMaskedPhysicalSum
          (fun _positive z v p X => a03NativeGCDSelectedGridMask
            (a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u)))
            (a03ActualRatioSourceGoodBlock T s ε f g) (a03NativeGCDNatTuple z v p.1.1 p.1.2 p.2) X)
          dual Φ T a b σ α f g := by
  filter_upwards [a03UnrestrictedRatioGCDVStar_absolute_convergence hΦ hSupp K hK hκ f g,
    eventually_gt_atTop (1:ℝ)] with T hconv hT
  intro σ hσ hroot α hα dual
  let S := a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u))
  let P := a03ActualRatioSourceGoodBlock T s ε f g
  rw [a03_actual_active_retained_GCD_eq_masked_of_integrable dual Φ hT a b s u ε σ α f g hf hg
    (fun positive z v m n h => (hconv σ hσ hroot α hα dual positive z v).1 ((m,n),h))]
  unfold a03ActualActiveMaskedRatioGCDVStar a03NativeGCDMaskedPhysicalSum
  apply congrArg (fun z : ℂ => (T:ℂ)*z)
  apply Finset.sum_congr rfl
  intro positive _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro v _
  let mask : ((ℕ×ℕ)×ℕ)→ℝ→ℝ := fun p X =>
    a03NativeGCDSelectedGridMask S P (a03NativeGCDNatTuple z v p.1.1 p.1.2 p.2) X
  have hMaskMeas (p : (ℕ×ℕ)×ℕ) : AEStronglyMeasurable (mask p) (volume.restrict (Ioi 0)) :=
    (a03NativeGCDSelectedGridMask_continuous S P _ (a03NativeGCDNatTuple_positive _ _ _ _ _)).aestronglyMeasurable.restrict
  have hMaskBound (p : (ℕ×ℕ)×ℕ) (X : ℝ) (_hX : 0<X) : |mask p X|≤1 := by
    have h := a03NativeGCDSelectedGridMask_bounds S P (a03NativeGCDNatTuple z v p.1.1 p.1.2 p.2)
      (a03NativeGCDNatTuple_positive z v p.1.1 p.1.2 p.2) X
    rw [abs_of_nonneg h.1]
    exact h.2
  have hmask := a03NativeGCD_bounded_mask_absolute_convergence
    (hconv σ hσ hroot α hα dual positive z v).1
    (hconv σ hσ hroot α hα dual positive z v).2.1 mask hMaskMeas hMaskBound
  change (∑'m : ℕ,∑'n : ℕ,∑'h : ℕ,∫X : ℝ in Ioi 0,(mask ((m,n),h) X:ℂ)*
    a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v m n h X)=_
  rw [←a03NativeGCD_triple_tsum hmask.2.2.1]
  exact hmask.2.2.2

end
end Sechstmoment
