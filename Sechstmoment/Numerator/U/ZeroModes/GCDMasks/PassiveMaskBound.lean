import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.FullAbsoluteBudget
import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.MaskComplementBudget
import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.MaskComplementGeometry
import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.MaskedReindex

/-! Removal of the literal passive seven-variable continuous mask.
All actual countable indices, amplifier ranges, gap signs and spatial
integration remain in the norm bound. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 3000000

def a03ActualNativeMaskComplement (dual : Bool) (Φ : ℝ→ℂ)
    (T a b s u ε : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  (T:ℂ)*∑positive : Bool,∑z∈Finset.range ⌊T^a⌋₊,∑v∈Finset.range ⌊T^b⌋₊,
    ∑'p : (ℕ×ℕ)×ℕ,∫X : ℝ in Ioi 0,
      ((1-a03NativeGCDSelectedDyadicMask (fun _ => True) T a b s u ε f g
        (a03NativeGCDNatTuple z v p.1.1 p.1.2 p.2) X:ℝ):ℂ)*
          a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v p.1.1 p.1.2 p.2 X

theorem a03_actual_unrestricted_sub_masked_eq_complement {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (a b s u ε : ℝ) (f g : ℝ→ℝ) :
    ∀ᶠ T : ℝ in atTop,∀ σ∈K,(∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ α : MomentShifts,(∀ j : Fin 4,‖α j‖≤1/4) →∀ dual : Bool,
      a03ActualUnrestrictedRatioGCDVStar dual Φ T a b σ α f g-
        a03ActualMaskedRatioGCDVStar (fun _ => True) dual Φ T a b s u ε σ α f g=
          a03ActualNativeMaskComplement dual Φ T a b s u ε σ α f g := by
  filter_upwards [a03UnrestrictedRatioGCDVStar_absolute_convergence hΦ hSupp K hK hκ f g]
    with T hCT
  intro σ hσ hroot α hα dual
  unfold a03ActualUnrestrictedRatioGCDVStar a03ActualMaskedRatioGCDVStar a03ActualNativeMaskComplement
    a03UnrestrictedRatioGCDVStarTerm
  rw [←mul_sub,←Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro positive _
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z _
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  have hC := hCT σ hσ hroot α hα dual positive z v
  let F := fun p : (ℕ×ℕ)×ℕ =>
    a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v p.1.1 p.1.2 p.2
  let mask := fun (p : (ℕ×ℕ)×ℕ) (X : ℝ) =>
    a03NativeGCDSelectedDyadicMask (fun _ => True) T a b s u ε f g
      (a03NativeGCDNatTuple z v p.1.1 p.1.2 p.2) X
  have hw (p : (ℕ×ℕ)×ℕ) : ∀j : Fin 5,1≤a03NativeGCDNatTuple z v p.1.1 p.1.2 p.2 j := by
    intro j
    fin_cases j <;> simp [a03NativeGCDNatTuple]
  have hM := a03NativeGCD_bounded_mask_absolute_convergence hC.1 hC.2.1 mask
    (fun p => (a03NativeGCDSelectedDyadicMask_continuous (fun _ => True) T a b s u ε f g _ (hw p)).aestronglyMeasurable)
    (fun p X _ => by
      have hb := a03NativeGCDSelectedDyadicMask_bounds (fun _ => True) T a b s u ε f g _ (hw p) X
      rw [abs_of_nonneg hb.1]
      exact hb.2)
  rw [←a03NativeGCD_triple_tsum hC.2.2.1,←a03NativeGCD_triple_tsum hM.2.2.1,
    ←hC.2.2.1.tsum_sub hM.2.2.1]
  apply tsum_congr
  intro p
  rw [←integral_sub (hC.1 p) (hM.1 p)]
  apply integral_congr_ae
  exact ae_of_all _ fun X => by
    dsimp [F,mask]
    push_cast
    ring

theorem a03_actual_native_mask_complement_uniform_rapid {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ a b s u ε : ℝ}
    (hκ : 0<κ) (ha : 0≤a) (hb : 0≤b) (hs : 0<s) (hs1 : s≤1/2)
    (hu : 0<u) (hε : 0<ε) (hma : s+a<1) (hmb : s+b<1)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) (N : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ α : MomentShifts,(∀ j : Fin 4,‖α j‖≤1/4) →∀ dual : Bool,
      ‖a03ActualNativeMaskComplement dual Φ T a b s u ε σ α f g‖≤C*T^(-N) := by
  let χ := a03NativeGCDMaskTailExponent a b s ε
  let c := a03NativeGCDMaskTailConstant ε
  have hχ : 0<χ := a03NativeGCDMaskTailExponent_pos hε hma hmb
  have hc : 0<c := a03NativeGCDMaskTailConstant_pos ε
  obtain ⟨M,hM⟩ := exists_nat_gt (N+a03NativeGCDFullBudgetPower a b)
  obtain ⟨C,hC,hBudget⟩ := a03NativeGCD_mask_complement_absolute_budget
    hΦ hSupp K hK hκ hs (by linarith : 0<u/2) hχ hc M f g
  obtain ⟨D,hD,hFull⟩ := a03NativeGCDFullBudget_smooth_uniform_power ha hb 56 f g hf hg
  refine ⟨D*C,by positivity,?_⟩
  filter_upwards [hBudget,eventually_gt_atTop (1:ℝ)] with T hBT hT
  intro σ hσ hroot α hα dual
  have hTp : 0<T := zero_lt_one.trans hT
  let row := fun (positive : Bool) (z v : ℕ) => ∑'p : (ℕ×ℕ)×ℕ,∫X : ℝ in Ioi 0,
    ((1-a03NativeGCDSelectedDyadicMask (fun _ => True) T a b s u ε f g
      (a03NativeGCDNatTuple z v p.1.1 p.1.2 p.2) X:ℝ):ℂ)*
        a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v p.1.1 p.1.2 p.2 X
  have hrow (positive : Bool) (z : ℕ) (hz : z∈Finset.range ⌊T^a⌋₊)
      (v : ℕ) (hv : v∈Finset.range ⌊T^b⌋₊) :
      ‖row positive z v‖≤a03NativeGCDFullBudgetRow T (-(M:ℝ)) 56 C f g z v := by
    by_cases hz0 : f (Real.log (z+1:ℝ)/Real.log T)=0
    · simp [row,a03UnrestrictedRatioGCDVStarIntegrand,hz0,a03NativeGCDFullBudgetRow]
    by_cases hv0 : g (Real.log (v+1:ℝ)/Real.log T)=0
    · simp [row,a03UnrestrictedRatioGCDVStarIntegrand,hv0,a03NativeGCDFullBudgetRow]
    let mask := fun (p : (ℕ×ℕ)×ℕ) (X : ℝ) =>
      a03NativeGCDSelectedDyadicMask (fun _ => True) T a b s u ε f g
        (a03NativeGCDNatTuple z v p.1.1 p.1.2 p.2) X
    have hw (p : (ℕ×ℕ)×ℕ) : ∀j : Fin 5,1≤a03NativeGCDNatTuple z v p.1.1 p.1.2 p.2 j := by
      intro j
      fin_cases j <;> simp [a03NativeGCDNatTuple]
    have hzc : (z+1:ℝ)≤T^a :=
      (by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hz) : (z+1:ℝ)≤⌊T^a⌋₊).trans
        (Nat.floor_le (Real.rpow_nonneg hTp.le a))
    have hvc : (v+1:ℝ)≤T^b :=
      (by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hv) : (v+1:ℝ)≤⌊T^b⌋₊).trans
        (Nat.floor_le (Real.rpow_nonneg hTp.le b))
    have hm := hBT σ hσ hroot α hα dual positive z v mask
      (fun p => (a03NativeGCDSelectedDyadicMask_continuous (fun _ => True) T a b s u ε f g _ (hw p)).aestronglyMeasurable)
      (fun p X _ => a03NativeGCDSelectedDyadicMask_bounds (fun _ => True) T a b s u ε f g _ (hw p) X)
      (by
        intro p X hX hmask
        have hclass := a03_native_GCD_passive_mask_complement_classified hT.le a b s u ε hs1 hε.le f g
          (a03NativeGCDNatTuple z v p.1.1 p.1.2 p.2) (hw p) X hX
          (by simpa only [a03NativeGCDNatTuple,Matrix.cons_val_zero,Nat.cast_add,Nat.cast_one] using hz0)
          (by simpa [a03NativeGCDNatTuple] using hv0)
          (by simpa [a03NativeGCDNatTuple] using hzc)
          (by simpa [a03NativeGCDNatTuple] using hvc) hmask
        rcases hclass with hprod|hfreq|hrM|hrN
        · exact Or.inl (a03CommonX_product_boundary_spatial hTp (by positivity) (by positivity) hX
            (by simpa [a03NativeGCDNatTuple] using hprod.le))
        · apply Or.inr (Or.inl _)
          have hfr : T^s≤T*(Nat.gcd ((z+1)*(p.1.1+1)) ((v+1)*(p.1.2+1)):ℝ)*(p.2+1)/X := by
            simpa [a03NativeGCDNatTuple,a03NativeGCDCoordinateGap,mul_assoc] using hfreq
          rw [abs_neg,abs_div,abs_mul,abs_mul,abs_mul,abs_of_pos hTp,
            abs_of_nonneg (show (0:ℝ)≤Nat.gcd ((z+1)*(p.1.1+1)) ((v+1)*(p.1.2+1)) from Nat.cast_nonneg _),
            abs_of_pos (by positivity : 0<(p.2:ℝ)+1),abs_of_pos hX]
          cases positive <;> norm_num [rectangularGapSign] <;> exact hfr
        · exact Or.inr (Or.inr (Or.inl (by simpa [a03NativeGCDNatTuple,χ,c] using hrM)))
        · exact Or.inr (Or.inr (Or.inr (by simpa [a03NativeGCDNatTuple,χ,c] using hrN))))
    have hn : Summable (fun p : (ℕ×ℕ)×ℕ => ‖∫X : ℝ in Ioi 0,
        ((1-mask p X:ℝ):ℂ)*a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v p.1.1 p.1.2 p.2 X‖) :=
      hm.1.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_integral_le_integral_norm _)
    calc
      _≤∑'p : (ℕ×ℕ)×ℕ,‖∫X : ℝ in Ioi 0,
          ((1-mask p X:ℝ):ℂ)*a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v p.1.1 p.1.2 p.2 X‖ :=
        norm_tsum_le_tsum_norm hn
      _≤∑'p : (ℕ×ℕ)×ℕ,∫X : ℝ in Ioi 0,
          ‖((1-mask p X:ℝ):ℂ)*a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v p.1.1 p.1.2 p.2 X‖ :=
        hn.tsum_le_tsum (fun _ => norm_integral_le_integral_norm _) hm.1
      _≤_ := hm.2
  have hAll := a03NativeGCDFullBudget_complex_norm_le hT.le row hrow
  calc
    _≤a03NativeGCDFullBudget T a b (-(M:ℝ)) 56 C f g := hAll
    _≤D*C*T^(-(M:ℝ)+a03NativeGCDFullBudgetPower a b) := hFull T hT.le C hC (-(M:ℝ))
    _≤D*C*T^(-N) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT.le (by linarith only [hM])) (by positivity)

theorem a03_actual_passive_retained_GCD_sub_unrestricted_uniform_rapid {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ a b s u ε : ℝ}
    (hκ : 0<κ) (ha : 0≤a) (hb : 0≤b) (hs : 0<s) (hs1 : s≤1/2)
    (hu : 0<u) (hε : 0<ε) (hma : s+a<1) (hmb : s+b<1)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) (N : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ α : MomentShifts,(∀ j : Fin 4,‖α j‖≤1/4) →∀ dual : Bool,
      ‖a03ActualPassiveRetainedRatioGCDVStarFinite (fun _ => True) dual Φ T a b s u ε σ α f g-
        a03ActualUnrestrictedRatioGCDVStar dual Φ T a b σ α f g‖≤C*T^(-N) := by
  obtain ⟨C,hC,hbound⟩ := a03_actual_native_mask_complement_uniform_rapid hΦ hSupp K hK hκ
    ha hb hs hs1 hu hε hma hmb f g hf hg N
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,
    a03_actual_passive_retained_GCD_eq_masked hΦ hSupp K hK hκ a b s u ε f g hf hg,
    a03_actual_unrestricted_sub_masked_eq_complement hΦ hSupp K hK hκ a b s u ε f g] with T hb he hc
  intro σ hσ hroot α hα dual
  rw [he σ hσ hroot α hα dual (fun _ => True),norm_sub_rev,hc σ hσ hroot α hα dual]
  exact hb σ hσ hroot α hα dual

end
end Sechstmoment
