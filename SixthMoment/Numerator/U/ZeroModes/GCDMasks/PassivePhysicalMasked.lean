import SixthMoment.Numerator.U.ZeroModes.GCDMasks.HighFrequencyAggregate
import SixthMoment.Numerator.U.ZeroModes.GCDMasks.MaskedReindex

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

def a03NativeGCDPassivePhysicalMask
    (select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop) (T a b s u ε : ℝ) (f g : ℝ→ℝ) :
    Bool→ℕ→ℕ→((ℕ×ℕ)×ℕ)→ℝ→ℝ :=
  fun _positive z v p X => a03NativeGCDSelectedDyadicMask select T a b s u ε f g
    (a03NativeGCDNatTuple z v p.1.1 p.1.2 p.2) X

theorem a03_actual_passive_retained_GCD_eq_physical_masked {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (a b s u ε : ℝ) (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∀ᶠ T : ℝ in atTop,∀ σ∈K,(∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ α : MomentShifts,(∀ j : Fin 4,‖α j‖≤1/4) →∀ dual : Bool,
      ∀ select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop,
      a03ActualPassiveRetainedRatioGCDVStarFinite select dual Φ T a b s u ε σ α f g=
        a03NativeGCDMaskedPhysicalSum
          (a03NativeGCDPassivePhysicalMask select T a b s u ε f g) dual Φ T a b σ α f g := by
  filter_upwards [a03_actual_passive_retained_GCD_eq_integrated_masked hΦ hSupp K hK hκ a b s u ε f g hf hg,
    a03UnrestrictedRatioGCDVStar_absolute_convergence hΦ hSupp K hK hκ f g] with T he hc
  intro σ hσ hroot α hα dual select
  rw [he σ hσ hroot α hα dual select]
  unfold a03ActualMaskedIntegratedRatioGCDVStar a03NativeGCDMaskedPhysicalSum
  congr 1
  apply Finset.sum_congr rfl
  intro positive _hp
  apply Finset.sum_congr rfl
  intro z _hz
  apply Finset.sum_congr rfl
  intro v _hv
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
  have hNorm := (hc σ hσ hroot α hα dual positive z v).2.2.2.1 X hX
  have hMasked : Summable (fun p : (ℕ×ℕ)×ℕ =>
      (a03NativeGCDSelectedDyadicMask select T a b s u ε f g
        (a03NativeGCDNatTuple z v p.1.1 p.1.2 p.2) X:ℂ)*
          a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v p.1.1 p.1.2 p.2 X) := by
    apply summable_norm_iff.mp
    apply hNorm.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro p
    have hb := a03NativeGCDSelectedDyadicMask_bounds select T a b s u ε f g
      (a03NativeGCDNatTuple z v p.1.1 p.1.2 p.2)
        (a03NativeGCDNatTuple_positive z v p.1.1 p.1.2 p.2) X
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hb.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hb.2
  exact (a03NativeGCD_triple_tsum hMasked).symm

end
end SixthMoment
