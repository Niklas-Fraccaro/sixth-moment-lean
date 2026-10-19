import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.HighFrequencyAggregate

/-! Exact difference of actual masked physical expressions. The infinite
native sums and every spatial integral are exchanged by the proved
absolute convergence, before algebraic subtraction is performed. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000

theorem a03NativeGCDMaskedPhysicalSum_sub
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (a b : ℝ) (f g : ℝ→ℝ) :
    ∀ᶠ T : ℝ in atTop,∀σ∈K,(∀k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀α : MomentShifts,(∀j : Fin 4,‖α j‖≤1/4) →∀dual : Bool,
      ∀mask₁ mask₂ : Bool→ℕ→ℕ→((ℕ×ℕ)×ℕ)→ℝ→ℝ,
      (∀positive z v p,Continuous (mask₁ positive z v p)) →
      (∀positive z v p,Continuous (mask₂ positive z v p)) →
      (∀positive z v p X,0<X →0≤mask₁ positive z v p X ∧ mask₁ positive z v p X≤1) →
      (∀positive z v p X,0<X →0≤mask₂ positive z v p X ∧ mask₂ positive z v p X≤1) →
      a03NativeGCDMaskedPhysicalSum mask₁ dual Φ T a b σ α f g-
        a03NativeGCDMaskedPhysicalSum mask₂ dual Φ T a b σ α f g=
      a03NativeGCDMaskedPhysicalSum (fun positive z v p X => mask₁ positive z v p X-mask₂ positive z v p X)
        dual Φ T a b σ α f g := by
  filter_upwards [a03UnrestrictedRatioGCDVStar_absolute_convergence hΦ hSupp K hK hκ f g]
    with T hconv
  intro σ hσ hroot α hα dual mask₁ mask₂ hm₁ hm₂ hb₁ hb₂
  have hlocal (positive : Bool) (z v : ℕ) :
      (∫X : ℝ in Ioi 0,∑'p : (ℕ×ℕ)×ℕ,(mask₁ positive z v p X:ℂ)*
        a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v p.1.1 p.1.2 p.2 X)-
      (∫X : ℝ in Ioi 0,∑'p : (ℕ×ℕ)×ℕ,(mask₂ positive z v p X:ℂ)*
        a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v p.1.1 p.1.2 p.2 X)=
      ∫X : ℝ in Ioi 0,∑'p : (ℕ×ℕ)×ℕ,((mask₁ positive z v p X-mask₂ positive z v p X):ℝ)*
        a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v p.1.1 p.1.2 p.2 X := by
    let F := fun p : (ℕ×ℕ)×ℕ => a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v p.1.1 p.1.2 p.2
    have hc := hconv σ hσ hroot α hα dual positive z v
    have h₁ := a03NativeGCD_bounded_mask_absolute_convergence hc.1 hc.2.1 (mask₁ positive z v)
      (fun p => (hm₁ positive z v p).aestronglyMeasurable) (fun p X hX => by
        rw [abs_of_nonneg (hb₁ positive z v p X hX).1]
        exact (hb₁ positive z v p X hX).2)
    have h₂ := a03NativeGCD_bounded_mask_absolute_convergence hc.1 hc.2.1 (mask₂ positive z v)
      (fun p => (hm₂ positive z v p).aestronglyMeasurable) (fun p X hX => by
        rw [abs_of_nonneg (hb₂ positive z v p X hX).1]
        exact (hb₂ positive z v p X hX).2)
    have hd := a03NativeGCD_bounded_mask_absolute_convergence hc.1 hc.2.1
      (fun p X => mask₁ positive z v p X-mask₂ positive z v p X)
      (fun p => ((hm₁ positive z v p).sub (hm₂ positive z v p)).aestronglyMeasurable) (fun p X hX => by
        have h₁ := hb₁ positive z v p X hX
        have h₂ := hb₂ positive z v p X hX
        exact abs_le.mpr ⟨by linarith,by linarith⟩)
    change (∫X : ℝ in Ioi 0,∑'p,(mask₁ positive z v p X:ℂ)*F p X)-
        (∫X : ℝ in Ioi 0,∑'p,(mask₂ positive z v p X:ℂ)*F p X)=
      ∫X : ℝ in Ioi 0,∑'p,(((mask₁ positive z v p X-mask₂ positive z v p X):ℝ):ℂ)*F p X
    rw [←h₁.2.2.2,←h₂.2.2.2,←hd.2.2.2,←h₁.2.2.1.tsum_sub h₂.2.2.1]
    apply tsum_congr
    intro p
    rw [←integral_sub (h₁.1 p) (h₂.1 p)]
    apply integral_congr_ae
    exact ae_of_all _ fun X => by push_cast; ring
  unfold a03NativeGCDMaskedPhysicalSum
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
  exact hlocal positive z v

end
end Sechstmoment
