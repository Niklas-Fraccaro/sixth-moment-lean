import Sechstmoment.Numerator.U.Sources.PassiveInactiveLinearSourceJoin
import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.ActiveMaskedReindex
import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.MaskedHighFrequency
import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.MaskedPhysicalLinearity
import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.PassivePhysicalMasked

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03NativeGCDActiveSelector (T s : ℝ) (f g : ℝ→ℝ)
    (i : (Fin 3→ℕ)×(Fin 4→ℕ)) : Prop :=
  phaseActualActiveNearBlock T (rectangularAFESmoothScale (i.1 0))
    (rectangularAFESmoothScale (i.1 1)) (rectangularAFESmoothScale (i.1 2)) (T^(s-1)) f g i.2

def a03NativeGCDActiveDyadicMask (T a b s u ε : ℝ) (f g : ℝ→ℝ) (w : Fin 5→ℕ) (X : ℝ) : ℝ :=
  a03NativeGCDSelectedGridMask
    (a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u)))
    (a03ActualRatioSourceGoodBlock T s ε f g) w X

def a03NativeGCDSourceComparisonMask (T a b s u ε : ℝ) (f g : ℝ→ℝ) (w : Fin 5→ℕ) (X : ℝ) : ℝ :=
  a03NativeGCDActiveDyadicMask T a b s u ε f g w X-
    a03NativeGCDSelectedDyadicMask (a03NativeGCDActiveSelector T s f g) T a b s u ε f g w X

theorem a03NativeGCDSourceComparisonMask_abs_le_one
    (T a b s u ε : ℝ) (f g : ℝ→ℝ) (w : Fin 5→ℕ) (hw : ∀j,1≤w j) (X : ℝ) :
    |a03NativeGCDSourceComparisonMask T a b s u ε f g w X|≤1 := by
  have h₁ := a03NativeGCDSelectedGridMask_bounds
    (a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u)))
    (a03ActualRatioSourceGoodBlock T s ε f g) w hw X
  have h₂ := a03NativeGCDSelectedDyadicMask_bounds (a03NativeGCDActiveSelector T s f g)
    T a b s u ε f g w hw X
  unfold a03NativeGCDSourceComparisonMask a03NativeGCDActiveDyadicMask
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem a03NativeGCDSourceComparisonMask_continuous
    (T a b s u ε : ℝ) (f g : ℝ→ℝ) (w : Fin 5→ℕ) (hw : ∀j,1≤w j) :
    Continuous (a03NativeGCDSourceComparisonMask T a b s u ε f g w) := by
  exact (a03NativeGCDSelectedGridMask_continuous
    (a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u)))
    (a03ActualRatioSourceGoodBlock T s ε f g) w hw).sub
      (a03NativeGCDSelectedDyadicMask_continuous (a03NativeGCDActiveSelector T s f g)
        T a b s u ε f g w hw)

theorem a03_native_GCD_active_passive_mask_low_gap_eq
    (T a b s u ε : ℝ) (f g : ℝ→ℝ) (w : Fin 5→ℕ) (X : ℝ) (hX : 0<X)
    (hf : f (Real.log (w 0:ℝ)/Real.log T)≠0) (hg : g (Real.log (w 1:ℝ)/Real.log T)≠0)
    (hlow : a03NativeGCDCoordinateGap w≤T^(s-1)*X) :
    a03NativeGCDSourceComparisonMask T a b s u ε f g w X=0 := by
  have he : a03NativeGCDActiveDyadicMask T a b s u ε f g w X=
      a03NativeGCDSelectedDyadicMask (a03NativeGCDActiveSelector T s f g) T a b s u ε f g w X := by
    unfold a03NativeGCDActiveDyadicMask a03NativeGCDSelectedGridMask a03NativeGCDSelectedDyadicMask
    apply Finset.sum_congr rfl
    intro i _
    change (if a03ActualRatioSourceGoodBlock T s ε f g i then
      a03NativeGCDAllDyadicWeight (a03NativeGCDActualScales i) w X else 0)=
      (if a03NativeGCDActiveSelector T s f g i ∧ a03ActualPassiveRatioSourceGoodBlock T s ε f g i then
        a03NativeGCDAllDyadicWeight (a03NativeGCDActualScales i) w X else 0)
    by_cases hw0 : a03NativeGCDAllDyadicWeight (a03NativeGCDActualScales i) w X=0
    · simp only [hw0,ite_self]
    have hp := a03_native_GCD_low_gap_nonzero_weight_passive T _ _ _ (T^(s-1)) f g i.2
      (boundaryActual_scale_pos (i.1 0)) (boundaryActual_scale_pos (i.1 1))
      (boundaryActual_scale_pos (i.1 2)) w X hX hw0 hf hg hlow
    have hiff : a03ActualRatioSourceGoodBlock T s ε f g i ↔
        a03NativeGCDActiveSelector T s f g i ∧ a03ActualPassiveRatioSourceGoodBlock T s ε f g i := by
      constructor
      · intro h
        exact ⟨h.1,hp,h.2⟩
      · intro h
        exact ⟨h.1,h.2.2⟩
    by_cases hs : a03ActualRatioSourceGoodBlock T s ε f g i
    · have hh := hiff.mp hs
      simp [hs,hh]
    · have hh : ¬(a03NativeGCDActiveSelector T s f g i ∧ a03ActualPassiveRatioSourceGoodBlock T s ε f g i) :=
        fun h => hs (hiff.mpr h)
      simp only [hs,hh,ite_false]
  exact sub_eq_zero.mpr he

theorem a03_native_GCD_active_passive_mask_supported_high_gap
    (T a b s u ε : ℝ) (f g : ℝ→ℝ) (w : Fin 5→ℕ) (X : ℝ) (hX : 0<X)
    (hf : f (Real.log (w 0:ℝ)/Real.log T)≠0) (hg : g (Real.log (w 1:ℝ)/Real.log T)≠0)
    (hm : a03NativeGCDSourceComparisonMask T a b s u ε f g w X≠0) :
    T^(s-1)*X<a03NativeGCDCoordinateGap w := by
  apply lt_of_not_ge
  intro hlow
  exact hm (a03_native_GCD_active_passive_mask_low_gap_eq T a b s u ε f g w X hX hf hg hlow)

theorem a03_native_GCD_active_passive_mask_physical_uniform_rapid
    {a b s κ : ℝ} (hs : 0<s) (hκ : 0<κ)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (K : Set MomentShifts) (hK : IsCompact K) (u ε M : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀σ∈K,
      (∀k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀α : MomentShifts,(∀j : Fin 4,‖α j‖≤1/4) →∀dual : Bool,
      ‖a03NativeGCDMaskedPhysicalSum (fun _positive z v p X =>
        a03NativeGCDSourceComparisonMask T a b s u ε f g (a03NativeGCDNatTuple z v p.1.1 p.1.2 p.2) X)
          dual Φ T a b σ α f g‖≤C*T^(-M) := by
  obtain ⟨C,hC,hrapid⟩ := a03NativeGCD_bounded_high_frequency_mask_uniform_rapid
    hs hκ f g hf hg hΦ hSupp K hK M
  refine ⟨C,hC,?_⟩
  filter_upwards [hrapid] with T hrapid
  intro σ hσ hroot α hα dual
  apply hrapid σ hσ hroot α hα dual
  · intro positive z v p X _hX
    exact a03NativeGCDSourceComparisonMask_abs_le_one T a b s u ε f g _
      (a03NativeGCDNatTuple_positive _ _ _ _ _) X
  · intro positive z v p X hX hm hf0 hg0
    have hh := a03_native_GCD_active_passive_mask_supported_high_gap T a b s u ε f g
      (a03NativeGCDNatTuple z v p.1.1 p.1.2 p.2) X hX
      (by simpa [a03NativeGCDNatTuple] using hf0) (by simpa [a03NativeGCDNatTuple] using hg0) hm
    have hc : T^(s-1)*X<(Nat.gcd ((z+1)*(p.1.1+1)) ((v+1)*(p.1.2+1)):ℝ)*(p.2+1) := by
      simpa [a03NativeGCDCoordinateGap,a03NativeGCDNatTuple] using hh
    exact hc.le

theorem a03_actual_passive_retained_GCD_active_inactive_partition
    (dual : Bool) (Φ : ℝ→ℂ) (T a b s u ε : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ) :
    a03ActualPassiveRetainedRatioGCDVStarFinite (fun _ => True) dual Φ T a b s u ε σ α f g=
      a03ActualPassiveRetainedRatioGCDVStarFinite (a03NativeGCDActiveSelector T s f g) dual Φ T a b s u ε σ α f g+
      a03ActualPassiveRetainedRatioGCDVStarFinite (fun i => ¬a03NativeGCDActiveSelector T s f g i) dual Φ T a b s u ε σ α f g := by
  unfold a03ActualPassiveRetainedRatioGCDVStarFinite
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro positive _
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold a03ActualPassiveRetainedRatioGCDVStarBlock
  dsimp only
  by_cases ha : a03NativeGCDActiveSelector T s f g i <;>
    by_cases hg : a03ActualPassiveRatioSourceGoodBlock T s ε f g i <;> simp [ha,hg]

theorem a03_actual_active_retained_sub_active_passive_retained_uniform_rapid
    {a b s κ : ℝ} (hs : 0<s) (hκ : 0<κ)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (K : Set MomentShifts) (hK : IsCompact K) (u ε M : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀σ∈K,
      (∀k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀α : MomentShifts,(∀j : Fin 4,‖α j‖≤1/4) →∀dual : Bool,
      ‖a03ActualRetainedRatioGCDVStarFinite dual Φ T a b s u ε σ α f g-
        a03ActualPassiveRetainedRatioGCDVStarFinite (a03NativeGCDActiveSelector T s f g)
          dual Φ T a b s u ε σ α f g‖≤C*T^(-M) := by
  obtain ⟨C,hC,hrapid⟩ := a03_native_GCD_active_passive_mask_physical_uniform_rapid
    hs hκ f g hf hg hΦ hSupp K hK u ε M
  refine ⟨C,hC,?_⟩
  filter_upwards [hrapid,
    a03_actual_active_retained_GCD_eq_physical_masked hΦ hSupp K hK hκ a b s u ε f g hf hg,
    a03_actual_passive_retained_GCD_eq_physical_masked hΦ hSupp K hK hκ a b s u ε f g hf hg,
    a03NativeGCDMaskedPhysicalSum_sub hΦ hSupp K hK hκ a b f g] with T hrapid heA heP hsub
  intro σ hσ hroot α hα dual
  let mask₁ : Bool→ℕ→ℕ→((ℕ×ℕ)×ℕ)→ℝ→ℝ := fun _positive z v p X =>
    a03NativeGCDActiveDyadicMask T a b s u ε f g (a03NativeGCDNatTuple z v p.1.1 p.1.2 p.2) X
  let mask₂ := a03NativeGCDPassivePhysicalMask (a03NativeGCDActiveSelector T s f g) T a b s u ε f g
  have h₁ : a03ActualRetainedRatioGCDVStarFinite dual Φ T a b s u ε σ α f g=
      a03NativeGCDMaskedPhysicalSum mask₁ dual Φ T a b σ α f g := heA σ hσ hroot α hα dual
  have h₂ : a03ActualPassiveRetainedRatioGCDVStarFinite (a03NativeGCDActiveSelector T s f g)
      dual Φ T a b s u ε σ α f g=a03NativeGCDMaskedPhysicalSum mask₂ dual Φ T a b σ α f g :=
    heP σ hσ hroot α hα dual _
  have hd := hsub σ hσ hroot α hα dual mask₁ mask₂ (by
    intro positive z v p
    exact a03NativeGCDSelectedGridMask_continuous
      (a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u)))
      (a03ActualRatioSourceGoodBlock T s ε f g) _ (a03NativeGCDNatTuple_positive _ _ _ _ _)) (by
    intro positive z v p
    exact a03NativeGCDSelectedDyadicMask_continuous (a03NativeGCDActiveSelector T s f g)
      T a b s u ε f g _ (a03NativeGCDNatTuple_positive _ _ _ _ _)) (by
    intro positive z v p X _hX
    exact a03NativeGCDSelectedGridMask_bounds
      (a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u)))
      (a03ActualRatioSourceGoodBlock T s ε f g) _ (a03NativeGCDNatTuple_positive _ _ _ _ _) X) (by
    intro positive z v p X _hX
    exact a03NativeGCDSelectedDyadicMask_bounds (a03NativeGCDActiveSelector T s f g)
      T a b s u ε f g _ (a03NativeGCDNatTuple_positive _ _ _ _ _) X)
  rw [h₁,h₂,hd]
  exact hrapid σ hσ hroot α hα dual

theorem a03_actual_active_retained_sub_passive_retained_uniform_slack_smaller
    (hinput : SeparatedQuadraticInput) {a b κ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hκ : 0<κ) (hR : 0≤R) :
    ∃ S U : ℝ,0<S ∧ S<1/2 ∧ S≤1/8 ∧ 0<U ∧ U≤1/8 ∧
      ∀s u : ℝ,0<s →s≤S →0<u →u≤U →
      ∀δ : ℝ,0<δ →∀ᶠT : ℝ in atTop,∀σ α : MomentShifts,(∀j,‖σ j‖≤R) →
        (∀j,‖α j‖≤R/Real.log T) →(∀j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
        ∀dual : Bool,
        ‖a03ActualRetainedRatioGCDVStarFinite dual (fun x => (Φ x:ℂ)) T a b s u
            (rectangularSlack a b/128) σ α f g-
          a03ActualPassiveRetainedRatioGCDVStarFinite (fun _ => True) dual (fun x => (Φ x:ℂ))
            T a b s u (rectangularSlack a b/128) σ α f g‖≤δ*T := by
  obtain ⟨S,U,hS,hS2,hScap,hU,hUcap,hsmall⟩ :=
    a03_actual_passive_ratio_inactive_retained_GCD_uniform_slack_smaller hinput ha hab hlen
      f g Φ hf hg hΦ hκ (by norm_num : (0:ℝ)<1) hR
  refine ⟨S,U,hS,hS2,hScap,hU,hUcap,?_⟩
  intro s u hs hss hu huu
  have hΦc : ContDiff ℝ ∞ (fun x => (Φ x:ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ.1
  have hΦs : tsupport (fun x => (Φ x:ℂ))⊆Icc 1 2 := (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦ.2
  let K : Set MomentShifts := Metric.closedBall 0 R
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨C,hC,hrapid⟩ := a03_actual_active_retained_sub_active_passive_retained_uniform_rapid
    hs hκ f g hf hg hΦc hΦs K hK u (rectangularSlack a b/128) 0
  intro δ hδ
  filter_upwards [hsmall s u hs hss hu huu (δ/2) (by positivity),hrapid,
    eventually_ge_atTop (2*C/δ),eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4*R))]
    with T hsmall hrapid hthreshold hT hlog hlogR
  intro σ α hσ hα hroot dual
  have hσK : σ∈K := by
    change dist σ 0≤R
    rw [dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg hR).mpr hσ
  have hαquarter : ∀j,‖α j‖≤1/4 := fun j =>
    (hα j).trans ((div_le_iff₀ (zero_lt_one.trans_le hlog)).mpr (by linarith))
  have hfarr := hrapid σ hσK hroot α hαquarter dual
  simp only [neg_zero,Real.rpow_zero,mul_one] at hfarr
  have hCδ : C≤(δ/2)*T := by
    have hh := (div_le_iff₀ hδ).mp hthreshold
    nlinarith
  have hinactive := hsmall σ α hσ hα hroot
    (fun i => ¬a03NativeGCDActiveSelector T s f g i) (fun _ hi => hi) dual
  calc
    _=‖(a03ActualRetainedRatioGCDVStarFinite dual (fun x => (Φ x:ℂ)) T a b s u
        (rectangularSlack a b/128) σ α f g-
      a03ActualPassiveRetainedRatioGCDVStarFinite (a03NativeGCDActiveSelector T s f g) dual
        (fun x => (Φ x:ℂ)) T a b s u (rectangularSlack a b/128) σ α f g)-
      a03ActualPassiveRetainedRatioGCDVStarFinite (fun i => ¬a03NativeGCDActiveSelector T s f g i) dual
        (fun x => (Φ x:ℂ)) T a b s u (rectangularSlack a b/128) σ α f g‖ := by
      rw [a03_actual_passive_retained_GCD_active_inactive_partition]
      congr 1
      ring
    _≤_ := norm_sub_le _ _
    _≤δ*T := by linarith [hfarr.trans hCδ,hinactive]

end
end Sechstmoment
