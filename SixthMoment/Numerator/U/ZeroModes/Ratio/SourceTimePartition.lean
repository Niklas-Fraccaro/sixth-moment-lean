import SixthMoment.Numerator.U.ZeroModes.Ratio.BadSourceFiniteBudget

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem a03ActualRatioTimeFinite_eq_source_add_bad {a b T : ℝ} (hT : 1<T)
    (dual : Bool) (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (σ α : MomentShifts) (c s u εsource v : ℝ) :
    a03ActualRatioTimeFinite false false dual (a03ZeroModeRatioWeight (rawMomentShifts T σ))
      c T a b s u v σ α f g Φ=
      a03ActualRatioSourceFiniteValue false dual (fun x => (Φ x:ℂ)) c T a b s u εsource v σ α f g+
        a03ActualRatioBadSourceTimeFinite dual c T a b s u εsource v σ α f g Φ := by
  unfold a03ActualRatioTimeFinite a03ActualRatioSourceFiniteValue a03ActualRatioBadSourceTimeFinite
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro positive _
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases i with ⟨j,k⟩
  rw [a03ActualRatioSourceBlockValue_eq_time_block hT dual positive f g Φ hf hg σ α c s εsource v j k]
  unfold a03ActualRatioBadSourceTimeBlock
  split_ifs <;> simp only [add_zero,zero_add]

theorem a03ActualRatioGoodSourceFinite_Mellin_continuous {a b c T : ℝ}
    (hc : 0<c) (hT : 1<T) (dual : Bool) (f g Φ : ℝ→ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ)
    (σ α : MomentShifts) (hα : ∀ j,‖α j‖≤1/4) (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4)
    (s u εsource : ℝ) :
    Continuous (fun v => a03ActualRatioSourceFiniteValue false dual (fun x => (Φ x:ℂ))
      c T a b s u εsource v σ α f g) := by
  unfold a03ActualRatioSourceFiniteValue
  apply continuous_finsetSum
  intro positive _
  apply continuous_finsetSum
  intro i _
  rcases i with ⟨j,k⟩
  simp_rw [a03ActualRatioSourceBlockValue_eq_time_block hT dual positive f g Φ hf hg σ α c s εsource _ j k]
  by_cases hgood : a03ActualRatioSourceGoodBlock T s εsource f g (j,k)
  · simp only [hgood,ite_true]
    exact a03ActualRatioTimeBlock_Mellin_continuous hc (zero_lt_one.trans hT).ne' false false dual positive
      _ a b s σ α f g Φ hΦ hα hσ j k
  · simp only [hgood,ite_false]
    exact continuous_const

theorem a03ActualRatioBadSourceFinite_Mellin_continuous {c T : ℝ}
    (hc : 0<c) (hT : T≠0) (dual : Bool) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (σ α : MomentShifts) (hα : ∀ j,‖α j‖≤1/4) (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4)
    (a b s u εsource : ℝ) :
    Continuous (fun v => a03ActualRatioBadSourceTimeFinite dual c T a b s u εsource v σ α f g Φ) := by
  unfold a03ActualRatioBadSourceTimeFinite
  apply continuous_finsetSum
  intro positive _
  apply continuous_finsetSum
  intro i _
  unfold a03ActualRatioBadSourceTimeBlock
  by_cases hgood : a03ActualRatioSourceGoodBlock T s εsource f g i
  · simp only [hgood,ite_true]
    exact continuous_const
  · simp only [hgood,ite_false]
    exact a03ActualRatioTimeBlock_Mellin_continuous hc hT false false dual positive _ a b s σ α f g Φ hΦ hα hσ i.1 i.2

theorem a03ActualRatioTimeMoment_eq_source_add_bad {a b c T : ℝ}
    (hc : 0<c) (hT : 1<T) (dual : Bool) (f g Φ : ℝ→ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ)
    (σ α : MomentShifts) (hα : ∀ j,‖α j‖≤1/4) (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4)
    (s u εsource θ : ℝ) :
    IntegrableOn (fun v => a03ActualRatioSourceFiniteValue false dual (fun x => (Φ x:ℂ))
      c T a b s u εsource v σ α f g) (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
    IntegrableOn (fun v => a03ActualRatioBadSourceTimeFinite dual c T a b s u εsource v σ α f g Φ)
      (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
    a03ActualRatioTimeMoment false false dual (a03ZeroModeRatioWeight (rawMomentShifts T σ))
      c T a b s u θ σ α f g Φ=
      a03ActualRatioSourceValueMoment false dual (fun x => (Φ x:ℂ)) c T a b s u εsource θ σ α f g+
        a03ActualRatioBadSourceTimeMoment dual c T a b s u εsource θ σ α f g Φ := by
  have hi := (a03ActualRatioGoodSourceFinite_Mellin_continuous hc hT dual f g Φ hf hg hΦ σ α hα hσ s u εsource).integrableOn_Icc (a:=-θ*Real.log T) (b:=θ*Real.log T) (μ:=volume)
  have hj := (a03ActualRatioBadSourceFinite_Mellin_continuous hc (zero_lt_one.trans hT).ne' dual
    f g Φ hΦ σ α hα hσ a b s u εsource).integrableOn_Icc (a:=-θ*Real.log T) (b:=θ*Real.log T) (μ:=volume)
  refine ⟨hi,hj,?_⟩
  unfold a03ActualRatioTimeMoment a03ActualRatioSourceValueMoment a03ActualRatioBadSourceTimeMoment
  simp_rw [a03ActualRatioTimeFinite_eq_source_add_bad hT dual f g Φ hf hg σ α c s u εsource]
  exact integral_add hi hj

end
end SixthMoment
