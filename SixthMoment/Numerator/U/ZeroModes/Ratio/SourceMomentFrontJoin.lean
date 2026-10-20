import SixthMoment.Numerator.U.Separation.TimeFarContourBudget
import SixthMoment.Numerator.U.ZeroModes.Ratio.DiscreteFrontJoin

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem a03_actual_time_source_Mellin_continuous
    {c T : ℝ} (hc : 0<c) (hT : T≠0) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (σ α : MomentShifts) (hα : ∀ j,‖α j‖≤1/4)
    (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4)
    (dual : Bool) (u w : ℕ) (n : Fin 4→ℕ) :
    Continuous (fun v : ℝ => ∫ t : ℝ,
      rectangularMomentPairWeight T f g Φ u w t*
        (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
          rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)) := by
  have hs : ∀ j,|(rawMomentShifts T σ j).re|<1/2 := fun j =>
    ((Complex.abs_re_le_norm _).trans (hσ j)).trans_lt (by norm_num)
  have hd : Continuous (fun p : ℝ×ℝ => if dual then bblrDualMultiplier p.2 (rawMomentShifts T σ) else 1) := by
    cases dual
    · exact continuous_const
    · exact (rectangular_dual_multiplier_continuous _ hs).comp continuous_snd
  have hm : Continuous (fun p : ℝ×ℝ => rectangularMomentPairWeight T f g Φ u w p.2) :=
    (rectangular_moment_pair_weight_continuous T f g Φ hΦ u w).comp continuous_snd
  have hk := a03_actual_small_Mellin_kernel_joint_continuous hc T σ α hα n
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support
    (rectangular_moment_pair_weight_compact hT f g Φ hΦ u w)
    ((hm.mul hd).mul hk).continuousOn
  intro v t _ ht
  have hz : rectangularMomentPairWeight T f g Φ u w t=0 :=
    image_eq_zero_of_notMem_tsupport ht
  simp only [hz,zero_mul]

theorem a03ActualRatioTimeBlock_Mellin_continuous
    {c T : ℝ} (hc : 0<c) (hT : T≠0) (m n dual positive : Bool) (G : ℂ→ℂ)
    (a b s : ℝ) (σ α : MomentShifts) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (hα : ∀ j,‖α j‖≤1/4) (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4)
    (j : Fin 3→ℕ) (k : Fin 4→ℕ) :
    Continuous (fun v : ℝ => a03ActualRatioTimeBlock m n dual positive G c T a b s v σ α f g Φ j k) := by
  unfold a03ActualRatioTimeBlock
  by_cases hactive : phaseActualActiveNearBlock T (rectangularAFESmoothScale (j 0))
    (rectangularAFESmoothScale (j 1)) (rectangularAFESmoothScale (j 2)) (T^(s-1)) f g k
  · simp only [hactive,ite_true]
    apply continuous_finsetSum
    intro i _
    by_cases hselected : if positive then rectangularPositiveQuadGap (i.1.1+1) (i.1.2+1) i.2
      else rectangularNegativeQuadGap (i.1.1+1) (i.1.2+1) i.2
    · simp only [hselected,ite_true]
      exact (a03_actual_time_source_Mellin_continuous hc hT f g Φ hΦ σ α hα hσ dual i.1.1 i.1.2 i.2).const_mul _
    · simp only [hselected,ite_false]
      exact continuous_const
  · simp only [hactive,ite_false]
    exact continuous_const

theorem a03ActualRatioTimeFinite_Mellin_continuous
    {c T : ℝ} (hc : 0<c) (hT : T≠0) (m n dual : Bool) (G : ℂ→ℂ)
    (a b s u : ℝ) (σ α : MomentShifts) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (hα : ∀ j,‖α j‖≤1/4) (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4) :
    Continuous (fun v : ℝ => a03ActualRatioTimeFinite m n dual G c T a b s u v σ α f g Φ) := by
  unfold a03ActualRatioTimeFinite
  apply continuous_finsetSum
  intro positive _
  apply continuous_finsetSum
  intro i _
  exact a03ActualRatioTimeBlock_Mellin_continuous hc hT m n dual positive G a b s σ α f g Φ hΦ hα hσ i.1 i.2

def a03ActualRatioTimeMoment (m n dual : Bool) (G : ℂ→ℂ)
    (c T a b s u θ : ℝ) (σ α : MomentShifts) (f g Φ : ℝ→ℝ) : ℂ :=
  ∫ v in Icc (-θ*Real.log T) (θ*Real.log T),
    a03ActualRatioTimeFinite m n dual G c T a b s u v σ α f g Φ

theorem a03_actual_source_moment_four_chambers
    {a b c T : ℝ} (hc : 0<c) (hT : 1<T) (dual : Bool) (f g Φ : ℝ→ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ)
    (σ : MomentShifts) (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4) (s u θ : ℝ) :
    a03ActualSourcePhysicalMoment dual (fun x => (Φ x:ℂ)) c T a b s u θ σ f g=
      ∑ m : Bool,∑ n : Bool,a03ActualRatioTimeMoment false false dual
        (a03ZeroModeRatioWeight (rawMomentShifts T σ)) c T a b s u θ σ
        (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g Φ := by
  have hT0 : T≠0 := (zero_lt_one.trans hT).ne'
  have hα : ∀ j,‖a03SourceShifts dual T σ j‖≤1/4 := by
    cases dual
    · simpa only [a03SourceShifts,Bool.false_eq_true,ite_false] using hσ
    · exact bblrSixShifts_norm_le _ hσ 1
  have hi (m n : Bool) : IntegrableOn (fun v => a03ActualRatioTimeFinite false false dual
      (a03ZeroModeRatioWeight (rawMomentShifts T σ)) c T a b s u v σ
      (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g Φ)
      (Icc (-θ*Real.log T) (θ*Real.log T)) :=
    (a03ActualRatioTimeFinite_Mellin_continuous hc hT0 false false dual _ a b s u σ _ f g Φ hΦ
      (fun j => hα (a03ZeroModePairPermutation m n j)) hσ).integrableOn_Icc
  unfold a03ActualSourcePhysicalMoment a03ActualRatioTimeMoment
  simp_rw [a03_actual_source_finite_four_chambers hT dual f g Φ hf hg σ c s u]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro m _
    exact integral_finsetSum _ (fun n _ => hi m n)
  · intro m _
    exact integrable_finsetSum _ (fun n _ => hi m n)

end
end SixthMoment
