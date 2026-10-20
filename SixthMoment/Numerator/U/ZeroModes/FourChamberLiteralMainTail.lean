import SixthMoment.Numerator.U.DiscrepancyIdentity
import SixthMoment.Numerator.U.ZeroModes.FourChamberMainPair

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 1000000

theorem a03FourChamberMainPairs_minus_literal_crossed_uniform_oT
    {a b : ℝ} (_ha : 0≤a) (hab : a≤b) (hrect : 3*a+5*b<2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (hroot : ∀ σ∈K,∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∀ ε : ℝ,0<ε → ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      ‖(∑ m : Bool,∑ n : Bool,a03ChamberMainPairMoment m n T a b σ f g Φ)-
        ∑ j : Fin 4,bblrIndexedMainTerm ⟨j.val+2,by omega⟩ T a b
          (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ‖≤ε*T := by
  obtain ⟨B,hB⟩ := hK.isBounded.exists_norm_le
  let R := max B 0
  have hR : 0≤R := le_max_right _ _
  have hσR (σ : MomentShifts) (hσ : σ∈K) (j : Fin 4) : ‖σ j‖≤R :=
    ((norm_le_pi_norm σ j).trans (hB σ hσ)).trans (le_max_left _ _)
  have hs := rectangular_slack_bounds hab hrect
  obtain ⟨C,hC,hbound⟩ := a03DiagonalIndexedMainTerm_uniform_power_bound hR hκ hab hs.1
    f g Φ hf hg hΦ
  have hq : rectangularSecondExponent a b (rectangularSlack a b)<1 := by linarith [hs.2.2]
  have hsmall := (rpow_isLittleO_id_of_lt_one hq).const_mul_left (4*C)
  intro ε hε
  filter_upwards [a03ChamberMainPairMoment_eventually_eq_indexed K hK hκ hroot a b f g Φ,
    hbound,hsmall.bound hε,eventually_gt_atTop (0:ℝ)] with T hp hb hsmall hT
  intro σ hσ
  have hpair : (∑ m : Bool,∑ n : Bool,a03ChamberMainPairMoment m n T a b σ f g Φ)=
      ∑ j : Fin 4,a03DiagonalArithmeticIndexedMainTerm ⟨j.val+2,by omega⟩ T a b
        (rawMomentShifts T σ) f g Φ := by
    simp_rw [hp σ hσ]
    simp only [Fintype.sum_bool,a03CrossedChamberLabel,Bool.false_eq_true,ite_false,ite_true,
      Fin.sum_univ_succ]
    norm_num
    ring
  rw [hpair,←Finset.sum_sub_distrib]
  have hb' (j : Fin 4) :
      ‖a03DiagonalArithmeticIndexedMainTerm ⟨j.val+2,by omega⟩ T a b
          (rawMomentShifts T σ) f g Φ-
        bblrIndexedMainTerm ⟨j.val+2,by omega⟩ T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ‖≤
      C*T^(rectangularSecondExponent a b (rectangularSlack a b)) := by
    rw [norm_sub_rev]
    exact hb σ (hσR σ hσ) (hroot σ hσ) _
  calc
    _≤∑ j : Fin 4,‖a03DiagonalArithmeticIndexedMainTerm ⟨j.val+2,by omega⟩ T a b
          (rawMomentShifts T σ) f g Φ-
        bblrIndexedMainTerm ⟨j.val+2,by omega⟩ T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ‖ := norm_sum_le _ _
    _≤∑ _j : Fin 4,C*T^(rectangularSecondExponent a b (rectangularSlack a b)) :=
      Finset.sum_le_sum (fun j _ => hb' j)
    _=(4*C)*T^(rectangularSecondExponent a b (rectangularSlack a b)) := by simp; ring
    _≤ε*T := by
      simpa only [Real.norm_eq_abs,abs_of_pos hT,abs_of_nonneg (by positivity :
        0≤4*C*T^(rectangularSecondExponent a b (rectangularSlack a b)))] using hsmall

end
end SixthMoment
