import SixthMoment.Numerator.U.Sources.BlockReindex
import SixthMoment.Numerator.U.ZeroModes.DiscreteChamberSymmetry
import SixthMoment.Numerator.U.ZeroModes.Ratio.ChamberWeight

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def a03ActualRatioTimeBlock (m n dual positive : Bool) (G : ℂ→ℂ)
    (c T a b s v : ℝ) (σ α : MomentShifts) (f g Φ : ℝ→ℝ)
    (j : Fin 3→ℕ) (k : Fin 4→ℕ) : ℂ :=
  if phaseActualActiveNearBlock T (rectangularAFESmoothScale (j 0))
    (rectangularAFESmoothScale (j 1)) (rectangularAFESmoothScale (j 2)) (T^(s-1)) f g k then
    ∑ i∈((Finset.range ⌊T^a⌋₊).product (Finset.range ⌊T^b⌋₊)).product (rectangularAFESmoothBox k),
      if (if positive then rectangularPositiveQuadGap (i.1.1+1) (i.1.2+1) i.2
        else rectangularNegativeQuadGap (i.1.1+1) (i.1.2+1) i.2) then
        (a03SourceAmplifierGapWeight (i.1.1+1) (i.1.2+1)
          (rectangularAFEGap positive (i.1.1+1) (i.1.2+1) i.2) j:ℂ)*
          (rectangularAFESmoothWeight k i.2:ℂ)*
            a03ZeroModeRatioFourWeight G m n (i.2 0+1) (i.2 1+1) (i.2 2+1) (i.2 3+1)*
              ∫ t : ℝ, rectangularMomentPairWeight T f g Φ i.1.1 i.1.2 t*
                (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
                  rectangularAFEMellinKernel (polarPoleKiller T σ) α t i.2
                    ((c:ℂ)+(v:ℂ)*I) else 0
  else 0

theorem a03_actual_source_block_four_ratio_partition {a b T : ℝ} (hT : 1<T)
    (dual positive : Bool) (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (σ : MomentShifts) (c s v : ℝ)
    (j : Fin 3→ℕ) (k : Fin 4→ℕ) (G : ℂ→ℂ) (γ : MomentShifts)
    (hG : BBLREntireWeight G γ) :
    a03ActualSourceBlockValue false dual positive (fun x => (Φ x:ℂ)) c T s v σ f g (j,k)=
      ∑ m : Bool,∑ n : Bool,a03ActualRatioTimeBlock m n dual positive G
        c T a b s v σ (a03SourceShifts dual T σ) f g Φ j k := by
  rw [a03ActualSourceBlockValue_finite_reindex hT dual positive f g Φ hf hg σ c s v]
  unfold a03ActualRatioTimeBlock
  by_cases hactive : phaseActualActiveNearBlock T (rectangularAFESmoothScale (j 0))
    (rectangularAFESmoothScale (j 1)) (rectangularAFESmoothScale (j 2)) (T^(s-1)) f g k
  · simp only [hactive,ite_true]
    conv_rhs => arg 2; ext m; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hselected : if positive then rectangularPositiveQuadGap (i.1.1+1) (i.1.2+1) i.2
      else rectangularNegativeQuadGap (i.1.1+1) (i.1.2+1) i.2
    · simp only [hselected,ite_true]
      have he := a03_zero_ratio_four_weight_sum G γ hG
        (by positivity : (0:ℝ) < (i.2 0:ℝ)+1) (by positivity : (0:ℝ) < (i.2 1:ℝ)+1)
        (by positivity : (0:ℝ) < (i.2 2:ℝ)+1) (by positivity : (0:ℝ) < (i.2 3:ℝ)+1)
      let C : ℂ := (a03SourceAmplifierGapWeight (i.1.1+1) (i.1.2+1)
        (rectangularAFEGap positive (i.1.1+1) (i.1.2+1) i.2) j:ℂ)*(rectangularAFESmoothWeight k i.2:ℂ)
      let I : ℂ := ∫ t : ℝ, rectangularMomentPairWeight T f g Φ i.1.1 i.1.2 t*
        (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
          rectangularAFEMellinKernel (polarPoleKiller T σ) (a03SourceShifts dual T σ) t i.2 ((c:ℂ)+(v:ℂ)*Complex.I)
      change C*I=∑ m : Bool,∑ n : Bool,C*a03ZeroModeRatioFourWeight G m n
        (i.2 0+1) (i.2 1+1) (i.2 2+1) (i.2 3+1)*I
      calc
        _=(C*I)*1 := by ring
        _=(C*I)*(∑ m : Bool,∑ n : Bool,a03ZeroModeRatioFourWeight G m n
            (i.2 0+1) (i.2 1+1) (i.2 2+1) (i.2 3+1)) := by rw [he]
        _=_ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _
          ring
    · simp only [hselected,ite_false,Finset.sum_const_zero]
  · simp only [hactive,ite_false,Finset.sum_const_zero]

theorem a03_zero_ratio_four_weight_discrete_pair_swap (G : ℂ→ℂ)
    (m n : Bool) (v : Fin 4→ℕ) :
    a03ZeroModeRatioFourWeight G false false
      (a03ZeroModeDiscretePairSwap m n v 0+1) (a03ZeroModeDiscretePairSwap m n v 1+1)
      (a03ZeroModeDiscretePairSwap m n v 2+1) (a03ZeroModeDiscretePairSwap m n v 3+1)=
      a03ZeroModeRatioFourWeight G m n (v 0+1) (v 1+1) (v 2+1) (v 3+1) := by
  cases m <;> cases n <;>
    simp [a03ZeroModeRatioFourWeight,a03ZeroModeDiscretePairSwap,a03ZeroModePairPermutation]

theorem a03ActualRatioTimeBlock_discrete_chamber
    (m n dual positive : Bool) (G : ℂ→ℂ) (c T a b s v : ℝ)
    (σ α : MomentShifts) (f g Φ : ℝ→ℝ) (j : Fin 3→ℕ) (k : Fin 4→ℕ) :
    a03ActualRatioTimeBlock m n dual positive G c T a b s v σ α f g Φ j k=
      a03ActualRatioTimeBlock false false dual positive G c T a b s v σ
        (a03ZeroModeChamberShifts m n α) f g Φ j (a03ZeroModeDiscretePairSwap m n k) := by
  unfold a03ActualRatioTimeBlock
  rw [a03ZeroModeDiscretePairSwap_active_near]
  by_cases hactive : phaseActualActiveNearBlock T (rectangularAFESmoothScale (j 0))
    (rectangularAFESmoothScale (j 1)) (rectangularAFESmoothScale (j 2)) (T^(s-1)) f g k
  · simp only [hactive,ite_true]
    apply Finset.sum_bij (fun i _ => (i.1,a03ZeroModeDiscretePairSwap m n i.2))
    · intro i hi
      have hi := Finset.mem_product.mp hi
      exact Finset.mem_product.mpr ⟨hi.1,(a03ZeroModeDiscretePairSwap_smooth_box m n k i.2).mpr hi.2⟩
    · intro i _ l _ he
      have h1 := congrArg Prod.fst he
      have h2 := congrArg (fun z => a03ZeroModeDiscretePairSwap m n z.2) he
      simp only [a03ZeroModeDiscretePairSwap_involution] at h2
      exact Prod.ext h1 h2
    · intro i hi
      have hi := Finset.mem_product.mp hi
      refine ⟨(i.1,a03ZeroModeDiscretePairSwap m n i.2),?_,?_⟩
      · apply Finset.mem_product.mpr
        exact ⟨hi.1,(a03ZeroModeDiscretePairSwap_smooth_box m n k _).mp
          (by simpa only [a03ZeroModeDiscretePairSwap_involution] using hi.2)⟩
      · simp only [a03ZeroModeDiscretePairSwap_involution]
    · intro i _
      dsimp only
      simp only [a03ZeroModeDiscretePairSwap_selected,a03ZeroModeDiscretePairSwap_gap,
        a03ZeroModeDiscretePairSwap_smooth_weight,a03_zero_ratio_four_weight_discrete_pair_swap]
      simp_rw [rectangularAFEMellinKernel_discrete_chamber]
  · simp only [hactive,ite_false]

def a03ActualRatioTimeFinite (m n dual : Bool) (G : ℂ→ℂ)
    (c T a b s u v : ℝ) (σ α : MomentShifts) (f g Φ : ℝ→ℝ) : ℂ :=
  ∑ positive : Bool, ∑ i∈a03ActualSourceBlockGrid (T^a) (T^b)
    (8*T^((a+b)/2+s+u/2)) (T^(2+u)),
      a03ActualRatioTimeBlock m n dual positive G c T a b s v σ α f g Φ i.1 i.2

theorem a03ActualRatioTimeFinite_discrete_chamber {T : ℝ} (hT : 0<T)
    (m n dual : Bool) (G : ℂ→ℂ) (c a b s u v : ℝ)
    (σ α : MomentShifts) (f g Φ : ℝ→ℝ) :
    a03ActualRatioTimeFinite m n dual G c T a b s u v σ α f g Φ=
      a03ActualRatioTimeFinite false false dual G c T a b s u v σ
        (a03ZeroModeChamberShifts m n α) f g Φ := by
  unfold a03ActualRatioTimeFinite
  apply Finset.sum_congr rfl
  intro positive _
  unfold a03ActualSourceBlockGrid
  apply Finset.sum_bij (fun i _ => (i.1,a03ZeroModeDiscretePairSwap m n i.2))
  · intro i hi
    have hi := Finset.mem_product.mp hi
    exact Finset.mem_product.mpr ⟨hi.1,(a03ZeroModeDiscretePairSwap_grid (Real.rpow_pos_of_pos hT _) m n i.2).mpr hi.2⟩
  · intro i _ l _ he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg (fun z => a03ZeroModeDiscretePairSwap m n z.2) he
    simp only [a03ZeroModeDiscretePairSwap_involution] at h2
    exact Prod.ext h1 h2
  · intro i hi
    have hi := Finset.mem_product.mp hi
    refine ⟨(i.1,a03ZeroModeDiscretePairSwap m n i.2),?_,?_⟩
    · exact Finset.mem_product.mpr ⟨hi.1,(a03ZeroModeDiscretePairSwap_grid (Real.rpow_pos_of_pos hT _) m n i.2).mpr hi.2⟩
    · simp only [a03ZeroModeDiscretePairSwap_involution]
  · intro i _
    exact a03ActualRatioTimeBlock_discrete_chamber m n dual positive G c T a b s v σ α f g Φ i.1 i.2

theorem a03_actual_source_finite_four_ratio_partition {a b T : ℝ} (hT : 1<T)
    (dual : Bool) (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (σ : MomentShifts) (c s u v : ℝ)
    (G : ℂ→ℂ) (γ : MomentShifts) (hG : BBLREntireWeight G γ) :
    a03ActualSourceFiniteValue false dual (fun x => (Φ x:ℂ)) c T a b s u v σ f g=
      ∑ m : Bool,∑ n : Bool,a03ActualRatioTimeFinite m n dual G
        c T a b s u v σ (a03SourceShifts dual T σ) f g Φ := by
  unfold a03ActualSourceFiniteValue a03ActualRatioTimeFinite
  simp_rw [a03_actual_source_block_four_ratio_partition hT dual _ f g Φ hf hg σ c s v _ _ G γ hG]
  simp only [Fintype.sum_bool]
  simp_rw [Finset.sum_add_distrib]
  ring

theorem a03_actual_source_finite_four_chambers {a b T : ℝ} (hT : 1<T)
    (dual : Bool) (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (σ : MomentShifts) (c s u v : ℝ) :
    a03ActualSourceFiniteValue false dual (fun x => (Φ x:ℂ)) c T a b s u v σ f g=
      ∑ m : Bool,∑ n : Bool,a03ActualRatioTimeFinite false false dual
        (a03ZeroModeRatioWeight (rawMomentShifts T σ)) c T a b s u v σ
        (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g Φ := by
  rw [a03_actual_source_finite_four_ratio_partition hT dual f g Φ hf hg σ c s u v
    (a03ZeroModeRatioWeight (rawMomentShifts T σ)) (rawMomentShifts T σ)
    (a03ZeroModeRatioWeight_admissible _)]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  exact a03ActualRatioTimeFinite_discrete_chamber (zero_lt_one.trans hT) m n dual _ c a b s u v σ _ f g Φ

end
end SixthMoment
