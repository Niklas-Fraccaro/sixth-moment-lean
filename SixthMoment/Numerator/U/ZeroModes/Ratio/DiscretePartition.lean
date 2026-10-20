import SixthMoment.Numerator.U.Reconstruction.TensorActualSourceEndpoint
import SixthMoment.Numerator.U.ZeroModes.Contour.RatioPartition

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
open Classical
noncomputable section
set_option maxHeartbeats 1000000

def a03ZeroModeRatioFourWeight (G : ℂ→ℂ) (m n : Bool) (x₁ x₂ x₃ x₄ : ℝ) : ℂ :=
  a03ZeroModeRatioPartition G (if m then x₂/x₁ else x₁/x₂)*
    a03ZeroModeRatioPartition G (if n then x₄/x₃ else x₃/x₄)

theorem a03_zero_ratio_four_weight_sum (G : ℂ→ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) {x₁ x₂ x₃ x₄ : ℝ}
    (hx₁ : 0<x₁) (hx₂ : 0<x₂) (hx₃ : 0<x₃) (hx₄ : 0<x₄) :
    (∑ m : Bool, ∑ n : Bool,a03ZeroModeRatioFourWeight G m n x₁ x₂ x₃ x₄)=1 := by
  have hm := a03ZeroModeRatioPartition_identity (div_pos hx₁ hx₂) G α hG
  have hn := a03ZeroModeRatioPartition_identity (div_pos hx₃ hx₄) G α hG
  rw [inv_div] at hm hn
  calc
    _=(a03ZeroModeRatioPartition G (x₁/x₂)+a03ZeroModeRatioPartition G (x₂/x₁))*
        (a03ZeroModeRatioPartition G (x₃/x₄)+a03ZeroModeRatioPartition G (x₄/x₃)) := by
      simp only [Fintype.sum_bool,a03ZeroModeRatioFourWeight,Bool.false_eq_true,ite_false,ite_true]
      ring
    _=1 := by rw [hm,hn]; ring

def a03ZeroModeRatioDiscreteSource (positive m n : Bool) (G : ℂ→ℂ)
    (q : QuadraticScales) (α β : ℕ→ℂ) (F : (Fin 7→ℕ)→ℂ) : ℂ :=
  ∑ w∈quadraticIndexSet q, if signedQuadraticRelation positive w then
    α (w 0)*β (w 1)*a03ZeroModeRatioFourWeight G m n (w 2) (w 3) (w 4) (w 5)*F w else 0

theorem a03_zero_ratio_discrete_source_partition (positive : Bool)
    (G : ℂ→ℂ) (γ : MomentShifts) (hG : BBLREntireWeight G γ)
    (q : QuadraticScales) (α β : ℕ→ℂ) (F : (Fin 7→ℕ)→ℂ) :
    (∑ w∈quadraticIndexSet q, if signedQuadraticRelation positive w then
      α (w 0)*β (w 1)*F w else 0)=
      ∑ m : Bool,∑ n : Bool,a03ZeroModeRatioDiscreteSource positive m n G q α β F := by
  unfold a03ZeroModeRatioDiscreteSource
  conv_rhs => arg 2; ext m; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hr : signedQuadraticRelation positive w
  · simp only [hr,ite_true]
    have hp (j : Fin 7) : 0<(w j:ℝ) := by
      have h := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hw j)).1
      exact_mod_cast (show 0<w j by omega)
    have he := a03_zero_ratio_four_weight_sum G γ hG (hp 2) (hp 3) (hp 4) (hp 5)
    calc
      _=(α (w 0)*β (w 1)*F w)*1 := by ring
      _=(α (w 0)*β (w 1)*F w)*(∑ m : Bool,∑ n : Bool,
        a03ZeroModeRatioFourWeight G m n (w 2) (w 3) (w 4) (w 5)) := by rw [he]
      _=_ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        ring
  · simp only [hr,ite_false,Finset.sum_const_zero]

theorem a03_zero_ratio_four_weight_pair_swap (G : ℂ→ℂ) (m n : Bool) (w : Fin 7→ℕ) :
    a03ZeroModeRatioFourWeight G false false
      (phasePairSwapTuple m n w 2) (phasePairSwapTuple m n w 3)
      (phasePairSwapTuple m n w 4) (phasePairSwapTuple m n w 5)=
      a03ZeroModeRatioFourWeight G m n (w 2) (w 3) (w 4) (w 5) := by
  cases m <;> cases n <;> simp [a03ZeroModeRatioFourWeight,phasePairSwapTuple]

theorem a03_zero_ratio_discrete_source_pair_swap (positive m n : Bool) (G : ℂ→ℂ)
    (q : QuadraticScales) (α β : ℕ→ℂ) (F : (Fin 7→ℕ)→ℂ) :
    a03ZeroModeRatioDiscreteSource positive m n G q α β F=
      a03ZeroModeRatioDiscreteSource positive false false G (phasePairSwapScales m n q)
        α β (fun w => F (phasePairSwapTuple m n w)) := by
  unfold a03ZeroModeRatioDiscreteSource
  apply Finset.sum_bij (fun w _ => phasePairSwapTuple m n w)
  · intro w hw
    exact (phase_pair_swap_index m n q w).mpr hw
  · intro w _ v _ he
    have h := congrArg (phasePairSwapTuple m n) he
    simpa only [phase_pair_swap_involution] using h
  · intro w hw
    refine ⟨phasePairSwapTuple m n w,?_,phase_pair_swap_involution m n w⟩
    exact (phase_pair_swap_index m n q (phasePairSwapTuple m n w)).mp
      (by simpa only [phase_pair_swap_involution] using hw)
  · intro w _
    dsimp only
    rw [phase_pair_swap_relation,phase_pair_swap_involution,a03_zero_ratio_four_weight_pair_swap]
    simp only [phasePairSwapTuple,Matrix.cons_val_zero,Matrix.cons_val_one]

end
end SixthMoment
