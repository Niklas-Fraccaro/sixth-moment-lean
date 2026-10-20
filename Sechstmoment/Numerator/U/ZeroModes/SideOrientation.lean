import Sechstmoment.Numerator.U.Sources.Weights.NormalizedData


namespace Sechstmoment
open Complex Real Source Set MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 1000000

def phaseSideSwapMainTuple (n : Fin 5 → ℕ) : Fin 5 → ℕ :=
  ![n 1,n 0,n 3,n 2,n 4]

theorem phase_side_swap_main_tuple_involution (n : Fin 5 → ℕ) :
    phaseSideSwapMainTuple (phaseSideSwapMainTuple n)=n := by
  funext j
  fin_cases j <;> simp [phaseSideSwapMainTuple]

theorem phase_side_swap_main_index (q : QuadraticScales) (n : Fin 5 → ℕ) :
    phaseSideSwapMainTuple n∈quadraticMainIndexSet (phaseSideSwapScales q) ↔
      n∈quadraticMainIndexSet q := by
  simp [quadraticMainIndexSet,Fintype.mem_piFinset,Fin.forall_fin_succ,
    phaseSideSwapMainTuple,phaseSideSwapScales]
  tauto

theorem phase_side_swap_zero_weighted_term (q : QuadraticScales)
    (A B : ℕ → ℂ) (W : Fin 5 → ℝ → ℂ) (n : Fin 5 → ℕ) :
    B ((phaseSideSwapMainTuple n) 0)*A ((phaseSideSwapMainTuple n) 1)*
      (∫ x : ℝ in Ioi 0, ∏ i : Fin 5, phaseSideSwapWeights W i
        (rectangularZeroArguments (phaseSideSwapScales q) (phaseSideSwapMainTuple n) x i))=
      A (n 0)*B (n 1)*∫ x : ℝ in Ioi 0,
        ∏ i : Fin 5, W i (rectangularZeroArguments q n x i) := by
  have hprod : ∀ x : ℝ,
      (∏ i : Fin 5, phaseSideSwapWeights W i
        (rectangularZeroArguments (phaseSideSwapScales q) (phaseSideSwapMainTuple n) x i))=
      ∏ i : Fin 5, W i (rectangularZeroArguments q n x i) := by
    intro x
    simp [Fin.prod_univ_five,phaseSideSwapWeights,rectangularZeroArguments,
      phaseSideSwapScales,phaseSideSwapMainTuple,Nat.gcd_comm,
      mul_comm,mul_left_comm]
  change B (n 1)*A (n 0)*(∫ x : ℝ in Ioi 0,
    ∏ i : Fin 5, phaseSideSwapWeights W i
      (rectangularZeroArguments (phaseSideSwapScales q) (phaseSideSwapMainTuple n) x i)) = _
  simp_rw [hprod]
  ring

theorem phase_side_swap_complex_zero_mode (q : QuadraticScales)
    (A B : ℕ → ℂ) (W : Fin 5 → ℝ → ℂ) :
    rectangularComplexZeroMode (phaseSideSwapScales q) B A
      (phaseSideSwapWeights W)=rectangularComplexZeroMode q A B W := by
  unfold rectangularComplexZeroMode
  symm
  apply Finset.sum_bij (fun n _ => phaseSideSwapMainTuple n)
  · intro n hn
    exact (phase_side_swap_main_index q n).mpr hn
  · intro n _ m _ h
    have he := congrArg phaseSideSwapMainTuple h
    simpa only [phase_side_swap_main_tuple_involution] using he
  · intro n hn
    refine ⟨phaseSideSwapMainTuple n,?_,phase_side_swap_main_tuple_involution n⟩
    exact (phase_side_swap_main_index q (phaseSideSwapMainTuple n)).mp
      (by simpa only [phase_side_swap_main_tuple_involution] using hn)
  · intro n _
    exact (phase_side_swap_zero_weighted_term q A B W n).symm

theorem phase_side_swap_complex_discrepancy (positive : Bool) (q : QuadraticScales)
    (A B : ℕ → ℂ) (W : Fin 5 → ℝ → ℂ) :
    rectangularComplexDiscrepancy (!positive) (phaseSideSwapScales q) B A
      (phaseSideSwapWeights W)=rectangularComplexDiscrepancy positive q A B W := by
  unfold rectangularComplexDiscrepancy
  rw [phase_side_swap_quadratic_sum,phase_side_swap_complex_zero_mode]

theorem phase_normalized_complex_zero_mode_eq_sorted (q : QuadraticScales)
    (A B : ℕ → ℂ) (W : Fin 5 → ℝ → ℂ) :
    rectangularComplexZeroMode (phaseNormalizedScales q)
      (phaseNormalizedAlpha q A B) (phaseNormalizedBeta q A B)
      (phaseNormalizedWeights q W)=
      rectangularComplexZeroMode (phaseSortedScales q) A B (phaseSortedWeights q W) := by
  unfold phaseNormalizedScales phaseNormalizedAlpha phaseNormalizedBeta phaseNormalizedWeights
  dsimp only
  split_ifs
  · rfl
  · exact phase_side_swap_complex_zero_mode _ _ _ _

end
end Sechstmoment
