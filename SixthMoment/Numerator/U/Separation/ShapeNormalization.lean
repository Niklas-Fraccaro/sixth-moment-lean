import SixthMoment.Arithmetic.QuadraticDivisor.ComplexWeights

namespace SixthMoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 1000000

def phasePairSwapScales (m n : Bool) (q : QuadraticScales) : QuadraticScales :=
  ⟨q.A,q.B,if m then q.M₂ else q.M₁,if m then q.M₁ else q.M₂,
    if n then q.N₂ else q.N₁,if n then q.N₁ else q.N₂,q.H⟩

def phasePairSwapTuple (m n : Bool) (v : Fin 7 → ℕ) : Fin 7 → ℕ :=
  ![v 0,v 1,if m then v 3 else v 2,if m then v 2 else v 3,
    if n then v 5 else v 4,if n then v 4 else v 5,v 6]

def phasePairSwapWeights (m n : Bool) (W : Fin 5 → ℝ → ℂ) : Fin 5 → ℝ → ℂ :=
  ![W 0,if m then W 2 else W 1,if m then W 1 else W 2,
    if n then W 4 else W 3,if n then W 3 else W 4]

def phaseSideSwapScales (q : QuadraticScales) : QuadraticScales :=
  ⟨q.B,q.A,q.N₁,q.N₂,q.M₁,q.M₂,q.H⟩

def phaseSideSwapTuple (v : Fin 7 → ℕ) : Fin 7 → ℕ :=
  ![v 1,v 0,v 4,v 5,v 2,v 3,v 6]

def phaseSideSwapWeights (W : Fin 5 → ℝ → ℂ) : Fin 5 → ℝ → ℂ :=
  ![W 0,W 3,W 4,W 1,W 2]

theorem phase_pair_swap_products (m n : Bool) (q : QuadraticScales) :
    (phasePairSwapScales m n q).M=q.M ∧ (phasePairSwapScales m n q).N=q.N ∧
      (phasePairSwapScales m n q).mass=q.mass := by
  cases m <;> cases n <;>
    simp [phasePairSwapScales,QuadraticScales.M,QuadraticScales.N,QuadraticScales.mass,mul_comm]

theorem phase_pair_swap_involution (m n : Bool) (v : Fin 7 → ℕ) :
    phasePairSwapTuple m n (phasePairSwapTuple m n v)=v := by
  funext j
  cases m <;> cases n <;> fin_cases j <;> simp [phasePairSwapTuple]

theorem phase_pair_swap_relation (m n positive : Bool) (v : Fin 7 → ℕ) :
    signedQuadraticRelation positive (phasePairSwapTuple m n v) ↔ signedQuadraticRelation positive v := by
  cases m <;> cases n <;> cases positive <;>
    simp [signedQuadraticRelation,phasePairSwapTuple,mul_comm,mul_left_comm,mul_assoc]

theorem phase_pair_swap_index (m n : Bool) (q : QuadraticScales) (v : Fin 7 → ℕ) :
    phasePairSwapTuple m n v ∈ quadraticIndexSet (phasePairSwapScales m n q) ↔
      v ∈ quadraticIndexSet q := by
  simp only [quadraticIndexSet,Fintype.mem_piFinset]
  cases m <;> cases n <;>
    simp [Fin.forall_fin_succ,phasePairSwapTuple,phasePairSwapScales,QuadraticScales.size]
  all_goals tauto

theorem phase_pair_swap_weighted_term (m n : Bool) (q : QuadraticScales)
    (A B : ℕ → ℂ) (W : Fin 5 → ℝ → ℂ) (v : Fin 7 → ℕ) :
    A ((phasePairSwapTuple m n v) 0)*B ((phasePairSwapTuple m n v) 1)*
      ∏ i : Fin 5, phasePairSwapWeights m n W i
        (rectangularWeightArguments (phasePairSwapScales m n q) (phasePairSwapTuple m n v) i)=
      A (v 0)*B (v 1)*∏ i : Fin 5, W i (rectangularWeightArguments q v i) := by
  cases m <;> cases n <;>
    simp [Fin.prod_univ_five,phasePairSwapTuple,phasePairSwapWeights,phasePairSwapScales,
      rectangularWeightArguments,mul_comm,mul_left_comm,mul_assoc]

theorem phase_pair_swap_quadratic_sum (m n positive : Bool) (q : QuadraticScales)
    (A B : ℕ → ℂ) (W : Fin 5 → ℝ → ℂ) :
    rectangularComplexQuadraticSum positive (phasePairSwapScales m n q) A B
      (phasePairSwapWeights m n W)=rectangularComplexQuadraticSum positive q A B W := by
  unfold rectangularComplexQuadraticSum
  symm
  apply Finset.sum_bij (fun v _ => phasePairSwapTuple m n v)
  · intro v hv
    exact (phase_pair_swap_index m n q v).mpr hv
  · intro a _ b _ h
    have := congrArg (phasePairSwapTuple m n) h
    simpa only [phase_pair_swap_involution] using this
  · intro v hv
    refine ⟨phasePairSwapTuple m n v,?_,phase_pair_swap_involution m n v⟩
    have := (phase_pair_swap_index m n q (phasePairSwapTuple m n v)).mp
      (by simpa only [phase_pair_swap_involution] using hv)
    exact this
  · intro v _
    rw [phase_pair_swap_relation,phase_pair_swap_weighted_term]

theorem phase_side_swap_mass (q : QuadraticScales) :
    (phaseSideSwapScales q).mass=q.mass := by
  simp [phaseSideSwapScales,QuadraticScales.mass,QuadraticScales.M,QuadraticScales.N]
  ring

theorem phase_side_swap_involution (v : Fin 7 → ℕ) :
    phaseSideSwapTuple (phaseSideSwapTuple v)=v := by
  funext j
  fin_cases j <;> simp [phaseSideSwapTuple]

theorem phase_side_swap_relation (positive : Bool) (v : Fin 7 → ℕ) :
    signedQuadraticRelation (!positive) (phaseSideSwapTuple v) ↔ signedQuadraticRelation positive v := by
  cases positive <;> simp [signedQuadraticRelation,phaseSideSwapTuple]
  all_goals constructor <;> intro h <;> linarith

theorem phase_side_swap_index (q : QuadraticScales) (v : Fin 7 → ℕ) :
    phaseSideSwapTuple v ∈ quadraticIndexSet (phaseSideSwapScales q) ↔
      v ∈ quadraticIndexSet q := by
  simp [quadraticIndexSet,Fintype.mem_piFinset,Fin.forall_fin_succ,phaseSideSwapTuple,
    phaseSideSwapScales,QuadraticScales.size]
  tauto

theorem phase_side_swap_weighted_term (q : QuadraticScales)
    (A B : ℕ → ℂ) (W : Fin 5 → ℝ → ℂ) (v : Fin 7 → ℕ) :
    B ((phaseSideSwapTuple v) 0)*A ((phaseSideSwapTuple v) 1)*
      ∏ i : Fin 5, phaseSideSwapWeights W i
        (rectangularWeightArguments (phaseSideSwapScales q) (phaseSideSwapTuple v) i)=
      A (v 0)*B (v 1)*∏ i : Fin 5, W i (rectangularWeightArguments q v i) := by
  simp [Fin.prod_univ_five,phaseSideSwapTuple,phaseSideSwapWeights,phaseSideSwapScales,
    rectangularWeightArguments,mul_comm,mul_left_comm,mul_assoc]

theorem phase_side_swap_quadratic_sum (positive : Bool) (q : QuadraticScales)
    (A B : ℕ → ℂ) (W : Fin 5 → ℝ → ℂ) :
    rectangularComplexQuadraticSum (!positive) (phaseSideSwapScales q) B A
      (phaseSideSwapWeights W)=rectangularComplexQuadraticSum positive q A B W := by
  unfold rectangularComplexQuadraticSum
  symm
  apply Finset.sum_bij (fun v _ => phaseSideSwapTuple v)
  · intro v hv
    exact (phase_side_swap_index q v).mpr hv
  · intro a _ b _ h
    have := congrArg phaseSideSwapTuple h
    simpa only [phase_side_swap_involution] using this
  · intro v hv
    refine ⟨phaseSideSwapTuple v,?_,phase_side_swap_involution v⟩
    exact (phase_side_swap_index q (phaseSideSwapTuple v)).mp
      (by simpa only [phase_side_swap_involution] using hv)
  · intro v _
    rw [phase_side_swap_relation,phase_side_swap_weighted_term]

end
end SixthMoment
