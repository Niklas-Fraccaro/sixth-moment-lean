import Sechstmoment.Numerator.U.Sources.FiniteReindex
import Sechstmoment.Numerator.U.ZeroModes.PolarChamberInvariance
import Sechstmoment.Numerator.U.ZeroModes.Ratio.DiscretePartition

/-! Exact chamber symmetries are performed on the four integer AFE
variables, together with their actual shifts and dyadic scales. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def a03ZeroModeDiscretePairSwap (m n : Bool) (v : Fin 4→ℕ) : Fin 4→ℕ :=
  fun j => v (a03ZeroModePairPermutation m n j)

@[simp] theorem a03ZeroModeDiscretePairSwap_involution (m n : Bool) (v : Fin 4→ℕ) :
    a03ZeroModeDiscretePairSwap m n (a03ZeroModeDiscretePairSwap m n v)=v := by
  funext j
  simp [a03ZeroModeDiscretePairSwap]

theorem a03ZeroModeDiscretePairSwap_sourceTuple (m n : Bool) (a b h : ℕ) (v : Fin 4→ℕ) :
    rectangularAFESourceTuple a b (a03ZeroModeDiscretePairSwap m n v) h=
      phasePairSwapTuple m n (rectangularAFESourceTuple a b v h) := by
  ext j
  cases m <;> cases n <;> fin_cases j <;>
    simp [a03ZeroModeDiscretePairSwap,a03ZeroModePairPermutation,rectangularAFESourceTuple,phasePairSwapTuple]

theorem a03ZeroModeDiscretePairSwap_scale_product (m n : Bool) (k : Fin 4→ℕ) :
    (∏ j : Fin 4,rectangularAFESmoothScale (a03ZeroModeDiscretePairSwap m n k j))=
      ∏ j : Fin 4,rectangularAFESmoothScale (k j) := by
  cases m <;> cases n <;>
    simp [a03ZeroModeDiscretePairSwap,a03ZeroModePairPermutation,Fin.prod_univ_four,
      mul_comm,mul_left_comm,mul_assoc]

theorem a03ZeroModeDiscretePairSwap_grid {X : ℝ} (hX : 0<X)
    (m n : Bool) (k : Fin 4→ℕ) :
    a03ZeroModeDiscretePairSwap m n k∈rectangularAFEProductScaleGrid X ↔
      k∈rectangularAFEProductScaleGrid X := by
  rw [rectangular_AFE_product_scale_grid_mem_iff hX,rectangular_AFE_product_scale_grid_mem_iff hX,
    a03ZeroModeDiscretePairSwap_scale_product]

theorem a03ZeroModeDiscretePairSwap_smooth_weight (m n : Bool) (k v : Fin 4→ℕ) :
    rectangularAFESmoothWeight (a03ZeroModeDiscretePairSwap m n k) (a03ZeroModeDiscretePairSwap m n v)=
      rectangularAFESmoothWeight k v := by
  cases m <;> cases n <;>
    simp [rectangularAFESmoothWeight,a03ZeroModeDiscretePairSwap,a03ZeroModePairPermutation,
      Fin.prod_univ_four,mul_comm,mul_left_comm,mul_assoc]

theorem a03ZeroModeDiscretePairSwap_smooth_box (m n : Bool) (k v : Fin 4→ℕ) :
    a03ZeroModeDiscretePairSwap m n v∈rectangularAFESmoothBox (a03ZeroModeDiscretePairSwap m n k) ↔
      v∈rectangularAFESmoothBox k := by
  cases m <;> cases n <;>
    simp [rectangularAFESmoothBox,Fintype.mem_piFinset,Fin.forall_fin_succ,
      a03ZeroModeDiscretePairSwap,a03ZeroModePairPermutation]
  all_goals tauto

theorem a03ZeroModeDiscretePairSwap_gap (m n positive : Bool) (a b : ℕ) (v : Fin 4→ℕ) :
    rectangularAFEGap positive a b (a03ZeroModeDiscretePairSwap m n v)=rectangularAFEGap positive a b v := by
  cases m <;> cases n <;> cases positive <;>
    simp [rectangularAFEGap,a03ZeroModeDiscretePairSwap,a03ZeroModePairPermutation,
      mul_comm,mul_left_comm,mul_assoc]

theorem a03ZeroModeDiscretePairSwap_selected (m n positive : Bool) (a b : ℕ) (v : Fin 4→ℕ) :
    (if positive then rectangularPositiveQuadGap a b (a03ZeroModeDiscretePairSwap m n v)
      else rectangularNegativeQuadGap a b (a03ZeroModeDiscretePairSwap m n v)) ↔
      (if positive then rectangularPositiveQuadGap a b v else rectangularNegativeQuadGap a b v) := by
  cases m <;> cases n <;> cases positive <;>
    simp [rectangularPositiveQuadGap,rectangularNegativeQuadGap,a03ZeroModeDiscretePairSwap,
      a03ZeroModePairPermutation,mul_comm,mul_left_comm,mul_assoc]

theorem a03ZeroModeDiscretePairSwap_near_relation (m n : Bool) (η : ℝ) (a b h : ℕ) (v : Fin 4→ℕ) :
    rectangularNearRelation η (rectangularAFESourceTuple a b (a03ZeroModeDiscretePairSwap m n v) h) ↔
      rectangularNearRelation η (rectangularAFESourceTuple a b v h) := by
  cases m <;> cases n <;>
    simp [rectangularNearRelation,rectangularAFESourceTuple,a03ZeroModeDiscretePairSwap,
      a03ZeroModePairPermutation,mul_comm,mul_left_comm,mul_assoc]

theorem a03ZeroModeDiscretePairSwap_active_near (m n : Bool) (T A B H η : ℝ)
    (f g : ℝ→ℝ) (k : Fin 4→ℕ) :
    phaseActualActiveNearBlock T A B H η f g (a03ZeroModeDiscretePairSwap m n k) ↔
      phaseActualActiveNearBlock T A B H η f g k := by
  have hforward : ∀ k : Fin 4→ℕ, phaseActualActiveNearBlock T A B H η f g k →
      phaseActualActiveNearBlock T A B H η f g (a03ZeroModeDiscretePairSwap m n k) := by
    intro k h
    obtain ⟨a,b,h,v,positive,ha,hb,hw,hh,hr,hn⟩ := h
    refine ⟨a,b,h,a03ZeroModeDiscretePairSwap m n v,positive,ha,hb,?_,hh,?_,?_⟩
    · simpa only [a03ZeroModeDiscretePairSwap_smooth_weight] using hw
    · rw [a03ZeroModeDiscretePairSwap_sourceTuple,phase_pair_swap_relation]
      exact hr
    · exact (a03ZeroModeDiscretePairSwap_near_relation m n η a b h v).mpr hn
  exact ⟨fun h => by simpa only [a03ZeroModeDiscretePairSwap_involution] using hforward _ h,hforward k⟩

theorem bblrGammaQuotient_discrete_chamber (m n : Bool) (t : ℝ) (α : MomentShifts) (z : ℂ) :
    bblrGammaQuotient t (a03ZeroModeChamberShifts m n α) z=bblrGammaQuotient t α z := by
  cases m <;> cases n <;>
    simp [bblrGammaQuotient,sourceZetaPoints,a03ZeroModeChamberShifts,a03ZeroModePairPermutation,
      Fin.prod_univ_four,mul_comm,mul_left_comm,mul_assoc]

theorem rectangularAFEMellinKernel_discrete_chamber (m n : Bool) (G : ℂ→ℂ)
    (α : MomentShifts) (t : ℝ) (v : Fin 4→ℕ) (z : ℂ) :
    rectangularAFEMellinKernel G (a03ZeroModeChamberShifts m n α) t
      (a03ZeroModeDiscretePairSwap m n v) z=rectangularAFEMellinKernel G α t v z := by
  rw [rectangularAFEMellinKernel,bblrGammaQuotient_discrete_chamber]
  unfold rectangularAFEMellinKernel
  have hp : rectangularAFEOscillation t (a03ZeroModeDiscretePairSwap m n v)=rectangularAFEOscillation t v := by
    cases m <;> cases n <;>
      simp [rectangularAFEOscillation,a03ZeroModeDiscretePairSwap,a03ZeroModePairPermutation,mul_comm]
  rw [hp]
  congr 1
  cases m <;> cases n <;>
    simp [a03ZeroModeChamberShifts,a03ZeroModeDiscretePairSwap,a03ZeroModePairPermutation,
      Fin.prod_univ_four,mul_comm,mul_left_comm,mul_assoc]

end
end Sechstmoment
