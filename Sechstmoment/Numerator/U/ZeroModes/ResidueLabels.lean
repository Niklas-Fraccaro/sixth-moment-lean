import Sechstmoment.Numerator.U.ZeroModes.Contour.Chambers


namespace Sechstmoment.Source
open Complex MeasureTheory
open scoped BigOperators
open Classical
noncomputable section

def a03ZeroModePairIndices (m n : Bool) : (Fin 4 → ℕ) ≃ (Fin 4 → ℕ) where
  toFun v := fun j => v (a03ZeroModePairPermutation m n j)
  invFun v := fun j => v (a03ZeroModePairPermutation m n j)
  left_inv v := by funext j; simp
  right_inv v := by funext j; simp

theorem a03ZeroModePairIndices_product (m n : Bool) (v : Fin 4 → ℕ) :
    positiveQuadProduct (a03ZeroModePairIndices m n v) = positiveQuadProduct v := by
  cases m <;> cases n <;>
    simp [positiveQuadProduct, a03ZeroModePairIndices, a03ZeroModePairPermutation] <;> ring

theorem a03ZeroModePairIndices_relation (m n : Bool) (u v : ℕ) (k : Fin 4 → ℕ) :
    diagonalQuadRelation u v (a03ZeroModePairIndices m n k) ↔
      diagonalQuadRelation u v k := by
  cases m <;> cases n <;>
    simp [diagonalQuadRelation, a03ZeroModePairIndices, a03ZeroModePairPermutation,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem a03ZeroModePairIndices_summand (m n : Bool) (G : ℂ → ℂ)
    (α : MomentShifts) (u v : ℕ) (t : ℝ) (k : Fin 4 → ℕ) :
    bblrDiagonalSummand G (a03ZeroModeChamberShifts m n α) u v t k =
      bblrDiagonalSummand G α u v t (a03ZeroModePairIndices m n k) := by
  unfold bblrDiagonalSummand
  rw [a03ZeroModePairIndices_product]
  congr 1
  change (∏ j : Fin 4, (k j+1:ℂ)^(1/2+a03ZeroModeChamberShifts m n α j)) =
    ∏ j : Fin 4, (k (a03ZeroModePairPermutation m n j)+1:ℂ)^(1/2+α j)
  cases m <;> cases n <;>
    rw [Fin.prod_univ_four, Fin.prod_univ_four] <;>
    dsimp [a03ZeroModeChamberShifts,
      a03ZeroModePairPermutation] <;> ring

theorem bblrDiagonalTerm_zeroMode_chamber (m n : Bool) (G : ℂ → ℂ)
    (α : MomentShifts) (u v : ℕ) (t : ℝ) :
    bblrDiagonalTerm G (a03ZeroModeChamberShifts m n α) u v t =
      bblrDiagonalTerm G α u v t := by
  unfold bblrDiagonalTerm
  rw [← ((a03ZeroModePairIndices m n).tsum_eq (fun k =>
    if diagonalQuadRelation u v k then bblrDiagonalSummand G α u v t k else 0))]
  apply tsum_congr
  intro k
  rw [a03ZeroModePairIndices_relation, ← a03ZeroModePairIndices_summand]

def a03ZeroModeResidueShifts (α : MomentShifts) : MomentShifts :=
  ![α 0, -α 3, α 2, -α 1]

def a03ZeroModeResidueLabel (m n : Bool) : Fin 6 :=
  if m then (if n then 2 else 3) else (if n then 4 else 5)

theorem a03ZeroModeResidueLabel_crossed (m n : Bool) :
    2 ≤ (a03ZeroModeResidueLabel m n).val := by
  cases m <;> cases n <;> norm_num [a03ZeroModeResidueLabel]

theorem a03ZeroModeResidueShifts_chamber (m n : Bool) (α : MomentShifts) :
    a03ZeroModeResidueShifts (a03ZeroModeChamberShifts m n α) =
      a03ZeroModeChamberShifts m n (bblrSixShifts α (a03ZeroModeResidueLabel m n)) := by
  funext j
  cases m <;> cases n <;> fin_cases j <;>
    simp [a03ZeroModeResidueShifts, a03ZeroModeChamberShifts,
      a03ZeroModePairPermutation, a03ZeroModeResidueLabel, bblrSixShifts]

theorem a03ZeroModeResidue_phase (m n : Bool) (α : MomentShifts) :
    -(a03ZeroModeChamberShifts m n α 1)-(a03ZeroModeChamberShifts m n α 3) =
      bblrSixPhaseExponents α (a03ZeroModeResidueLabel m n) := by
  cases m <;> cases n <;>
    dsimp [a03ZeroModeChamberShifts, a03ZeroModePairPermutation,
      a03ZeroModeResidueLabel, bblrSixPhaseExponents]

theorem bblrDiagonalTerm_zeroMode_residue_label (m n : Bool) (G : ℂ → ℂ)
    (α : MomentShifts) (u v : ℕ) (t : ℝ) :
    bblrDiagonalTerm G (a03ZeroModeResidueShifts (a03ZeroModeChamberShifts m n α))
      u v t = bblrDiagonalTerm G (bblrSixShifts α (a03ZeroModeResidueLabel m n)) u v t := by
  rw [a03ZeroModeResidueShifts_chamber, bblrDiagonalTerm_zeroMode_chamber]

theorem bblrDiagonalTerm_zeroMode_residue_weighted_label (m n : Bool)
    (G : ℂ → ℂ) (α : MomentShifts) (u v : ℕ) (t : ℝ) :
    (t/(2*Real.pi):ℂ)^(-(a03ZeroModeChamberShifts m n α 1)-
      (a03ZeroModeChamberShifts m n α 3))*
      bblrDiagonalTerm G (a03ZeroModeResidueShifts (a03ZeroModeChamberShifts m n α))
        u v t =
      (t/(2*Real.pi):ℂ)^(bblrSixPhaseExponents α (a03ZeroModeResidueLabel m n))*
        bblrDiagonalTerm G (bblrSixShifts α (a03ZeroModeResidueLabel m n)) u v t := by
  rw [a03ZeroModeResidue_phase, bblrDiagonalTerm_zeroMode_residue_label]

theorem bblrDiagonalTerm_zeroMode_four_residue_sum (G : ℂ → ℂ)
    (α : MomentShifts) (u v : ℕ) (t : ℝ) :
    (∑ m : Bool, ∑ n : Bool,
      (t/(2*Real.pi):ℂ)^(-(a03ZeroModeChamberShifts m n α 1)-
        (a03ZeroModeChamberShifts m n α 3))*
        bblrDiagonalTerm G (a03ZeroModeResidueShifts (a03ZeroModeChamberShifts m n α))
          u v t) =
      ∑ j : Fin 4,
        (t/(2*Real.pi):ℂ)^(bblrSixPhaseExponents α ⟨j.val+2, by omega⟩)*
          bblrDiagonalTerm G (bblrSixShifts α ⟨j.val+2, by omega⟩) u v t := by
  simp_rw [bblrDiagonalTerm_zeroMode_residue_weighted_label]
  simp [Fin.sum_univ_four, a03ZeroModeResidueLabel]
  ring

end
end Sechstmoment.Source
