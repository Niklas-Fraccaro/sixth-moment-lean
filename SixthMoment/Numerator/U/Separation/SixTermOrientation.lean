import Mathlib.Tactic
import SixthMoment.Zeta.AFE.Four.Terms

namespace SixthMoment.Source
open Complex MeasureTheory
open scoped BigOperators
open Classical
noncomputable section

def a03BothPairFlip (j : Fin 4) : Fin 4 := ![1, 0, 3, 2] j

@[simp] theorem a03BothPairFlip_involutive (j : Fin 4) :
    a03BothPairFlip (a03BothPairFlip j) = j := by
  fin_cases j <;> norm_num [a03BothPairFlip]

def a03BothPairFlipIndices : (Fin 4 → ℕ) ≃ (Fin 4 → ℕ) where
  toFun n := fun j => n (a03BothPairFlip j)
  invFun n := fun j => n (a03BothPairFlip j)
  left_inv n := by funext j; simp
  right_inv n := by funext j; simp

theorem a03BothPairFlip_product (n : Fin 4 → ℕ) :
    positiveQuadProduct (a03BothPairFlipIndices n) = positiveQuadProduct n := by
  simp [positiveQuadProduct, a03BothPairFlipIndices, a03BothPairFlip]
  ring

theorem a03BothPairFlip_diagonal_relation (u v : ℕ) (n : Fin 4 → ℕ) :
    diagonalQuadRelation u v (a03BothPairFlipIndices n) ↔ diagonalQuadRelation u v n := by
  change (u*(n 1+1)*(n 0+1) = v*(n 3+1)*(n 2+1)) ↔
    (u*(n 0+1)*(n 1+1) = v*(n 2+1)*(n 3+1))
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem a03BothPairFlip_diagonal_summand (G : ℂ → ℂ) (α : MomentShifts)
    (u v : ℕ) (t : ℝ) (n : Fin 4 → ℕ) :
    bblrDiagonalSummand G (fun j => α (a03BothPairFlip j)) u v t n =
      bblrDiagonalSummand G α u v t (a03BothPairFlipIndices n) := by
  unfold bblrDiagonalSummand
  rw [a03BothPairFlip_product]
  congr 1
  simp [Fin.prod_univ_four, a03BothPairFlipIndices, a03BothPairFlip]
  ring

theorem bblrDiagonalTerm_both_pair_flip (G : ℂ → ℂ) (α : MomentShifts)
    (u v : ℕ) (t : ℝ) :
    bblrDiagonalTerm G (fun j => α (a03BothPairFlip j)) u v t =
      bblrDiagonalTerm G α u v t := by
  unfold bblrDiagonalTerm
  rw [← (a03BothPairFlipIndices.tsum_eq (fun n =>
    if diagonalQuadRelation u v n then bblrDiagonalSummand G α u v t n else 0))]
  apply tsum_congr
  intro n
  rw [a03BothPairFlip_diagonal_relation, ← a03BothPairFlip_diagonal_summand]

def a03DualTermPartner (j : Fin 6) : Fin 6 := ![1, 0, 5, 3, 4, 2] j

@[simp] theorem a03DualTermPartner_involutive (j : Fin 6) :
    a03DualTermPartner (a03DualTermPartner j) = j := by
  fin_cases j <;> norm_num [a03DualTermPartner]

theorem bblrDiagonalTerm_dual_six_orientation (G : ℂ → ℂ) (α : MomentShifts)
    (u v : ℕ) (t : ℝ) (j : Fin 6) :
    bblrDiagonalTerm G (bblrSixShifts (bblrSixShifts α 1) j) u v t =
      bblrDiagonalTerm G (bblrSixShifts α (a03DualTermPartner j)) u v t := by
  fin_cases j
  · simp [bblrSixShifts, a03DualTermPartner]
  · have he : (![α 0, α 1, α 2, α 3] : MomentShifts) = α := by
      funext i
      fin_cases i <;> rfl
    simp [bblrSixShifts, a03DualTermPartner, he]
  · simp [bblrSixShifts, a03DualTermPartner]
  · have h := bblrDiagonalTerm_both_pair_flip G (bblrSixShifts α 3) u v t
    convert h using 1 <;> congr 2
    funext i
    fin_cases i <;> simp [bblrSixShifts, a03BothPairFlip]
  · have h := bblrDiagonalTerm_both_pair_flip G (bblrSixShifts α 4) u v t
    convert h using 1 <;> congr 2
    funext i
    fin_cases i <;> simp [bblrSixShifts, a03BothPairFlip]
  · simp [bblrSixShifts, a03DualTermPartner]

theorem bblrSixPhaseExponents_dual_partner (α : MomentShifts) (j : Fin 6) :
    bblrSixPhaseExponents α 1 + bblrSixPhaseExponents (bblrSixShifts α 1) j =
      bblrSixPhaseExponents α (a03DualTermPartner j) := by
  fin_cases j <;> simp [bblrSixPhaseExponents, bblrSixShifts, a03DualTermPartner] <;> ring

theorem bblr_dual_leading_phase_six_orientation (G : ℂ → ℂ) (α : MomentShifts)
    (u v : ℕ) {t : ℝ} (ht : 0 < t) (j : Fin 6) :
    (t/(2*Real.pi) : ℂ)^(bblrSixPhaseExponents α 1)*
      (t/(2*Real.pi) : ℂ)^(bblrSixPhaseExponents (bblrSixShifts α 1) j)*
      bblrDiagonalTerm G (bblrSixShifts (bblrSixShifts α 1) j) u v t =
    (t/(2*Real.pi) : ℂ)^(bblrSixPhaseExponents α (a03DualTermPartner j))*
      bblrDiagonalTerm G (bblrSixShifts α (a03DualTermPartner j)) u v t := by
  have hn : (t/(2*Real.pi) : ℂ) ≠ 0 := by
    exact div_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne')
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'))
  rw [← Complex.cpow_add _ _ hn, bblrSixPhaseExponents_dual_partner,
    bblrDiagonalTerm_dual_six_orientation]

end
end SixthMoment.Source
