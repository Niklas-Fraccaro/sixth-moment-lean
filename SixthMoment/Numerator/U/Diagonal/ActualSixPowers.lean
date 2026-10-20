import SixthMoment.Numerator.U.Diagonal.ActualDiagonalMellin


namespace SixthMoment
open Complex
open scoped BigOperators
open Classical
noncomputable section
set_option maxHeartbeats 0

theorem actualShiftedPower_mul (a : ℂ) (m n : ℕ) :
    shiftedPowerArithmetic a (m*n) = shiftedPowerArithmetic a m*shiftedPowerArithmetic a n := by
  by_cases hm : m=0
  · simp [hm]
  by_cases hn : n=0
  · simp [hn]
  rw [shiftedPowerArithmetic_apply a (mul_ne_zero hm hn),
    shiftedPowerArithmetic_apply a hm, shiftedPowerArithmetic_apply a hn]
  simpa only [Nat.cast_mul] using Complex.natCast_mul_natCast_cpow m n (-a)

theorem actualShiftedPower_add (a b : ℂ) (n : ℕ) :
    shiftedPowerArithmetic (a+b) n = shiftedPowerArithmetic a n*shiftedPowerArithmetic b n := by
  by_cases hn : n=0
  · simp [hn]
  simp only [shiftedPowerArithmetic_apply _ hn, neg_add]
  rw [Complex.cpow_add _ _ (by exact_mod_cast hn)]

theorem literalTripleDirichletTerm_const (c : ℂ) (x : ℕ × ℕ × ℕ) :
    literalTripleDirichletTerm (fun _ => c) x =
      shiftedPowerArithmetic c (x.1*(x.2.1*x.2.2)) := by
  simp only [literalTripleDirichletTerm, actualShiftedPower_mul]
  ring

theorem literalTripleDirichletTerm_add_const (a : Fin 3 → ℂ) (c : ℂ)
    (x : ℕ × ℕ × ℕ) :
    literalTripleDirichletTerm (fun i => a i+c) x =
      literalTripleDirichletTerm a x*shiftedPowerArithmetic c (x.1*(x.2.1*x.2.2)) := by
  simp only [literalTripleDirichletTerm, actualShiftedPower_add, actualShiftedPower_mul]
  ring

theorem literalDiagonalSixTerm_eq_half_powers (a b : Fin 3 → ℂ) (x : DiagonalSixIndices) :
    literalDiagonalSixTerm a b x =
      literalTripleDirichletTerm (fun i => a i+(1/2:ℂ)) x.val.1*
        literalTripleDirichletTerm (fun i => b i+(1/2:ℂ)) x.val.2 := by
  rw [literalTripleDirichletTerm_add_const, literalTripleDirichletTerm_add_const]
  rw [← x.property.1]
  have h : shiftedPowerArithmetic (1/2:ℂ) (x.val.1.1*(x.val.1.2.1*x.val.1.2.2))*
      shiftedPowerArithmetic (1/2:ℂ) (x.val.1.1*(x.val.1.2.1*x.val.1.2.2)) =
      shiftedPowerArithmetic 1 (x.val.1.1*(x.val.1.2.1*x.val.1.2.2)) := by
    rw [← actualShiftedPower_add]
    norm_num
  unfold literalDiagonalSixTerm
  calc
    _ = literalTripleDirichletTerm a x.val.1*literalTripleDirichletTerm b x.val.2*
        (shiftedPowerArithmetic (1/2:ℂ) (x.val.1.1*(x.val.1.2.1*x.val.1.2.2))*
          shiftedPowerArithmetic (1/2:ℂ) (x.val.1.1*(x.val.1.2.1*x.val.1.2.2))) := by rw [h]
    _ = _ := by ring

theorem diagonalSixIndices_components_ne_zero (x : DiagonalSixIndices) :
    x.val.1.1 ≠ 0 ∧ x.val.1.2.1 ≠ 0 ∧ x.val.1.2.2 ≠ 0 ∧
      x.val.2.1 ≠ 0 ∧ x.val.2.2.1 ≠ 0 ∧ x.val.2.2.2 ≠ 0 := by
  have hl := x.property.2
  have hr : x.val.2.1*(x.val.2.2.1*x.val.2.2.2) ≠ 0 := by rwa [← x.property.1]
  simp only [mul_ne_zero_iff] at hl hr
  exact ⟨hl.1,hl.2.1,hl.2.2,hr.1,hr.2.1,hr.2.2⟩

def diagonalSixQuad (x : DiagonalSixIndices) : Fin 4 → ℕ :=
  ![x.val.1.2.1-1,x.val.1.2.2-1,x.val.2.2.1-1,x.val.2.2.2-1]

theorem diagonalSixQuad_positive_values (x : DiagonalSixIndices) :
    (diagonalSixQuad x 0+1=x.val.1.2.1) ∧
    (diagonalSixQuad x 1+1=x.val.1.2.2) ∧
    (diagonalSixQuad x 2+1=x.val.2.2.1) ∧
    (diagonalSixQuad x 3+1=x.val.2.2.2) := by
  obtain ⟨_,h1,h2,_,h3,h4⟩ := diagonalSixIndices_components_ne_zero x
  simp only [diagonalSixQuad, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  exact ⟨Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h1),
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h2),
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h3),
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h4)⟩

theorem diagonalSixQuad_source_relation (x : DiagonalSixIndices) :
    Source.diagonalQuadRelation x.val.1.1 x.val.2.1 (diagonalSixQuad x) := by
  obtain ⟨h0,h1,h2,h3⟩ := diagonalSixQuad_positive_values x
  unfold Source.diagonalQuadRelation
  rw [h0,h1,h2,h3]
  simpa only [mul_assoc] using x.property.1

theorem literalDiagonalSixTerm_eq_sourceDirichlet (α : MomentShifts) (u v z : ℂ)
    (x : DiagonalSixIndices) :
    literalDiagonalSixTerm (polarMellinLeftTriple α u z) (polarMellinRightTriple α v z) x =
      shiftedPowerArithmetic u x.val.1.1*shiftedPowerArithmetic v x.val.2.1*
        actualDiagonalQuadDirichletTerm α (diagonalSixQuad x) z/
          ((x.val.1.1*x.val.2.1:ℕ):ℂ)^(1/2:ℂ) := by
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := diagonalSixIndices_components_ne_zero x
  obtain ⟨hq0,hq1,hq2,hq3⟩ := diagonalSixQuad_positive_values x
  rw [literalDiagonalSixTerm_eq_half_powers]
  change
    (shiftedPowerArithmetic (u+(1/2:ℂ)) x.val.1.1*
      shiftedPowerArithmetic (z+α 0+(1/2:ℂ)) x.val.1.2.1*
        shiftedPowerArithmetic (z+α 1+(1/2:ℂ)) x.val.1.2.2)*
    (shiftedPowerArithmetic (v+(1/2:ℂ)) x.val.2.1*
      shiftedPowerArithmetic (z+α 2+(1/2:ℂ)) x.val.2.2.1*
        shiftedPowerArithmetic (z+α 3+(1/2:ℂ)) x.val.2.2.2) = _
  rw [actualShiftedPower_add u (1/2:ℂ), actualShiftedPower_add v (1/2:ℂ)]
  have he (j : Fin 4) : z+α j+(1/2:ℂ) = (1/2:ℂ)+α j+z := by ring
  simp_rw [he]
  have hab : ((x.val.1.1*x.val.2.1:ℕ):ℂ)^(1/2:ℂ) =
      (x.val.1.1:ℂ)^(1/2:ℂ)*(x.val.2.1:ℂ)^(1/2:ℂ) := by
    simpa only [Nat.cast_mul] using
      Complex.natCast_mul_natCast_cpow x.val.1.1 x.val.2.1 (1/2:ℂ)
  unfold actualDiagonalQuadDirichletTerm
  rw [Fin.prod_univ_four, hab]
  have hc (j : Fin 4) (k : ℕ) (hk : diagonalSixQuad x j+1=k) :
      (diagonalSixQuad x j+1:ℂ)=(k:ℂ) := by exact_mod_cast hk
  rw [hc 0 _ hq0,hc 1 _ hq1,hc 2 _ hq2,hc 3 _ hq3]
  simp only [shiftedPowerArithmetic, ArithmeticFunction.coe_mk, h0,h1,h2,h3,h4,h5,
    ite_false, Complex.cpow_neg, div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

end
end SixthMoment
