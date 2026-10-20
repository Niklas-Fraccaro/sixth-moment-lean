import SixthMoment.Numerator.U.Reconstruction.RectangularQuadraticReindex


namespace SixthMoment
open Source
open Classical
open scoped BigOperators
noncomputable section

def rectangularNearLeftProduct (n : Fin 7 → ℕ) : ℝ :=
  (n 0 : ℝ)*n 2*n 3

def rectangularNearRightProduct (n : Fin 7 → ℕ) : ℝ :=
  (n 1 : ℝ)*n 4*n 5

def rectangularNearRelation (η : ℝ) (n : Fin 7 → ℕ) : Prop :=
  (n 6 : ℝ) ≤ η*Real.sqrt ((n 0 : ℝ)*n 1*n 2*n 3*n 4*n 5)

theorem rectangular_near_product_comparable {A B η : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hη : η ≤ 1/2)
    (hne : |A-B| ≤ η*Real.sqrt (A*B)) : B ≤ 4*A := by
  have hs : Real.sqrt (A*B) ≤ A+B := Real.sqrt_le_iff.mpr
    ⟨by positivity, by nlinarith [sq_nonneg A, sq_nonneg B]⟩
  have hηs : η*Real.sqrt (A*B) ≤ (1/2 : ℝ)*Real.sqrt (A*B) :=
    mul_le_mul_of_nonneg_right hη (Real.sqrt_nonneg _)
  have hs' : (1/2 : ℝ)*Real.sqrt (A*B) ≤ (A+B)/2 := by linarith
  have hab := neg_le_abs (A-B)
  linarith

theorem rectangular_near_product_sqrt_le {A B η : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hη : η ≤ 1/2)
    (hne : |A-B| ≤ η*Real.sqrt (A*B)) : Real.sqrt (A*B) ≤ 2*A := by
  have hBA := rectangular_near_product_comparable hA hB hη hne
  have hmul := mul_le_mul_of_nonneg_left hBA hA.le
  apply Real.sqrt_le_iff.mpr
  exact ⟨by positivity, by nlinarith⟩

theorem rectangular_near_gap_lt_one {A B η X h : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hη0 : 0 ≤ η) (hη : η ≤ 1/2)
    (hAX : A ≤ X) (hsmall : 2*η*X < 1)
    (hrel : |A-B| = h) (hne : h ≤ η*Real.sqrt (A*B)) : h < 1 := by
  have hs := rectangular_near_product_sqrt_le hA hB hη (by simpa [hrel] using hne)
  have hsη := mul_le_mul_of_nonneg_left hs hη0
  have hX := mul_le_mul_of_nonneg_left hAX (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hη0)
  nlinarith

theorem rectangular_near_tuple_mass (n : Fin 7 → ℕ) :
    (n 0 : ℝ)*n 1*n 2*n 3*n 4*n 5 =
      rectangularNearLeftProduct n*rectangularNearRightProduct n := by
  unfold rectangularNearLeftProduct rectangularNearRightProduct
  ring

theorem rectangular_signed_relation_abs_gap (positive : Bool) (n : Fin 7 → ℕ)
    (hrel : signedQuadraticRelation positive n) :
    |rectangularNearLeftProduct n-rectangularNearRightProduct n| = (n 6 : ℝ) := by
  have hreal : rectangularNearLeftProduct n-rectangularNearRightProduct n =
      if positive then (n 6 : ℝ) else -(n 6 : ℝ) := by
    unfold rectangularNearLeftProduct rectangularNearRightProduct
    unfold signedQuadraticRelation at hrel
    cases positive <;> simp only [Bool.false_eq_true, ite_false, ite_true] at *
    all_goals exact_mod_cast hrel
  rw [hreal]
  cases positive <;> simp

theorem rectangular_near_double_m_unit_excluded (positive : Bool)
    (n : Fin 7 → ℕ) {η X : ℝ}
    (hη0 : 0 ≤ η) (hη : η ≤ 1/2) (hsmall : 2*η*X < 1)
    (ha : 0 < n 0) (haX : (n 0 : ℝ) ≤ X) (hh : 0 < n 6)
    (hm₁ : n 2 = 1) (hm₂ : n 3 = 1)
    (hrel : signedQuadraticRelation positive n) : ¬ rectangularNearRelation η n := by
  intro hnear
  have hA : 0 < rectangularNearLeftProduct n := by
    simp [rectangularNearLeftProduct, hm₁, hm₂]
    exact_mod_cast ha
  have hB : 0 ≤ rectangularNearRightProduct n := by
    unfold rectangularNearRightProduct
    positivity
  have hAX : rectangularNearLeftProduct n ≤ X := by
    simpa [rectangularNearLeftProduct, hm₁, hm₂] using haX
  have hgap := rectangular_signed_relation_abs_gap positive n hrel
  have hne : (n 6 : ℝ) ≤ η*Real.sqrt
      (rectangularNearLeftProduct n*rectangularNearRightProduct n) := by
    simpa [rectangularNearRelation, rectangular_near_tuple_mass] using hnear
  have hlt := rectangular_near_gap_lt_one hA hB hη0 hη hAX hsmall hgap hne
  have hh1 : (1:ℝ) ≤ n 6 := by exact_mod_cast Nat.succ_le_iff.mpr hh
  linarith

theorem rectangular_near_double_n_unit_excluded (positive : Bool)
    (n : Fin 7 → ℕ) {η X : ℝ}
    (hη0 : 0 ≤ η) (hη : η ≤ 1/2) (hsmall : 2*η*X < 1)
    (hb : 0 < n 1) (hbX : (n 1 : ℝ) ≤ X) (hh : 0 < n 6)
    (hn₁ : n 4 = 1) (hn₂ : n 5 = 1)
    (hrel : signedQuadraticRelation positive n) : ¬ rectangularNearRelation η n := by
  intro hnear
  have hA : 0 < rectangularNearRightProduct n := by
    simp [rectangularNearRightProduct, hn₁, hn₂]
    exact_mod_cast hb
  have hB : 0 ≤ rectangularNearLeftProduct n := by
    unfold rectangularNearLeftProduct
    positivity
  have hAX : rectangularNearRightProduct n ≤ X := by
    simpa [rectangularNearRightProduct, hn₁, hn₂] using hbX
  have hgap : |rectangularNearRightProduct n-rectangularNearLeftProduct n| = (n 6 : ℝ) := by
    rw [abs_sub_comm]
    exact rectangular_signed_relation_abs_gap positive n hrel
  have hne : (n 6 : ℝ) ≤ η*Real.sqrt
      (rectangularNearRightProduct n*rectangularNearLeftProduct n) := by
    simpa [rectangularNearRelation, rectangular_near_tuple_mass, mul_comm] using hnear
  have hlt := rectangular_near_gap_lt_one hA hB hη0 hη hAX hsmall hgap hne
  have hh1 : (1:ℝ) ≤ n 6 := by exact_mod_cast Nat.succ_le_iff.mpr hh
  linarith

theorem rectangular_near_double_unit_gap_zero (positive : Bool)
    (n : Fin 7 → ℕ) {η X : ℝ}
    (hη0 : 0 ≤ η) (hη : η ≤ 1/2) (hsmall : 2*η*X < 1)
    (ha : 0 < n 0) (hb : 0 < n 1)
    (hunit : (n 2 = 1 ∧ n 3 = 1 ∧ (n 0 : ℝ) ≤ X) ∨
      (n 4 = 1 ∧ n 5 = 1 ∧ (n 1 : ℝ) ≤ X))
    (hrel : signedQuadraticRelation positive n) (hne : rectangularNearRelation η n) :
    n 6 = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hh
  rcases hunit with ⟨hm₁, hm₂, haX⟩ | ⟨hn₁, hn₂, hbX⟩
  · exact rectangular_near_double_m_unit_excluded positive n hη0 hη hsmall
      ha haX hh hm₁ hm₂ hrel hne
  · exact rectangular_near_double_n_unit_excluded positive n hη0 hη hsmall
      hb hbX hh hn₁ hn₂ hrel hne

theorem rectangular_near_double_unit_gap_far (positive : Bool)
    (n : Fin 7 → ℕ) {η X : ℝ}
    (hη0 : 0 ≤ η) (hη : η ≤ 1/2) (hsmall : 2*η*X < 1)
    (ha : 0 < n 0) (hb : 0 < n 1) (hh : 0 < n 6)
    (hunit : (n 2 = 1 ∧ n 3 = 1 ∧ (n 0 : ℝ) ≤ X) ∨
      (n 4 = 1 ∧ n 5 = 1 ∧ (n 1 : ℝ) ≤ X))
    (hrel : signedQuadraticRelation positive n) :
    η*Real.sqrt ((n 0 : ℝ)*n 1*n 2*n 3*n 4*n 5) < (n 6 : ℝ) := by
  apply lt_of_not_ge
  intro hne
  have hz := rectangular_near_double_unit_gap_zero positive n hη0 hη hsmall ha hb hunit hrel hne
  omega

theorem rectangular_AFE_double_m_unit_near_excluded (positive : Bool)
    (a b : ℕ) (n : Fin 4 → ℕ) {η X : ℝ}
    (hη0 : 0 ≤ η) (hη : η ≤ 1/2) (hsmall : 2*η*X < 1)
    (ha : 0 < a) (haX : (a : ℝ) ≤ X) (hm₁ : n 0 = 0) (hm₂ : n 1 = 0)
    (hselected : if positive then rectangularPositiveQuadGap a b n
      else rectangularNegativeQuadGap a b n) :
    ¬ rectangularNearRelation η
      (rectangularAFESourceTuple a b n (rectangularAFEGap positive a b n)) := by
  apply rectangular_near_double_m_unit_excluded positive _ hη0 hη hsmall
  · simpa [rectangularAFESourceTuple] using ha
  · simpa [rectangularAFESourceTuple] using haX
  · simpa [rectangularAFESourceTuple] using rectangular_AFE_gap_pos positive a b n hselected
  · simp [rectangularAFESourceTuple, hm₁]
  · simp [rectangularAFESourceTuple, hm₂]
  · exact rectangular_AFE_gap_source_relation positive a b n hselected

theorem rectangular_AFE_double_n_unit_near_excluded (positive : Bool)
    (a b : ℕ) (n : Fin 4 → ℕ) {η X : ℝ}
    (hη0 : 0 ≤ η) (hη : η ≤ 1/2) (hsmall : 2*η*X < 1)
    (hb : 0 < b) (hbX : (b : ℝ) ≤ X) (hn₁ : n 2 = 0) (hn₂ : n 3 = 0)
    (hselected : if positive then rectangularPositiveQuadGap a b n
      else rectangularNegativeQuadGap a b n) :
    ¬ rectangularNearRelation η
      (rectangularAFESourceTuple a b n (rectangularAFEGap positive a b n)) := by
  apply rectangular_near_double_n_unit_excluded positive _ hη0 hη hsmall
  · simpa [rectangularAFESourceTuple] using hb
  · simpa [rectangularAFESourceTuple] using hbX
  · simpa [rectangularAFESourceTuple] using rectangular_AFE_gap_pos positive a b n hselected
  · simp [rectangularAFESourceTuple, hn₁]
  · simp [rectangularAFESourceTuple, hn₂]
  · exact rectangular_AFE_gap_source_relation positive a b n hselected

def rectangularNearDoubleUnitSelection (η X : ℝ) (n : Fin 7 → ℕ) : Prop :=
  rectangularNearRelation η n ∧
    ((n 2 = 1 ∧ n 3 = 1 ∧ (n 0 : ℝ) ≤ X) ∨
      (n 4 = 1 ∧ n 5 = 1 ∧ (n 1 : ℝ) ≤ X))

theorem rectangular_near_double_unit_source_sum_zero (positive : Bool)
    (q : QuadraticScales) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) {η X : ℝ}
    (hη0 : 0 ≤ η) (hη : η ≤ 1/2) (hsmall : 2*η*X < 1) :
    (∑ n ∈ quadraticIndexSet q,
      if signedQuadraticRelation positive n ∧ rectangularNearDoubleUnitSelection η X n
        then quadraticSummand q α β W n else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hselect : signedQuadraticRelation positive n ∧ rectangularNearDoubleUnitSelection η X n
  · have hi (j : Fin 7) : 0 < n j := by
      have hj := (Fintype.mem_piFinset.mp hn) j
      exact Nat.succ_le_iff.mp (Finset.mem_Icc.mp hj).1
    have hz := rectangular_near_double_unit_gap_zero positive n hη0 hη hsmall
      (hi 0) (hi 1) hselect.2.2 hselect.1 hselect.2.1
    have hp := hi 6
    omega
  · simp [hselect]

end
end SixthMoment
