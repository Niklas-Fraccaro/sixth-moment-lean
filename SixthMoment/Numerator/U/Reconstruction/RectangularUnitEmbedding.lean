import SixthMoment.Arithmetic.QuadraticDivisor.ComplexWeights
import SixthMoment.Numerator.U.Reconstruction.RectangularSmoothAFE


namespace SixthMoment
open Complex Source Set MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def rectangularUnitFactor (b : Bool) : ℕ := if b then 2 else 1

def rectangularUnitMFactor (f : Fin 4 → Bool) : ℕ :=
  rectangularUnitFactor (f 0)*rectangularUnitFactor (f 1)

def rectangularUnitNFactor (f : Fin 4 → Bool) : ℕ :=
  rectangularUnitFactor (f 2)*rectangularUnitFactor (f 3)

def rectangularUnitFactors (f : Fin 4 → Bool) : Fin 7 → ℕ :=
  ![rectangularUnitNFactor f, rectangularUnitMFactor f,
    rectangularUnitFactor (f 0), rectangularUnitFactor (f 1),
    rectangularUnitFactor (f 2), rectangularUnitFactor (f 3),
    rectangularUnitMFactor f*rectangularUnitNFactor f]

def rectangularUnitTuple (f : Fin 4 → Bool) (n : Fin 7 → ℕ) : Fin 7 → ℕ :=
  fun j => rectangularUnitFactors f j*n j

def rectangularUnitInverse (f : Fin 4 → Bool) (n : Fin 7 → ℕ) : Fin 7 → ℕ :=
  fun j => n j/rectangularUnitFactors f j

def rectangularUnitScales (f : Fin 4 → Bool) (q : QuadraticScales) : QuadraticScales where
  A := rectangularUnitNFactor f*q.A
  B := rectangularUnitMFactor f*q.B
  M₁ := rectangularUnitFactor (f 0)*q.M₁
  M₂ := rectangularUnitFactor (f 1)*q.M₂
  N₁ := rectangularUnitFactor (f 2)*q.N₁
  N₂ := rectangularUnitFactor (f 3)*q.N₂
  H := (rectangularUnitMFactor f*rectangularUnitNFactor f)*q.H

def rectangularUnitCoefficient (c : ℕ) (α : ℕ → ℂ) (n : ℕ) : ℂ :=
  if c ∣ n then α (n/c) else 0

theorem rectangular_unit_factor_bounds (b : Bool) :
    1 ≤ rectangularUnitFactor b ∧ rectangularUnitFactor b ≤ 2 := by
  cases b <;> norm_num [rectangularUnitFactor]

theorem rectangular_unit_factor_pos (b : Bool) : 0 < rectangularUnitFactor b :=
  lt_of_lt_of_le Nat.zero_lt_one (rectangular_unit_factor_bounds b).1

theorem rectangular_unit_m_factor_power (f : Fin 4 → Bool) :
    rectangularUnitMFactor f = 2^((if f 0 then 1 else 0)+(if f 1 then 1 else 0)) := by
  cases h0 : f 0 <;> cases h1 : f 1 <;>
    norm_num [rectangularUnitMFactor, rectangularUnitFactor, h0, h1]

theorem rectangular_unit_n_factor_power (f : Fin 4 → Bool) :
    rectangularUnitNFactor f = 2^((if f 2 then 1 else 0)+(if f 3 then 1 else 0)) := by
  cases h2 : f 2 <;> cases h3 : f 3 <;>
    norm_num [rectangularUnitNFactor, rectangularUnitFactor, h2, h3]

theorem rectangular_unit_product_factors_bounds (f : Fin 4 → Bool) :
    1 ≤ rectangularUnitMFactor f ∧ rectangularUnitMFactor f ≤ 4 ∧
      1 ≤ rectangularUnitNFactor f ∧ rectangularUnitNFactor f ≤ 4 := by
  unfold rectangularUnitMFactor rectangularUnitNFactor
  have h0 := rectangular_unit_factor_bounds (f 0)
  have h1 := rectangular_unit_factor_bounds (f 1)
  have h2 := rectangular_unit_factor_bounds (f 2)
  have h3 := rectangular_unit_factor_bounds (f 3)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Nat.mul_le_mul h0.1 h1.1
  · exact Nat.mul_le_mul h0.2 h1.2
  · exact Nat.mul_le_mul h2.1 h3.1
  · exact Nat.mul_le_mul h2.2 h3.2

theorem rectangular_unit_factors_pos (f : Fin 4 → Bool) (j : Fin 7) :
    0 < rectangularUnitFactors f j := by
  have h := rectangular_unit_product_factors_bounds f
  have hm : 0 < rectangularUnitMFactor f := lt_of_lt_of_le Nat.zero_lt_one h.1
  have hn : 0 < rectangularUnitNFactor f := lt_of_lt_of_le Nat.zero_lt_one h.2.2.1
  fin_cases j <;> simp [rectangularUnitFactors]
  all_goals first | exact rectangular_unit_factor_pos _ | exact hm | exact hn | exact ⟨hm, hn⟩

theorem rectangular_unit_factors_bounds (f : Fin 4 → Bool) (j : Fin 7) :
    1 ≤ rectangularUnitFactors f j ∧ rectangularUnitFactors f j ≤ 16 := by
  have h := rectangular_unit_product_factors_bounds f
  have h0 := rectangular_unit_factor_bounds (f 0)
  have h1 := rectangular_unit_factor_bounds (f 1)
  have h2 := rectangular_unit_factor_bounds (f 2)
  have h3 := rectangular_unit_factor_bounds (f 3)
  have hmn : 1 ≤ rectangularUnitMFactor f*rectangularUnitNFactor f ∧
      rectangularUnitMFactor f*rectangularUnitNFactor f ≤ 16 :=
    ⟨Nat.mul_le_mul h.1 h.2.2.1, Nat.mul_le_mul h.2.1 h.2.2.2⟩
  fin_cases j <;> simp [rectangularUnitFactors]
  all_goals omega

theorem rectangular_unit_scales_size (f : Fin 4 → Bool) (q : QuadraticScales) (j : Fin 7) :
    (rectangularUnitScales f q).size j = rectangularUnitFactors f j*q.size j := by
  fin_cases j <;> simp [rectangularUnitScales, QuadraticScales.size, rectangularUnitFactors]

theorem rectangular_unit_coefficient_on_image {c : ℕ} (hc : 0 < c) (α : ℕ → ℂ) (n : ℕ) :
    rectangularUnitCoefficient c α (c*n) = α n := by
  simp [rectangularUnitCoefficient, Nat.mul_div_right _ hc]

theorem rectangular_unit_coefficient_dvd {c n : ℕ} (α : ℕ → ℂ)
    (hn : rectangularUnitCoefficient c α n ≠ 0) : c ∣ n := by
  by_contra h
  simp [rectangularUnitCoefficient, h] at hn

theorem rectangular_unit_coefficient_bound {c : ℕ} (α : ℕ → ℂ) {L : ℝ}
    (hL : 0 ≤ L) (hα : ∀ n, ‖α n‖ ≤ L) (n : ℕ) :
    ‖rectangularUnitCoefficient c α n‖ ≤ L := by
  unfold rectangularUnitCoefficient
  split
  · exact hα _
  · simpa using hL

theorem rectangular_unit_coefficient_power_bound {c : ℕ} (hc : 0 < c)
    (α : ℕ → ℂ) {K A ε : ℝ} (hK : 0 ≤ K) (hA : 0 < A) (hε : 0 ≤ ε)
    (hα : ∀ n, ‖α n‖ ≤ K*A^ε) (n : ℕ) :
    ‖rectangularUnitCoefficient c α n‖ ≤ K*((c : ℝ)*A)^ε := by
  have hL : 0 ≤ K*A^ε := mul_nonneg hK (Real.rpow_nonneg hA.le _)
  have hc1 : (1:ℝ) ≤ c := by exact_mod_cast Nat.succ_le_iff.mpr hc
  have hAc : A ≤ (c : ℝ)*A := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 hA.le
  exact (rectangular_unit_coefficient_bound α hL hα n).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hA.le hAc hε) hK)

theorem rectangular_unit_tuple_injective (f : Fin 4 → Bool) :
    Function.Injective (rectangularUnitTuple f) := by
  intro n m h
  ext j
  have hj := congrFun h j
  exact Nat.eq_of_mul_eq_mul_left (rectangular_unit_factors_pos f j) hj

theorem rectangular_unit_tuple_inverse_left (f : Fin 4 → Bool) (n : Fin 7 → ℕ) :
    rectangularUnitInverse f (rectangularUnitTuple f n) = n := by
  ext j
  exact Nat.mul_div_right _ (rectangular_unit_factors_pos f j)

theorem rectangular_unit_tuple_inverse_right (f : Fin 4 → Bool) (n : Fin 7 → ℕ)
    (hn : ∀ j, rectangularUnitFactors f j ∣ n j) :
    rectangularUnitTuple f (rectangularUnitInverse f n) = n := by
  ext j
  exact Nat.mul_div_cancel' (hn j)

theorem rectangular_unit_relation_lhs (f : Fin 4 → Bool) (n : Fin 7 → ℕ) :
    ((rectangularUnitTuple f n 0 : ℤ)*rectangularUnitTuple f n 2*rectangularUnitTuple f n 3-
      (rectangularUnitTuple f n 1 : ℤ)*rectangularUnitTuple f n 4*rectangularUnitTuple f n 5) =
      (rectangularUnitMFactor f*rectangularUnitNFactor f : ℕ)*
        ((n 0 : ℤ)*n 2*n 3-(n 1 : ℤ)*n 4*n 5) := by
  simp [rectangularUnitTuple, rectangularUnitFactors, rectangularUnitMFactor, rectangularUnitNFactor]
  ring

theorem rectangular_unit_signed_relation (f : Fin 4 → Bool) (positive : Bool) (n : Fin 7 → ℕ) :
    signedQuadraticRelation positive (rectangularUnitTuple f n) ↔
      signedQuadraticRelation positive n := by
  have hc : (rectangularUnitMFactor f*rectangularUnitNFactor f : ℕ) ≠ 0 :=
    Nat.ne_of_gt (rectangular_unit_factors_pos f 6)
  have hcz : ((rectangularUnitMFactor f*rectangularUnitNFactor f : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hc
  have hh : (rectangularUnitTuple f n 6 : ℤ) =
      ((rectangularUnitMFactor f*rectangularUnitNFactor f : ℕ) : ℤ)*n 6 := by
    simp [rectangularUnitTuple, rectangularUnitFactors]
  unfold signedQuadraticRelation
  rw [rectangular_unit_relation_lhs, hh]
  cases positive
  · simp only [Bool.false_eq_true, ite_false, ← mul_neg]
    exact mul_right_inj' hcz
  · simp only [ite_true]
    exact mul_right_inj' hcz

theorem rectangular_unit_scaled_index_mem {c n : ℕ} (hc : 0 < c) {x : ℝ} (hx : 0 < x) :
    c*n ∈ Finset.Icc 1 ⌊2*((c : ℝ)*x)⌋₊ ↔ n ∈ Finset.Icc 1 ⌊2*x⌋₊ := by
  have hcr : (0:ℝ) < c := by exact_mod_cast hc
  simp only [Finset.mem_Icc]
  rw [Nat.le_floor_iff (by positivity), Nat.le_floor_iff (by positivity), Nat.cast_mul]
  constructor
  · intro ⟨hl, hu⟩
    refine ⟨?_, ?_⟩
    · apply Nat.one_le_iff_ne_zero.mpr
      intro hn
      simp [hn] at hl
    · apply (mul_le_mul_iff_left₀ hcr).mp
      nlinarith
  · intro ⟨hl, hu⟩
    refine ⟨Nat.mul_le_mul (Nat.succ_le_iff.mpr hc) hl, ?_⟩
    nlinarith

theorem rectangular_unit_index_mem (f : Fin 4 → Bool) (q : QuadraticScales)
    (hq : ∀ j, 0 < q.size j) (n : Fin 7 → ℕ) :
    rectangularUnitTuple f n ∈ quadraticIndexSet (rectangularUnitScales f q) ↔
      n ∈ quadraticIndexSet q := by
  simp only [quadraticIndexSet, Fintype.mem_piFinset]
  apply forall_congr'
  intro j
  rw [rectangular_unit_scales_size]
  exact rectangular_unit_scaled_index_mem (rectangular_unit_factors_pos f j) (hq j)

theorem rectangular_unit_coefficient_support {c : ℕ} (_hc : 0 < c)
    (α : ℕ → ℂ) (A : ℝ) (hα : ∀ n : ℕ, (n : ℝ) ∉ Icc A (2*A) → α n = 0) :
    ∀ n : ℕ, (n : ℝ) ∉ Icc ((c : ℝ)*A) (2*((c : ℝ)*A)) →
      rectangularUnitCoefficient c α n = 0 := by
  intro n hn
  unfold rectangularUnitCoefficient
  split
  next hd =>
    apply hα
    intro hm
    apply hn
    have he : (n : ℝ) = (c : ℝ)*(n/c : ℕ) := by
      exact_mod_cast (Nat.mul_div_cancel' hd).symm
    rw [he]
    have hc0 : (0:ℝ) ≤ c := Nat.cast_nonneg _
    constructor
    · exact mul_le_mul_of_nonneg_left hm.1 hc0
    · nlinarith [mul_le_mul_of_nonneg_left hm.2 hc0]
  next => rfl

theorem rectangular_unit_scales_lower_bound (f : Fin 4 → Bool) (q : QuadraticScales)
    (hA : 1 ≤ q.A) (hB : 1 ≤ q.B) (hH : 1 ≤ q.H)
    (hm1 : if f 0 then q.M₁ = 2/3 else 1 ≤ q.M₁)
    (hm2 : if f 1 then q.M₂ = 2/3 else 1 ≤ q.M₂)
    (hn1 : if f 2 then q.N₁ = 2/3 else 1 ≤ q.N₁)
    (hn2 : if f 3 then q.N₂ = 2/3 else 1 ≤ q.N₂) :
    ∀ j, 1 ≤ (rectangularUnitScales f q).size j := by
  have hb := rectangular_unit_product_factors_bounds f
  have hM : (1:ℝ) ≤ rectangularUnitMFactor f := by exact_mod_cast hb.1
  have hN : (1:ℝ) ≤ rectangularUnitNFactor f := by exact_mod_cast hb.2.2.1
  have hMN : (1:ℝ) ≤ (rectangularUnitMFactor f : ℝ)*(rectangularUnitNFactor f : ℝ) := by
    exact_mod_cast Nat.mul_le_mul hb.1 hb.2.2.1
  have hs (b : Bool) (x : ℝ) (hx : if b then x = 2/3 else 1 ≤ x) :
      1 ≤ (rectangularUnitFactor b : ℝ)*x := by
    cases b with
    | false => simpa [rectangularUnitFactor] using hx
    | true =>
      simp only [ite_true] at hx
      rw [hx]
      norm_num [rectangularUnitFactor]
  intro j
  fin_cases j <;> simp [rectangularUnitScales, QuadraticScales.size]
  · exact one_le_mul_of_one_le_of_one_le hN hA
  · exact one_le_mul_of_one_le_of_one_le hM hB
  · exact hs _ _ hm1
  · exact hs _ _ hm2
  · exact hs _ _ hn1
  · exact hs _ _ hn2
  · exact one_le_mul_of_one_le_of_one_le hMN hH

theorem rectangular_unit_weight_arguments (f : Fin 4 → Bool) (q : QuadraticScales)
    (n : Fin 7 → ℕ) (i : Fin 5) :
    rectangularWeightArguments (rectangularUnitScales f q) (rectangularUnitTuple f n) i =
      rectangularWeightArguments q n i := by
  have hc (j : Fin 7) : ((rectangularUnitFactors f j : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (rectangular_unit_factors_pos f j)
  fin_cases i <;> simp [rectangularWeightArguments, rectangularUnitScales,
    rectangularUnitTuple, rectangularUnitFactors, Nat.cast_mul]
  all_goals first
    | exact mul_div_mul_left _ _ (by simpa [rectangularUnitFactors] using hc 6)
    | exact mul_div_mul_left _ _ (by simpa [rectangularUnitFactors] using hc 2)
    | exact mul_div_mul_left _ _ (by simpa [rectangularUnitFactors] using hc 3)
    | exact mul_div_mul_left _ _ (by simpa [rectangularUnitFactors] using hc 4)
    | exact mul_div_mul_left _ _ (by simpa [rectangularUnitFactors] using hc 5)

theorem rectangular_quadratic_summand_product (q : QuadraticScales)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (n : Fin 7 → ℕ) :
    quadraticSummand q α β W n = α (n 0)*β (n 1)*
      ∏ i : Fin 5, (W i (rectangularWeightArguments q n i) : ℂ) := by
  simp [quadraticSummand, rectangularWeightArguments, Fin.prod_univ_five]
  ring

theorem rectangular_unit_summand_preserved (f : Fin 4 → Bool) (q : QuadraticScales)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (n : Fin 7 → ℕ) :
    quadraticSummand (rectangularUnitScales f q)
      (rectangularUnitCoefficient (rectangularUnitNFactor f) α)
      (rectangularUnitCoefficient (rectangularUnitMFactor f) β) W (rectangularUnitTuple f n) =
      quadraticSummand q α β W n := by
  rw [rectangular_quadratic_summand_product, rectangular_quadratic_summand_product]
  have hM : 0 < rectangularUnitMFactor f := lt_of_lt_of_le Nat.zero_lt_one
    (rectangular_unit_product_factors_bounds f).1
  have hN : 0 < rectangularUnitNFactor f := lt_of_lt_of_le Nat.zero_lt_one
    (rectangular_unit_product_factors_bounds f).2.2.1
  have ha : rectangularUnitTuple f n 0 = rectangularUnitNFactor f*n 0 := by
    simp [rectangularUnitTuple, rectangularUnitFactors]
  have hb : rectangularUnitTuple f n 1 = rectangularUnitMFactor f*n 1 := by
    simp [rectangularUnitTuple, rectangularUnitFactors]
  rw [ha, hb, rectangular_unit_coefficient_on_image hN, rectangular_unit_coefficient_on_image hM]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => by rw [rectangular_unit_weight_arguments])

def rectangularUnitCoordinate (j : Fin 4) : Fin 7 := ⟨j.val+2, by omega⟩
def rectangularUnitWeightCoordinate (j : Fin 4) : Fin 5 := ⟨j.val+1, by omega⟩

theorem rectangular_unit_coordinate_factor (f : Fin 4 → Bool) (j : Fin 4) :
    rectangularUnitFactors f (rectangularUnitCoordinate j) = rectangularUnitFactor (f j) := by
  fin_cases j <;> simp [rectangularUnitFactors, rectangularUnitCoordinate]

theorem rectangular_unit_coordinate_weight_argument (q : QuadraticScales) (n : Fin 7 → ℕ)
    (j : Fin 4) : rectangularWeightArguments q n (rectangularUnitWeightCoordinate j) =
      (n (rectangularUnitCoordinate j) : ℝ)/q.size (rectangularUnitCoordinate j) := by
  fin_cases j <;> simp [rectangularWeightArguments, rectangularUnitWeightCoordinate,
    rectangularUnitCoordinate, QuadraticScales.size]

theorem rectangular_unit_low_variable_dvd (b : Bool) (x : ℝ) (W : ℝ → ℝ)
    (hW : SmoothDyadicWeight W) (hx : b = true → x = 2/3) (n : ℕ)
    (hn : n ∈ Finset.Icc 1 ⌊2*((rectangularUnitFactor b : ℝ)*x)⌋₊)
    (hWn : W ((n : ℝ)/((rectangularUnitFactor b : ℝ)*x)) ≠ 0) :
    rectangularUnitFactor b ∣ n := by
  cases b with
  | false => simp [rectangularUnitFactor]
  | true =>
    have hxx := hx rfl
    have hs : (n : ℝ)/((rectangularUnitFactor true : ℝ)*x) ∈ tsupport W :=
      subset_tsupport W hWn
    have hl := (hW.2 hs).1
    have hu : n ≤ 2 := by
      have hu0 := (Finset.mem_Icc.mp hn).2
      have hu1 : ⌊2*((rectangularUnitFactor true : ℝ)*x)⌋₊ < 3 := by
        apply (Nat.floor_lt (by positivity)).mpr
        norm_num [rectangularUnitFactor, hxx]
      omega
    have hn2 : n = 2 := by
      have hn0 : n ≠ 0 := by
        intro h
        norm_num [rectangularUnitFactor, hxx, h] at hl
      have hn1 : n ≠ 1 := by
        intro h
        norm_num [rectangularUnitFactor, hxx, h] at hl
      omega
    simp [rectangularUnitFactor, hn2]

def rectangularQuadraticSignedTerm (positive : Bool) (q : QuadraticScales)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (n : Fin 7 → ℕ) : ℂ :=
  if signedQuadraticRelation positive n then quadraticSummand q α β W n else 0

theorem rectangular_unit_signed_term_preserved (f : Fin 4 → Bool) (positive : Bool)
    (q : QuadraticScales) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (n : Fin 7 → ℕ) :
    rectangularQuadraticSignedTerm positive (rectangularUnitScales f q)
      (rectangularUnitCoefficient (rectangularUnitNFactor f) α)
      (rectangularUnitCoefficient (rectangularUnitMFactor f) β) W (rectangularUnitTuple f n) =
      rectangularQuadraticSignedTerm positive q α β W n := by
  unfold rectangularQuadraticSignedTerm
  rw [rectangular_unit_signed_relation, rectangular_unit_summand_preserved]

theorem rectangular_unit_gap_divisible (f : Fin 4 → Bool) (positive : Bool) (n : Fin 7 → ℕ)
    (ha : rectangularUnitNFactor f ∣ n 0) (hb : rectangularUnitMFactor f ∣ n 1)
    (hm1 : rectangularUnitFactor (f 0) ∣ n 2) (hm2 : rectangularUnitFactor (f 1) ∣ n 3)
    (hn1 : rectangularUnitFactor (f 2) ∣ n 4) (hn2 : rectangularUnitFactor (f 3) ∣ n 5)
    (hrel : signedQuadraticRelation positive n) :
    rectangularUnitMFactor f*rectangularUnitNFactor f ∣ n 6 := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  obtain ⟨m1, hm1⟩ := hm1
  obtain ⟨m2, hm2⟩ := hm2
  obtain ⟨n1, hn1⟩ := hn1
  obtain ⟨n2, hn2⟩ := hn2
  have hL : rectangularUnitMFactor f*rectangularUnitNFactor f ∣ n 0*n 2*n 3 := by
    refine ⟨a*m1*m2, ?_⟩
    rw [ha, hm1, hm2]
    unfold rectangularUnitMFactor
    ring
  have hR : rectangularUnitMFactor f*rectangularUnitNFactor f ∣ n 1*n 4*n 5 := by
    refine ⟨b*n1*n2, ?_⟩
    rw [hb, hn1, hn2]
    unfold rectangularUnitNFactor
    ring
  have hLz : ((rectangularUnitMFactor f*rectangularUnitNFactor f : ℕ) : ℤ) ∣
      (n 0 : ℤ)*n 2*n 3 := by exact_mod_cast hL
  have hRz : ((rectangularUnitMFactor f*rectangularUnitNFactor f : ℕ) : ℤ) ∣
      (n 1 : ℤ)*n 4*n 5 := by exact_mod_cast hR
  have hd := dvd_sub hLz hRz
  unfold signedQuadraticRelation at hrel
  rw [hrel] at hd
  cases positive <;> simp at hd
  all_goals exact Int.natCast_dvd_natCast.mp hd

theorem rectangular_unit_nonzero_term_divisible (f : Fin 4 → Bool) (positive : Bool)
    (q : QuadraticScales) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ)
    (hW : ∀ i, SmoothDyadicWeight (W i))
    (hunit : ∀ j, f j = true → q.size (rectangularUnitCoordinate j) = 2/3)
    (n : Fin 7 → ℕ) (hn : n ∈ quadraticIndexSet (rectangularUnitScales f q))
    (ht : rectangularQuadraticSignedTerm positive (rectangularUnitScales f q)
      (rectangularUnitCoefficient (rectangularUnitNFactor f) α)
      (rectangularUnitCoefficient (rectangularUnitMFactor f) β) W n ≠ 0) :
    ∀ j, rectangularUnitFactors f j ∣ n j := by
  have hrel : signedQuadraticRelation positive n := by
    by_contra hh
    simp [rectangularQuadraticSignedTerm, hh] at ht
  have hterm : quadraticSummand (rectangularUnitScales f q)
      (rectangularUnitCoefficient (rectangularUnitNFactor f) α)
      (rectangularUnitCoefficient (rectangularUnitMFactor f) β) W n ≠ 0 := by
    simpa [rectangularQuadraticSignedTerm, hrel] using ht
  rw [rectangular_quadratic_summand_product] at hterm
  have hab := (mul_ne_zero_iff.mp hterm).1
  have ha := rectangular_unit_coefficient_dvd α (mul_ne_zero_iff.mp hab).1
  have hb := rectangular_unit_coefficient_dvd β (mul_ne_zero_iff.mp hab).2
  have hweights (i : Fin 5) :
      W i (rectangularWeightArguments (rectangularUnitScales f q) n i) ≠ 0 := by
    intro hz
    apply (mul_ne_zero_iff.mp hterm).2
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hz]; rfl)
  have hd (j : Fin 4) : rectangularUnitFactor (f j) ∣ n (rectangularUnitCoordinate j) := by
    have hj := (Fintype.mem_piFinset.mp hn) (rectangularUnitCoordinate j)
    rw [rectangular_unit_scales_size, rectangular_unit_coordinate_factor] at hj
    have hw := hweights (rectangularUnitWeightCoordinate j)
    rw [rectangular_unit_coordinate_weight_argument, rectangular_unit_scales_size,
      rectangular_unit_coordinate_factor] at hw
    exact rectangular_unit_low_variable_dvd (f j) _ _ (hW _) (hunit j) _ hj hw
  have hh := rectangular_unit_gap_divisible f positive n ha hb
    (by simpa [rectangularUnitCoordinate] using hd 0)
    (by simpa [rectangularUnitCoordinate] using hd 1)
    (by simpa [rectangularUnitCoordinate] using hd 2)
    (by simpa [rectangularUnitCoordinate] using hd 3) hrel
  intro j
  fin_cases j <;> simp only [rectangularUnitFactors]
  · exact ha
  · exact hb
  · simpa [rectangularUnitCoordinate] using hd 0
  · simpa [rectangularUnitCoordinate] using hd 1
  · simpa [rectangularUnitCoordinate] using hd 2
  · simpa [rectangularUnitCoordinate] using hd 3
  · exact hh

theorem rectangular_unit_signed_quadratic_sum (f : Fin 4 → Bool) (positive : Bool)
    (q : QuadraticScales) (hq : ∀ j, 0 < q.size j)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (hW : ∀ i, SmoothDyadicWeight (W i))
    (hunit : ∀ j, f j = true → q.size (rectangularUnitCoordinate j) = 2/3) :
    signedQuadraticSum positive q α β W =
      signedQuadraticSum positive (rectangularUnitScales f q)
        (rectangularUnitCoefficient (rectangularUnitNFactor f) α)
        (rectangularUnitCoefficient (rectangularUnitMFactor f) β) W := by
  change (∑ n ∈ quadraticIndexSet q, rectangularQuadraticSignedTerm positive q α β W n) =
    ∑ n ∈ quadraticIndexSet (rectangularUnitScales f q),
      rectangularQuadraticSignedTerm positive (rectangularUnitScales f q)
        (rectangularUnitCoefficient (rectangularUnitNFactor f) α)
        (rectangularUnitCoefficient (rectangularUnitMFactor f) β) W n
  apply Finset.sum_bij_ne_zero (fun n _ _ => rectangularUnitTuple f n)
  · intro n hn _
    exact (rectangular_unit_index_mem f q hq n).mpr hn
  · intro n _ _ m _ _ he
    exact rectangular_unit_tuple_injective f he
  · intro n hn ht
    have hd := rectangular_unit_nonzero_term_divisible f positive q α β W hW hunit n hn ht
    let m := rectangularUnitInverse f n
    have he : rectangularUnitTuple f m = n := rectangular_unit_tuple_inverse_right f n hd
    have hm : m ∈ quadraticIndexSet q := by
      apply (rectangular_unit_index_mem f q hq m).mp
      rw [he]
      exact hn
    have hmt : rectangularQuadraticSignedTerm positive q α β W m ≠ 0 := by
      intro hz
      have hp := rectangular_unit_signed_term_preserved f positive q α β W m
      rw [he, hz] at hp
      exact ht hp
    exact ⟨m, hm, hmt, he⟩
  · intro n _ _
    exact (rectangular_unit_signed_term_preserved f positive q α β W n).symm

theorem rectangular_unit_complex_signed_quadratic_sum (f : Fin 4 → Bool) (positive : Bool)
    (q : QuadraticScales) (hq : ∀ j, 0 < q.size j)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℂ) (hW : ∀ i, RectangularComplexWeight (W i))
    (hunit : ∀ j, f j = true → q.size (rectangularUnitCoordinate j) = 2/3) :
    rectangularComplexQuadraticSum positive q α β W =
      rectangularComplexQuadraticSum positive (rectangularUnitScales f q)
        (rectangularUnitCoefficient (rectangularUnitNFactor f) α)
        (rectangularUnitCoefficient (rectangularUnitMFactor f) β) W := by
  rw [rectangular_complex_quadratic_sum_expand, rectangular_complex_quadratic_sum_expand]
  apply Finset.sum_congr rfl
  intro c hc
  rw [rectangular_unit_signed_quadratic_sum f positive q hq α β (rectangularRealComponent W c)
    (rectangular_component_smooth W hW c) hunit]

theorem rectangular_unit_scales_size_bounds (f : Fin 4 → Bool) (q : QuadraticScales)
    (hq : ∀ j, 0 ≤ q.size j) (j : Fin 7) :
    q.size j ≤ (rectangularUnitScales f q).size j ∧
      (rectangularUnitScales f q).size j ≤ 16*q.size j := by
  rw [rectangular_unit_scales_size]
  have hb := rectangular_unit_factors_bounds f j
  have hl : (1:ℝ) ≤ rectangularUnitFactors f j := by exact_mod_cast hb.1
  have hu : (rectangularUnitFactors f j : ℝ) ≤ 16 := by exact_mod_cast hb.2
  constructor
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right hl (hq j)
  · exact mul_le_mul_of_nonneg_right hu (hq j)

theorem rectangular_unit_mass_identity (f : Fin 4 → Bool) (q : QuadraticScales) :
    (rectangularUnitScales f q).mass =
      ((rectangularUnitMFactor f*rectangularUnitNFactor f : ℕ) : ℝ)^2*q.mass := by
  simp [rectangularUnitScales, QuadraticScales.mass, QuadraticScales.M, QuadraticScales.N,
    rectangularUnitMFactor, rectangularUnitNFactor]
  ring

theorem rectangular_unit_gcd_identity (f : Fin 4 → Bool) (a b m n : ℕ) :
    Nat.gcd ((rectangularUnitNFactor f*a)*(rectangularUnitFactor (f 0)*m))
      ((rectangularUnitMFactor f*b)*(rectangularUnitFactor (f 2)*n)) =
      (rectangularUnitFactor (f 0)*rectangularUnitFactor (f 2))*
        Nat.gcd (rectangularUnitFactor (f 3)*a*m) (rectangularUnitFactor (f 1)*b*n) := by
  have hL : (rectangularUnitNFactor f*a)*(rectangularUnitFactor (f 0)*m) =
      (rectangularUnitFactor (f 0)*rectangularUnitFactor (f 2))*
        (rectangularUnitFactor (f 3)*a*m) := by
    unfold rectangularUnitNFactor
    ring
  have hR : (rectangularUnitMFactor f*b)*(rectangularUnitFactor (f 2)*n) =
      (rectangularUnitFactor (f 0)*rectangularUnitFactor (f 2))*
        (rectangularUnitFactor (f 1)*b*n) := by
    unfold rectangularUnitMFactor
    ring
  rw [hL, hR, Nat.gcd_mul_left]

theorem rectangular_unit_discrete_gcd_identity (f : Fin 4 → Bool)
    (hm : f 1 = false) (hn : f 3 = false) (a b m n : ℕ) :
    Nat.gcd ((rectangularUnitNFactor f*a)*(rectangularUnitFactor (f 0)*m))
      ((rectangularUnitMFactor f*b)*(rectangularUnitFactor (f 2)*n)) =
      (rectangularUnitMFactor f*rectangularUnitNFactor f)*Nat.gcd (a*m) (b*n) := by
  rw [rectangular_unit_gcd_identity]
  simp [rectangularUnitMFactor, rectangularUnitNFactor, rectangularUnitFactor, hm, hn]

def rectangularUnitMainTuple (f : Fin 4 → Bool) (n : Fin 5 → ℕ) : Fin 5 → ℕ :=
  ![rectangularUnitNFactor f*n 0, rectangularUnitMFactor f*n 1,
    rectangularUnitFactor (f 0)*n 2, rectangularUnitFactor (f 2)*n 3, n 4]

theorem rectangular_unit_discrete_zero_arguments (f : Fin 4 → Bool)
    (hm : f 1 = false) (hn : f 3 = false) (q : QuadraticScales)
    (n : Fin 5 → ℕ) (x : ℝ) (i : Fin 5) :
    rectangularZeroArguments (rectangularUnitScales f q) (rectangularUnitMainTuple f n) x i =
      rectangularZeroArguments q n x i := by
  have hg := rectangular_unit_discrete_gcd_identity f hm hn (n 0) (n 1) (n 2) (n 3)
  have hM : 0 < rectangularUnitMFactor f := lt_of_lt_of_le Nat.zero_lt_one
    (rectangular_unit_product_factors_bounds f).1
  have hN : 0 < rectangularUnitNFactor f := lt_of_lt_of_le Nat.zero_lt_one
    (rectangular_unit_product_factors_bounds f).2.2.1
  have hMr : (rectangularUnitMFactor f : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hNr : (rectangularUnitNFactor f : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h0r : (rectangularUnitFactor (f 0) : ℝ) ≠ 0 := by
    exact_mod_cast (rectangular_unit_factor_pos (f 0)).ne'
  have h2r : (rectangularUnitFactor (f 2) : ℝ) ≠ 0 := by
    exact_mod_cast (rectangular_unit_factor_pos (f 2)).ne'
  have hmFactor : rectangularUnitFactor (f 1) = 1 := by simp [rectangularUnitFactor, hm]
  have hnFactor : rectangularUnitFactor (f 3) = 1 := by simp [rectangularUnitFactor, hn]
  have hMeq : rectangularUnitMFactor f = rectangularUnitFactor (f 0) := by
    simp [rectangularUnitMFactor, hmFactor]
  have hNeq : rectangularUnitNFactor f = rectangularUnitFactor (f 2) := by
    simp [rectangularUnitNFactor, hnFactor]
  simp only [hMeq, hNeq] at hg
  fin_cases i <;> simp [rectangularZeroArguments, rectangularUnitScales,
    rectangularUnitMainTuple, hg, hMeq, hNeq, hmFactor, hnFactor]
  all_goals field_simp

theorem rectangular_unit_discrete_zero_summand (f : Fin 4 → Bool)
    (hm : f 1 = false) (hn : f 3 = false) (q : QuadraticScales)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (n : Fin 5 → ℕ) :
    quadraticZeroModeSummand (rectangularUnitScales f q)
      (rectangularUnitCoefficient (rectangularUnitNFactor f) α)
      (rectangularUnitCoefficient (rectangularUnitMFactor f) β) W (rectangularUnitMainTuple f n) =
      quadraticZeroModeSummand q α β W n := by
  rw [rectangular_real_zero_summand_product, rectangular_real_zero_summand_product]
  have hM : 0 < rectangularUnitMFactor f := lt_of_lt_of_le Nat.zero_lt_one
    (rectangular_unit_product_factors_bounds f).1
  have hN : 0 < rectangularUnitNFactor f := lt_of_lt_of_le Nat.zero_lt_one
    (rectangular_unit_product_factors_bounds f).2.2.1
  have ha : rectangularUnitMainTuple f n 0 = rectangularUnitNFactor f*n 0 := by
    simp [rectangularUnitMainTuple]
  have hb : rectangularUnitMainTuple f n 1 = rectangularUnitMFactor f*n 1 := by
    simp [rectangularUnitMainTuple]
  rw [ha, hb, rectangular_unit_coefficient_on_image hN, rectangular_unit_coefficient_on_image hM]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  exact Finset.prod_congr rfl (fun i _ => by rw [rectangular_unit_discrete_zero_arguments f hm hn])

end
end SixthMoment
