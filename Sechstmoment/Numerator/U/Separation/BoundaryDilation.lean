import Sechstmoment.Numerator.U.Reconstruction.RectangularUnitEmbedding

namespace Sechstmoment
open Complex Source Set MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def boundaryCommonFactors (c : ℕ) : Fin 7 → ℕ := ![c,c,1,1,1,1,c]
def boundaryCommonTuple (c : ℕ) (n : Fin 7 → ℕ) : Fin 7 → ℕ :=
  fun j => boundaryCommonFactors c j*n j
def boundaryCommonInverse (c : ℕ) (n : Fin 7 → ℕ) : Fin 7 → ℕ :=
  fun j => n j/boundaryCommonFactors c j
def boundaryCommonScales (c : ℕ) (q : QuadraticScales) : QuadraticScales where
  A := c*q.A
  B := c*q.B
  M₁ := q.M₁
  M₂ := q.M₂
  N₁ := q.N₁
  N₂ := q.N₂
  H := c*q.H

theorem boundaryCommon_factor_pos {c : ℕ} (hc : 0<c) (j : Fin 7) :
    0 < boundaryCommonFactors c j := by
  fin_cases j <;> simp [boundaryCommonFactors, hc]

theorem boundaryCommon_scale_size (c : ℕ) (q : QuadraticScales) (j : Fin 7) :
    (boundaryCommonScales c q).size j = boundaryCommonFactors c j*q.size j := by
  fin_cases j <;> simp [boundaryCommonScales, boundaryCommonFactors, QuadraticScales.size]

theorem boundaryCommon_tuple_injective {c : ℕ} (hc : 0<c) :
    Function.Injective (boundaryCommonTuple c) := by
  intro n m h
  ext j
  exact Nat.eq_of_mul_eq_mul_left (boundaryCommon_factor_pos hc j) (congrFun h j)

theorem boundaryCommon_inverse_right {c : ℕ} (_hc : 0<c) (n : Fin 7 → ℕ)
    (hd : ∀ j, boundaryCommonFactors c j ∣ n j) :
    boundaryCommonTuple c (boundaryCommonInverse c n) = n := by
  ext j
  exact Nat.mul_div_cancel' (hd j)

theorem boundaryCommon_index_mem {c : ℕ} (hc : 0<c) (q : QuadraticScales)
    (hq : ∀ j, 0<q.size j) (n : Fin 7 → ℕ) :
    boundaryCommonTuple c n ∈ quadraticIndexSet (boundaryCommonScales c q) ↔
      n ∈ quadraticIndexSet q := by
  simp only [quadraticIndexSet, Fintype.mem_piFinset]
  apply forall_congr'
  intro j
  rw [boundaryCommon_scale_size]
  exact rectangular_unit_scaled_index_mem (boundaryCommon_factor_pos hc j) (hq j)

theorem boundaryCommon_signed_relation {c : ℕ} (hc : 0<c)
    (positive : Bool) (n : Fin 7 → ℕ) :
    signedQuadraticRelation positive (boundaryCommonTuple c n) ↔
      signedQuadraticRelation positive n := by
  have hcz : (c : ℤ) ≠ 0 := by exact_mod_cast hc.ne'
  have hL : (boundaryCommonTuple c n 0 : ℤ)*boundaryCommonTuple c n 2*
      boundaryCommonTuple c n 3-(boundaryCommonTuple c n 1 : ℤ)*
      boundaryCommonTuple c n 4*boundaryCommonTuple c n 5 =
      (c : ℤ)*((n 0 : ℤ)*n 2*n 3-(n 1 : ℤ)*n 4*n 5) := by
    simp [boundaryCommonTuple, boundaryCommonFactors]
    ring
  unfold signedQuadraticRelation
  rw [hL]
  cases positive <;> simp [boundaryCommonTuple, boundaryCommonFactors, ←mul_neg,
    mul_right_inj' hcz]

theorem boundaryCommon_weight_arguments {c : ℕ} (hc : 0<c) (q : QuadraticScales)
    (n : Fin 7 → ℕ) (i : Fin 5) :
    rectangularWeightArguments (boundaryCommonScales c q) (boundaryCommonTuple c n) i =
      rectangularWeightArguments q n i := by
  have hcr : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  fin_cases i <;> simp [boundaryCommonScales, boundaryCommonTuple,
    boundaryCommonFactors, rectangularWeightArguments]
  exact mul_div_mul_left _ _ hcr

theorem boundaryCommon_signed_term {c : ℕ} (hc : 0<c) (positive : Bool)
    (q : QuadraticScales) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (n : Fin 7 → ℕ) :
    rectangularQuadraticSignedTerm positive (boundaryCommonScales c q)
      (rectangularUnitCoefficient c α) (rectangularUnitCoefficient c β) W
      (boundaryCommonTuple c n) = rectangularQuadraticSignedTerm positive q α β W n := by
  unfold rectangularQuadraticSignedTerm
  rw [boundaryCommon_signed_relation hc]
  split
  · rw [rectangular_quadratic_summand_product, rectangular_quadratic_summand_product]
    have ha : boundaryCommonTuple c n 0 = c*n 0 := by
      simp [boundaryCommonTuple, boundaryCommonFactors]
    have hb : boundaryCommonTuple c n 1 = c*n 1 := by
      simp [boundaryCommonTuple, boundaryCommonFactors]
    rw [ha, hb, rectangular_unit_coefficient_on_image hc,
      rectangular_unit_coefficient_on_image hc]
    congr 1
    exact Finset.prod_congr rfl (fun i _ => by rw [boundaryCommon_weight_arguments hc])
  · rfl

theorem boundaryCommon_nonzero_divisible {c : ℕ} (_hc : 0<c) (positive : Bool)
    (q : QuadraticScales) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (n : Fin 7 → ℕ)
    (ht : rectangularQuadraticSignedTerm positive (boundaryCommonScales c q)
      (rectangularUnitCoefficient c α) (rectangularUnitCoefficient c β) W n ≠ 0) :
    ∀ j, boundaryCommonFactors c j ∣ n j := by
  have hrel : signedQuadraticRelation positive n := by
    by_contra hh
    simp [rectangularQuadraticSignedTerm, hh] at ht
  have hterm : quadraticSummand (boundaryCommonScales c q)
      (rectangularUnitCoefficient c α) (rectangularUnitCoefficient c β) W n ≠ 0 := by
    simpa [rectangularQuadraticSignedTerm, hrel] using ht
  rw [rectangular_quadratic_summand_product] at hterm
  have hab := (mul_ne_zero_iff.mp hterm).1
  have ha := rectangular_unit_coefficient_dvd α (mul_ne_zero_iff.mp hab).1
  have hb := rectangular_unit_coefficient_dvd β (mul_ne_zero_iff.mp hab).2
  have hL : (c : ℤ) ∣ (n 0 : ℤ)*n 2*n 3 := by
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by exact_mod_cast ha) _) _
  have hR : (c : ℤ) ∣ (n 1 : ℤ)*n 4*n 5 := by
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by exact_mod_cast hb) _) _
  have hh := dvd_sub hL hR
  unfold signedQuadraticRelation at hrel
  rw [hrel] at hh
  have hd : c ∣ n 6 := by
    cases positive <;> simp at hh
    all_goals exact Int.natCast_dvd_natCast.mp hh
  intro j
  fin_cases j <;> simp [boundaryCommonFactors, ha, hb, hd]

theorem boundaryCommon_signed_sum {c : ℕ} (hc : 0<c) (positive : Bool)
    (q : QuadraticScales) (hq : ∀ j, 0<q.size j)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) :
    signedQuadraticSum positive q α β W = signedQuadraticSum positive
      (boundaryCommonScales c q) (rectangularUnitCoefficient c α)
      (rectangularUnitCoefficient c β) W := by
  change (∑ n ∈ quadraticIndexSet q, rectangularQuadraticSignedTerm positive q α β W n) =
    ∑ n ∈ quadraticIndexSet (boundaryCommonScales c q), rectangularQuadraticSignedTerm
      positive (boundaryCommonScales c q) (rectangularUnitCoefficient c α)
        (rectangularUnitCoefficient c β) W n
  apply Finset.sum_bij_ne_zero (fun n _ _ => boundaryCommonTuple c n)
  · intro n hn _
    exact (boundaryCommon_index_mem hc q hq n).mpr hn
  · intro n _ _ m _ _ he
    exact boundaryCommon_tuple_injective hc he
  · intro n hn ht
    have hd := boundaryCommon_nonzero_divisible hc positive q α β W n ht
    let m := boundaryCommonInverse c n
    have he : boundaryCommonTuple c m = n := boundaryCommon_inverse_right hc n hd
    have hm : m ∈ quadraticIndexSet q := by
      apply (boundaryCommon_index_mem hc q hq m).mp
      rw [he]
      exact hn
    have hmt : rectangularQuadraticSignedTerm positive q α β W m ≠ 0 := by
      intro hz
      have hp := boundaryCommon_signed_term hc positive q α β W m
      rw [he, hz] at hp
      exact ht hp
    exact ⟨m, hm, hmt, he⟩
  · intro n _ _
    exact (boundaryCommon_signed_term hc positive q α β W n).symm

theorem boundaryCommon_complex_signed_sum {c : ℕ} (hc : 0<c) (positive : Bool)
    (q : QuadraticScales) (hq : ∀ j, 0<q.size j)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℂ) :
    rectangularComplexQuadraticSum positive q α β W = rectangularComplexQuadraticSum
      positive (boundaryCommonScales c q) (rectangularUnitCoefficient c α)
      (rectangularUnitCoefficient c β) W := by
  rw [rectangular_complex_quadratic_sum_expand, rectangular_complex_quadratic_sum_expand]
  apply Finset.sum_congr rfl
  intro d _
  rw [boundaryCommon_signed_sum hc positive q hq α β (rectangularRealComponent W d)]

theorem boundaryCommon_mass (c : ℕ) (q : QuadraticScales) :
    (boundaryCommonScales c q).mass = (c : ℝ)^2*q.mass := by
  simp [boundaryCommonScales, QuadraticScales.mass, QuadraticScales.M, QuadraticScales.N]
  ring

theorem boundaryCommon_two_lower_bound (q : QuadraticScales)
    (hA : 2/3≤q.A) (hB : 2/3≤q.B) (hH : 2/3≤q.H)
    (hm1 : 1≤q.M₁) (hm2 : 1≤q.M₂) (hn1 : 1≤q.N₁) (hn2 : 1≤q.N₂) :
    ∀ j, 1≤(boundaryCommonScales 2 q).size j := by
  intro j
  fin_cases j <;> simp [boundaryCommonScales, QuadraticScales.size]
  all_goals linarith

def boundaryEmbeddedScales (f : Fin 4 → Bool) (q : QuadraticScales) : QuadraticScales :=
  boundaryCommonScales 2 (rectangularUnitScales f q)
def boundaryEmbeddedAlpha (f : Fin 4 → Bool) (α : ℕ → ℂ) : ℕ → ℂ :=
  rectangularUnitCoefficient 2 (rectangularUnitCoefficient (rectangularUnitNFactor f) α)
def boundaryEmbeddedBeta (f : Fin 4 → Bool) (β : ℕ → ℂ) : ℕ → ℂ :=
  rectangularUnitCoefficient 2 (rectangularUnitCoefficient (rectangularUnitMFactor f) β)

theorem boundaryEmbedded_signed_sum (f : Fin 4 → Bool) (positive : Bool)
    (q : QuadraticScales) (hq : ∀ j, 0<q.size j)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℂ) (hW : ∀ i, RectangularComplexWeight (W i))
    (hu : ∀ j, f j = true → q.size (rectangularUnitCoordinate j) = 2/3) :
    rectangularComplexQuadraticSum positive q α β W =
      rectangularComplexQuadraticSum positive (boundaryEmbeddedScales f q)
        (boundaryEmbeddedAlpha f α) (boundaryEmbeddedBeta f β) W := by
  rw [rectangular_unit_complex_signed_quadratic_sum f positive q hq α β W hW hu]
  exact boundaryCommon_complex_signed_sum (by norm_num) positive (rectangularUnitScales f q)
    (fun j => by
      rw [rectangular_unit_scales_size]
      exact mul_pos (by exact_mod_cast rectangular_unit_factors_pos f j) (hq j))
    (rectangularUnitCoefficient (rectangularUnitNFactor f) α)
    (rectangularUnitCoefficient (rectangularUnitMFactor f) β) W

theorem boundaryEmbedded_mass (f : Fin 4 → Bool) (q : QuadraticScales) :
    (boundaryEmbeddedScales f q).mass =
      4*((rectangularUnitMFactor f*rectangularUnitNFactor f : ℕ) : ℝ)^2*q.mass := by
  unfold boundaryEmbeddedScales
  rw [boundaryCommon_mass, rectangular_unit_mass_identity]
  norm_num
  ring

theorem boundaryEmbedded_size_bounds (f : Fin 4 → Bool) (q : QuadraticScales)
    (hq : ∀ j, 0≤q.size j) (j : Fin 7) :
    q.size j ≤ (boundaryEmbeddedScales f q).size j ∧
      (boundaryEmbeddedScales f q).size j ≤ 32*q.size j := by
  unfold boundaryEmbeddedScales
  rw [boundaryCommon_scale_size]
  have hu := rectangular_unit_scales_size_bounds f q hq j
  have hf : (1 : ℝ) ≤ boundaryCommonFactors 2 j ∧
      (boundaryCommonFactors 2 j : ℝ) ≤ 2 := by
    fin_cases j <;> norm_num [boundaryCommonFactors]
  have hnn : 0≤(rectangularUnitScales f q).size j := (hq j).trans hu.1
  constructor
  · exact hu.1.trans (by simpa using mul_le_mul_of_nonneg_right hf.1 hnn)
  · calc
      _ ≤ 2*(rectangularUnitScales f q).size j :=
        mul_le_mul_of_nonneg_right hf.2 hnn
      _ ≤ 2*(16*q.size j) := mul_le_mul_of_nonneg_left hu.2 (by norm_num)
      _ = _ := by ring

theorem boundaryEmbedded_lower_bound (f : Fin 4 → Bool) (q : QuadraticScales)
    (hA : 2/3≤q.A) (hB : 2/3≤q.B) (hH : 2/3≤q.H)
    (hm1 : if f 0 then q.M₁=2/3 else 1≤q.M₁)
    (hm2 : if f 1 then q.M₂=2/3 else 1≤q.M₂)
    (hn1 : if f 2 then q.N₁=2/3 else 1≤q.N₁)
    (hn2 : if f 3 then q.N₂=2/3 else 1≤q.N₂) :
    ∀ j, 1≤(boundaryEmbeddedScales f q).size j := by
  have hp (b : Bool) (x : ℝ) (hx : if b then x=2/3 else 1≤x) :
      1≤(rectangularUnitFactor b : ℝ)*x := by
    cases b
    · simpa [rectangularUnitFactor] using hx
    · simp only [ite_true] at hx
      rw [hx]
      norm_num [rectangularUnitFactor]
  have hf := rectangular_unit_product_factors_bounds f
  have hm : (1 : ℝ)≤rectangularUnitMFactor f := by exact_mod_cast hf.1
  have hn : (1 : ℝ)≤rectangularUnitNFactor f := by exact_mod_cast hf.2.2.1
  have hmn : (1 : ℝ)≤(rectangularUnitMFactor f : ℝ)*rectangularUnitNFactor f :=
    one_le_mul_of_one_le_of_one_le hm hn
  apply boundaryCommon_two_lower_bound
  · change 2/3≤(rectangularUnitNFactor f : ℝ)*q.A
    exact hA.trans (by simpa using mul_le_mul_of_nonneg_right hn (by linarith : 0≤q.A))
  · change 2/3≤(rectangularUnitMFactor f : ℝ)*q.B
    exact hB.trans (by simpa using mul_le_mul_of_nonneg_right hm (by linarith : 0≤q.B))
  · change 2/3≤((rectangularUnitMFactor f : ℝ)*rectangularUnitNFactor f)*q.H
    exact hH.trans (by simpa using mul_le_mul_of_nonneg_right hmn (by linarith : 0≤q.H))
  · exact hp _ _ hm1
  · exact hp _ _ hm2
  · exact hp _ _ hn1
  · exact hp _ _ hn2

theorem boundaryEmbedded_alpha_support (f : Fin 4 → Bool) (q : QuadraticScales)
    (α : ℕ → ℂ) (hα : ∀ n : ℕ, (n : ℝ)∉Icc q.A (2*q.A) → α n=0) :
    ∀ n : ℕ, (n : ℝ)∉Icc (boundaryEmbeddedScales f q).A
      (2*(boundaryEmbeddedScales f q).A) → boundaryEmbeddedAlpha f α n=0 := by
  exact rectangular_unit_coefficient_support (by norm_num) _ _
    (rectangular_unit_coefficient_support (by
      exact lt_of_lt_of_le Nat.zero_lt_one (rectangular_unit_product_factors_bounds f).2.2.1)
      α q.A hα)

theorem boundaryEmbedded_beta_support (f : Fin 4 → Bool) (q : QuadraticScales)
    (β : ℕ → ℂ) (hβ : ∀ n : ℕ, (n : ℝ)∉Icc q.B (2*q.B) → β n=0) :
    ∀ n : ℕ, (n : ℝ)∉Icc (boundaryEmbeddedScales f q).B
      (2*(boundaryEmbeddedScales f q).B) → boundaryEmbeddedBeta f β n=0 := by
  exact rectangular_unit_coefficient_support (by norm_num) _ _
    (rectangular_unit_coefficient_support (by
      exact lt_of_lt_of_le Nat.zero_lt_one (rectangular_unit_product_factors_bounds f).1)
      β q.B hβ)

theorem boundaryEmbedded_alpha_bound (f : Fin 4 → Bool) (q : QuadraticScales)
    (α : ℕ → ℂ) {K ε : ℝ} (hK : 0≤K) (hε : 0≤ε) (hA : 0<q.A)
    (hα : ∀ n, ‖α n‖≤K*q.A^ε) :
    ∀ n, ‖boundaryEmbeddedAlpha f α n‖≤K*(boundaryEmbeddedScales f q).A^ε := by
  have hn : 0<rectangularUnitNFactor f :=
    lt_of_lt_of_le Nat.zero_lt_one (rectangular_unit_product_factors_bounds f).2.2.1
  have hAn : 0<(rectangularUnitNFactor f : ℝ)*q.A :=
    mul_pos (by exact_mod_cast hn) hA
  exact rectangular_unit_coefficient_power_bound (by norm_num) _ hK hAn hε
    (rectangular_unit_coefficient_power_bound hn α hK hA hε hα)

theorem boundaryEmbedded_beta_bound (f : Fin 4 → Bool) (q : QuadraticScales)
    (β : ℕ → ℂ) {K ε : ℝ} (hK : 0≤K) (hε : 0≤ε) (hB : 0<q.B)
    (hβ : ∀ n, ‖β n‖≤K*q.B^ε) :
    ∀ n, ‖boundaryEmbeddedBeta f β n‖≤K*(boundaryEmbeddedScales f q).B^ε := by
  have hm : 0<rectangularUnitMFactor f :=
    lt_of_lt_of_le Nat.zero_lt_one (rectangular_unit_product_factors_bounds f).1
  have hBm : 0<(rectangularUnitMFactor f : ℝ)*q.B :=
    mul_pos (by exact_mod_cast hm) hB
  exact rectangular_unit_coefficient_power_bound (by norm_num) _ hK hBm hε
    (rectangular_unit_coefficient_power_bound hm β hK hB hε hβ)

theorem boundaryEmbedded_mass_le (f : Fin 4 → Bool) (q : QuadraticScales)
    (hq : 0≤q.mass) : q.mass≤(boundaryEmbeddedScales f q).mass := by
  rw [boundaryEmbedded_mass]
  have hb := rectangular_unit_product_factors_bounds f
  have hn : (1 : ℝ)≤(rectangularUnitMFactor f*rectangularUnitNFactor f : ℕ) := by
    exact_mod_cast Nat.mul_le_mul hb.1 hb.2.2.1
  have hp : 1≤4*((rectangularUnitMFactor f*rectangularUnitNFactor f : ℕ) : ℝ)^2 := by
    nlinarith
  simpa using mul_le_mul_of_nonneg_right hp hq

theorem boundaryEmbedded_derivative_bounds (f : Fin 4 → Bool) (q : QuadraticScales)
    (W : Fin 5 → ℝ → ℂ) {ε : ℝ} (hε : 0≤ε) (hq : 0≤q.mass)
    (bounds : ℕ → ℝ) (hb : ∀ j, 0≤bounds j)
    (hd : ∀ j i x, ‖iteratedDeriv j (W i) x‖≤bounds j*q.mass^ε) :
    ∀ j i x, ‖iteratedDeriv j (W i) x‖≤bounds j*(boundaryEmbeddedScales f q).mass^ε := by
  intro j i x
  exact (hd j i x).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hq (boundaryEmbedded_mass_le f q hq) hε) (hb j))

end
end Sechstmoment
