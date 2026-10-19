import Sechstmoment.Numerator.U.Reconstruction.RectangularUnitEmbedding

/-!
# Exact zero modes of the discrete singleton boundary blocks

The signed source sum was already invariant under the integer dilation of
unit variables. For units in the discrete m₁/n₁ positions the *whole actual
zero mode* is invariant as well. The larger reduced-gap range is removed by
the genuine support of W₀ and gcd ≥ 1; it is not assumed to cancel.
This covers f₁ = f₃ = false. Double-unit pairs remain a separate obligation.
-/
namespace Sechstmoment
open Complex Source Set MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def rectangularUnitMainFactors (f : Fin 4 → Bool) : Fin 5 → ℕ :=
  ![rectangularUnitNFactor f, rectangularUnitMFactor f,
    rectangularUnitFactor (f 0), rectangularUnitFactor (f 2), 1]

def rectangularUnitMainInverse (f : Fin 4 → Bool) (n : Fin 5 → ℕ) : Fin 5 → ℕ :=
  fun j => n j / rectangularUnitMainFactors f j

theorem rectangular_unit_main_factor_pos (f : Fin 4 → Bool) (j : Fin 5) :
    0 < rectangularUnitMainFactors f j := by
  have h := rectangular_unit_product_factors_bounds f
  fin_cases j
  · simpa [rectangularUnitMainFactors] using lt_of_lt_of_le Nat.zero_lt_one h.2.2.1
  · simpa [rectangularUnitMainFactors] using lt_of_lt_of_le Nat.zero_lt_one h.1
  · simpa [rectangularUnitMainFactors] using rectangular_unit_factor_pos (f 0)
  · simpa [rectangularUnitMainFactors] using rectangular_unit_factor_pos (f 2)
  · norm_num [rectangularUnitMainFactors]

theorem rectangular_unit_main_tuple_factors (f : Fin 4 → Bool) (n : Fin 5 → ℕ)
    (j : Fin 5) :
    rectangularUnitMainTuple f n j = rectangularUnitMainFactors f j * n j := by
  fin_cases j <;> simp [rectangularUnitMainTuple, rectangularUnitMainFactors]

theorem rectangular_unit_main_tuple_injective (f : Fin 4 → Bool) :
    Function.Injective (rectangularUnitMainTuple f) := by
  intro n m h
  ext j
  have hj := congrFun h j
  rw [rectangular_unit_main_tuple_factors, rectangular_unit_main_tuple_factors] at hj
  exact Nat.eq_of_mul_eq_mul_left (rectangular_unit_main_factor_pos f j) hj

theorem rectangular_unit_main_inverse_right (f : Fin 4 → Bool) (n : Fin 5 → ℕ)
    (hn : ∀ j, rectangularUnitMainFactors f j ∣ n j) :
    rectangularUnitMainTuple f (rectangularUnitMainInverse f n) = n := by
  ext j
  rw [rectangular_unit_main_tuple_factors]
  exact Nat.mul_div_cancel' (hn j)

private theorem main_index_coordinate (q : QuadraticScales) (n : Fin 5 → ℕ)
    (hn : n ∈ quadraticMainIndexSet q) (j : Fin 5) :
    n j ∈ Finset.Icc 1 ⌊2*(![q.A,q.B,q.M₁,q.N₁,q.H] : Fin 5 → ℝ) j⌋₊ :=
  (Fintype.mem_piFinset.mp hn) j

/-- Every nonzero transformed zero-mode summand has the four required
integer divisibilities. The reduced-gap coordinate is unchanged. -/
theorem rectangular_unit_main_nonzero_divisible (f : Fin 4 → Bool)
    (q : QuadraticScales) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ)
    (hW : ∀ i, SmoothDyadicWeight (W i))
    (hm₁ : f 0 = true → q.M₁ = 2/3) (hn₁ : f 2 = true → q.N₁ = 2/3)
    (n : Fin 5 → ℕ) (hn : n ∈ quadraticMainIndexSet (rectangularUnitScales f q))
    (ht : quadraticZeroModeSummand (rectangularUnitScales f q)
      (rectangularUnitCoefficient (rectangularUnitNFactor f) α)
      (rectangularUnitCoefficient (rectangularUnitMFactor f) β) W n ≠ 0) :
    ∀ j, rectangularUnitMainFactors f j ∣ n j := by
  have ha : rectangularUnitCoefficient (rectangularUnitNFactor f) α (n 0) ≠ 0 := by
    intro hz
    simp [quadraticZeroModeSummand, hz] at ht
  have hb : rectangularUnitCoefficient (rectangularUnitMFactor f) β (n 1) ≠ 0 := by
    intro hz
    simp [quadraticZeroModeSummand, hz] at ht
  have hwm : W 1 ((n 2 : ℝ)/(rectangularUnitScales f q).M₁) ≠ 0 := by
    intro hz
    simp [quadraticZeroModeSummand, hz] at ht
  have hwn : W 3 ((n 3 : ℝ)/(rectangularUnitScales f q).N₁) ≠ 0 := by
    intro hz
    simp [quadraticZeroModeSummand, hz] at ht
  have hdm := rectangular_unit_low_variable_dvd (f 0) q.M₁ (W 1) (hW 1) hm₁ (n 2)
    (by simpa [rectangularUnitScales] using main_index_coordinate _ n hn 2)
    (by simpa [rectangularUnitScales] using hwm)
  have hdn := rectangular_unit_low_variable_dvd (f 2) q.N₁ (W 3) (hW 3) hn₁ (n 3)
    (by simpa [rectangularUnitScales] using main_index_coordinate _ n hn 3)
    (by simpa [rectangularUnitScales] using hwn)
  intro j
  fin_cases j
  · simpa [rectangularUnitMainFactors] using rectangular_unit_coefficient_dvd α ha
  · simpa [rectangularUnitMainFactors] using rectangular_unit_coefficient_dvd β hb
  · simpa [rectangularUnitMainFactors] using hdm
  · simpa [rectangularUnitMainFactors] using hdn
  · simp [rectangularUnitMainFactors]

/-- The actual zero-mode support controls its reduced-gap index directly.
The hypothesis concerns a concrete nonzero summand, not a bound on an error. -/
theorem rectangular_zero_mode_reduced_gap_mem (q : QuadraticScales)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (hW₀ : SmoothDyadicWeight (W 0))
    (hH : 0 < q.H) (n : Fin 5 → ℕ) (ha : 0 < n 0) (hm : 0 < n 2)
    (hh : 0 < n 4) (ht : quadraticZeroModeSummand q α β W n ≠ 0) :
    n 4 ∈ Finset.Icc 1 ⌊2*q.H⌋₊ := by
  have hw : W 0 ((Nat.gcd (n 0*n 2) (n 1*n 3) : ℝ)*n 4/q.H) ≠ 0 := by
    intro hz
    simp [quadraticZeroModeSummand, hz] at ht
  have hu := (hW₀.2 (subset_tsupport (W 0) hw)).2
  have hd : 0 < Nat.gcd (n 0*n 2) (n 1*n 3) :=
    Nat.gcd_pos_of_pos_left _ (Nat.mul_pos ha hm)
  have hd1 : (1 : ℝ) ≤ Nat.gcd (n 0*n 2) (n 1*n 3) := by
    exact_mod_cast Nat.succ_le_iff.mpr hd
  apply Finset.mem_Icc.mpr
  refine ⟨Nat.succ_le_iff.mpr hh, ?_⟩
  apply (Nat.le_floor_iff (by positivity : 0 ≤ 2*q.H)).mpr
  have hmul := (div_le_iff₀ hH).mp hu
  have hn4 : (0 : ℝ) ≤ n 4 := Nat.cast_nonneg _
  nlinarith

/-- The complete finite literal source zero mode is invariant for singleton
units put on their discrete sides. All extra transformed gap indices vanish
by the proved support bound above. -/
theorem rectangular_unit_discrete_quadratic_zero_mode (f : Fin 4 → Bool)
    (hm : f 1 = false) (hn : f 3 = false) (q : QuadraticScales)
    (hq : ∀ j, 0 < q.size j) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ)
    (hW : ∀ i, SmoothDyadicWeight (W i))
    (hm₁ : f 0 = true → q.M₁ = 2/3) (hn₁ : f 2 = true → q.N₁ = 2/3) :
    quadraticZeroMode q α β W =
      quadraticZeroMode (rectangularUnitScales f q)
        (rectangularUnitCoefficient (rectangularUnitNFactor f) α)
        (rectangularUnitCoefficient (rectangularUnitMFactor f) β) W := by
  unfold quadraticZeroMode
  apply Finset.sum_bij_ne_zero (fun n _ _ => rectangularUnitMainTuple f n)
  · intro n hni _
    apply Fintype.mem_piFinset.mpr
    intro j
    have hj := main_index_coordinate q n hni j
    have hb := rectangular_unit_product_factors_bounds f
    have hM : 0 < rectangularUnitMFactor f := by omega
    have hN : 0 < rectangularUnitNFactor f := by omega
    have hH : 0 < q.H := by simpa [QuadraticScales.size] using hq 6
    have hMN : (1 : ℝ) ≤ (rectangularUnitMFactor f*rectangularUnitNFactor f : ℕ) := by
      exact_mod_cast Nat.mul_le_mul hb.1 hb.2.2.1
    simp only [Nat.cast_mul] at hMN
    fin_cases j
    · simpa [rectangularUnitMainTuple, rectangularUnitScales] using
        (rectangular_unit_scaled_index_mem hN (by simpa [QuadraticScales.size] using hq 0)).mpr hj
    · simpa [rectangularUnitMainTuple, rectangularUnitScales] using
        (rectangular_unit_scaled_index_mem hM (by simpa [QuadraticScales.size] using hq 1)).mpr hj
    · simpa [rectangularUnitMainTuple, rectangularUnitScales] using
        (rectangular_unit_scaled_index_mem (rectangular_unit_factor_pos (f 0))
          (by simpa [QuadraticScales.size] using hq 2)).mpr hj
    · simpa [rectangularUnitMainTuple, rectangularUnitScales] using
        (rectangular_unit_scaled_index_mem (rectangular_unit_factor_pos (f 2))
          (by simpa [QuadraticScales.size] using hq 4)).mpr hj
    · have hu : (n 4 : ℝ) ≤ 2*q.H :=
        (Nat.le_floor_iff (by positivity : 0 ≤ 2*q.H)).mp (Finset.mem_Icc.mp hj).2
      apply Finset.mem_Icc.mpr
      refine ⟨by simpa [rectangularUnitMainTuple] using (Finset.mem_Icc.mp hj).1, ?_⟩
      apply (Nat.le_floor_iff (by simp [rectangularUnitScales]; positivity)).mpr
      simp [rectangularUnitMainTuple, rectangularUnitScales]
      have hle := mul_le_mul_of_nonneg_right hMN hH.le
      nlinarith
  · intro n _ _ m _ _ he
    exact rectangular_unit_main_tuple_injective f he
  · intro n hni ht
    have hd := rectangular_unit_main_nonzero_divisible f q α β W hW hm₁ hn₁ n hni ht
    let m := rectangularUnitMainInverse f n
    have he : rectangularUnitMainTuple f m = n := rectangular_unit_main_inverse_right f n hd
    have hmt : quadraticZeroModeSummand q α β W m ≠ 0 := by
      intro hz
      have hs := rectangular_unit_discrete_zero_summand f hm hn q α β W m
      rw [he, hz] at hs
      exact ht hs
    have hcoords (j : Fin 5) :
        rectangularUnitMainTuple f m j ∈ Finset.Icc 1
          ⌊2*(![(rectangularUnitScales f q).A, (rectangularUnitScales f q).B,
          (rectangularUnitScales f q).M₁, (rectangularUnitScales f q).N₁,
          (rectangularUnitScales f q).H] : Fin 5 → ℝ) j⌋₊ := by
      rw [he]
      exact main_index_coordinate _ n hni j
    have hb := rectangular_unit_product_factors_bounds f
    have hM : 0 < rectangularUnitMFactor f := by omega
    have hN : 0 < rectangularUnitNFactor f := by omega
    have h0 := (rectangular_unit_scaled_index_mem hN
      (by simpa [QuadraticScales.size] using hq 0)).mp
      (by simpa [rectangularUnitMainTuple, rectangularUnitScales] using hcoords 0)
    have h1 := (rectangular_unit_scaled_index_mem hM
      (by simpa [QuadraticScales.size] using hq 1)).mp
      (by simpa [rectangularUnitMainTuple, rectangularUnitScales] using hcoords 1)
    have h2 := (rectangular_unit_scaled_index_mem (rectangular_unit_factor_pos (f 0))
      (by simpa [QuadraticScales.size] using hq 2)).mp
      (by simpa [rectangularUnitMainTuple, rectangularUnitScales] using hcoords 2)
    have h3 := (rectangular_unit_scaled_index_mem (rectangular_unit_factor_pos (f 2))
      (by simpa [QuadraticScales.size] using hq 4)).mp
      (by simpa [rectangularUnitMainTuple, rectangularUnitScales] using hcoords 3)
    have hh : 0 < m 4 := by
      have hh0 : 1 ≤ m 4 := by
        simpa [rectangularUnitMainTuple] using (Finset.mem_Icc.mp (hcoords 4)).1
      omega
    have h4 := rectangular_zero_mode_reduced_gap_mem q α β W (hW 0)
      (by simpa [QuadraticScales.size] using hq 6) m
      (by have h := (Finset.mem_Icc.mp h0).1; omega)
      (by have h := (Finset.mem_Icc.mp h2).1; omega) hh hmt
    have hmi : m ∈ quadraticMainIndexSet q := by
      apply Fintype.mem_piFinset.mpr
      intro j
      fin_cases j
      · simpa using h0
      · simpa using h1
      · simpa using h2
      · simpa using h3
      · simpa using h4
    exact ⟨m, hmi, hmt, he⟩
  · intro n _ _
    exact (rectangular_unit_discrete_zero_summand f hm hn q α β W n).symm

/- The two source terms are transferred separately before taking their
actual difference. Thus this is an exact source discrepancy identity. -/
theorem rectangular_unit_discrete_signed_discrepancy (f : Fin 4 → Bool)
    (hm : f 1 = false) (hn : f 3 = false) (positive : Bool) (q : QuadraticScales)
    (hq : ∀ j, 0 < q.size j) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ)
    (hW : ∀ i, SmoothDyadicWeight (W i))
    (hm₁ : f 0 = true → q.M₁ = 2/3) (hn₁ : f 2 = true → q.N₁ = 2/3) :
    signedQuadraticDiscrepancy positive q α β W =
      signedQuadraticDiscrepancy positive (rectangularUnitScales f q)
        (rectangularUnitCoefficient (rectangularUnitNFactor f) α)
        (rectangularUnitCoefficient (rectangularUnitMFactor f) β) W := by
  have hunit : ∀ j, f j = true → q.size (rectangularUnitCoordinate j) = 2/3 := by
    intro j
    fin_cases j
    · simpa [QuadraticScales.size, rectangularUnitCoordinate] using hm₁
    · simp [hm]
    · simpa [QuadraticScales.size, rectangularUnitCoordinate] using hn₁
    · simp [hn]
  unfold signedQuadraticDiscrepancy
  rw [rectangular_unit_signed_quadratic_sum f positive q hq α β W hW hunit,
    rectangular_unit_discrete_quadratic_zero_mode f hm hn q hq α β W hW hm₁ hn₁]

/-- Complex Mellin weights inherit the full singleton zero-mode identity
through the genuine integrable 32-component expansion. -/
theorem rectangular_unit_discrete_complex_zero_mode (f : Fin 4 → Bool)
    (hm : f 1 = false) (hn : f 3 = false) (q : QuadraticScales)
    (hq : ∀ j, 0 < q.size j) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℂ)
    (hW : ∀ i, RectangularComplexWeight (W i))
    (hm₁ : f 0 = true → q.M₁ = 2/3) (hn₁ : f 2 = true → q.N₁ = 2/3) :
    rectangularComplexZeroMode q α β W =
      rectangularComplexZeroMode (rectangularUnitScales f q)
        (rectangularUnitCoefficient (rectangularUnitNFactor f) α)
        (rectangularUnitCoefficient (rectangularUnitMFactor f) β) W := by
  have hM₂ : 0 < q.M₂ := by simpa [QuadraticScales.size] using hq 3
  have hM₂' : 0 < (rectangularUnitScales f q).M₂ := by
    simpa [rectangularUnitScales, rectangularUnitFactor, hm] using hM₂
  rw [rectangular_complex_zero_mode_expand q hM₂ α β W hW,
    rectangular_complex_zero_mode_expand (rectangularUnitScales f q) hM₂'
      (rectangularUnitCoefficient (rectangularUnitNFactor f) α)
      (rectangularUnitCoefficient (rectangularUnitMFactor f) β) W hW]
  apply Finset.sum_congr rfl
  intro c _
  rw [rectangular_unit_discrete_quadratic_zero_mode f hm hn q hq α β
    (rectangularRealComponent W c) (rectangular_component_smooth W hW c) hm₁ hn₁]

/-- The whole complex source discrepancy, including its literal zero mode,
is preserved for these singleton boundary blocks. -/
theorem rectangular_unit_discrete_complex_discrepancy (f : Fin 4 → Bool)
    (hm : f 1 = false) (hn : f 3 = false) (positive : Bool) (q : QuadraticScales)
    (hq : ∀ j, 0 < q.size j) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℂ)
    (hW : ∀ i, RectangularComplexWeight (W i))
    (hm₁ : f 0 = true → q.M₁ = 2/3) (hn₁ : f 2 = true → q.N₁ = 2/3) :
    rectangularComplexDiscrepancy positive q α β W =
      rectangularComplexDiscrepancy positive (rectangularUnitScales f q)
        (rectangularUnitCoefficient (rectangularUnitNFactor f) α)
        (rectangularUnitCoefficient (rectangularUnitMFactor f) β) W := by
  have hunit : ∀ j, f j = true → q.size (rectangularUnitCoordinate j) = 2/3 := by
    intro j
    fin_cases j
    · simpa [QuadraticScales.size, rectangularUnitCoordinate] using hm₁
    · simp [hm]
    · simpa [QuadraticScales.size, rectangularUnitCoordinate] using hn₁
    · simp [hn]
  unfold rectangularComplexDiscrepancy
  rw [rectangular_unit_complex_signed_quadratic_sum f positive q hq α β W hW hunit,
    rectangular_unit_discrete_complex_zero_mode f hm hn q hq α β W hW hm₁ hn₁]

end
end Sechstmoment
