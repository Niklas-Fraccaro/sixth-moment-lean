import Sechstmoment.Numerator.U.Reconstruction.RectangularUnitZeroMode
import Sechstmoment.Numerator.U.Separation.BoundaryDilation


namespace Sechstmoment
open Complex Real Source Set MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def boundaryCommonMainTuple (c : ℕ) (n : Fin 5 → ℕ) : Fin 5 → ℕ :=
  ![c*n 0,c*n 1,n 2,n 3,n 4]

def boundaryCommonMainInverse (c : ℕ) (n : Fin 5 → ℕ) : Fin 5 → ℕ :=
  ![n 0/c,n 1/c,n 2,n 3,n 4]

theorem boundaryCommon_main_tuple_injective {c : ℕ} (hc : 0 < c) :
    Function.Injective (boundaryCommonMainTuple c) := by
  intro n m h
  have h₀ : c*n 0=c*m 0 := congrFun h 0
  have h₁ : c*n 1=c*m 1 := congrFun h 1
  have h₂ : n 2=m 2 := congrFun h 2
  have h₃ : n 3=m 3 := congrFun h 3
  have h₄ : n 4=m 4 := congrFun h 4
  funext j
  fin_cases j
  · exact Nat.eq_of_mul_eq_mul_left hc h₀
  · exact Nat.eq_of_mul_eq_mul_left hc h₁
  · exact h₂
  · exact h₃
  · exact h₄

theorem boundaryCommon_main_inverse_right (c : ℕ) (n : Fin 5 → ℕ)
    (h₀ : c ∣ n 0) (h₁ : c ∣ n 1) :
    boundaryCommonMainTuple c (boundaryCommonMainInverse c n)=n := by
  funext j
  fin_cases j <;> simp [boundaryCommonMainTuple,boundaryCommonMainInverse,
    Nat.mul_div_cancel' h₀,Nat.mul_div_cancel' h₁]

theorem boundaryCommon_zero_arguments {c : ℕ} (hc : 0 < c) (q : QuadraticScales)
    (n : Fin 5 → ℕ) (x : ℝ) (i : Fin 5) :
    rectangularZeroArguments (boundaryCommonScales c q) (boundaryCommonMainTuple c n) x i=
      rectangularZeroArguments q n x i := by
  have hg : Nat.gcd ((c*n 0)*n 2) ((c*n 1)*n 3)=
      c*Nat.gcd (n 0*n 2) (n 1*n 3) := by
    rw [Nat.mul_assoc,Nat.mul_assoc,Nat.gcd_mul_left]
  have hcr : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  fin_cases i <;>
    dsimp [rectangularZeroArguments,boundaryCommonScales,boundaryCommonMainTuple]
  all_goals rw [hg]
  all_goals push_cast
  · calc
      ((c:ℝ)*Nat.gcd (n 0*n 2) (n 1*n 3))*(n 4:ℝ)/((c:ℝ)*q.H)=
          (c:ℝ)*((Nat.gcd (n 0*n 2) (n 1*n 3):ℝ)*n 4)/((c:ℝ)*q.H) := by ring
      _ = _ := mul_div_mul_left _ _ hcr
  · calc
      (c:ℝ)*(n 1:ℝ)*(n 3:ℝ)*x/
          (((c:ℝ)*Nat.gcd (n 0*n 2) (n 1*n 3))*q.M₂)=
          (c:ℝ)*((n 1:ℝ)*n 3*x)/
            ((c:ℝ)*((Nat.gcd (n 0*n 2) (n 1*n 3):ℝ)*q.M₂)) := by ring
      _ = _ := mul_div_mul_left _ _ hcr
  · calc
      (c:ℝ)*(n 0:ℝ)*(n 2:ℝ)*x/
          (((c:ℝ)*Nat.gcd (n 0*n 2) (n 1*n 3))*q.N₂)=
          (c:ℝ)*((n 0:ℝ)*n 2*x)/
            ((c:ℝ)*((Nat.gcd (n 0*n 2) (n 1*n 3):ℝ)*q.N₂)) := by ring
      _ = _ := mul_div_mul_left _ _ hcr

theorem boundaryCommon_zero_summand {c : ℕ} (hc : 0 < c)
    (q : QuadraticScales) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (n : Fin 5 → ℕ) :
    quadraticZeroModeSummand (boundaryCommonScales c q)
      (rectangularUnitCoefficient c α) (rectangularUnitCoefficient c β) W
      (boundaryCommonMainTuple c n)=quadraticZeroModeSummand q α β W n := by
  rw [rectangular_real_zero_summand_product,rectangular_real_zero_summand_product]
  change rectangularUnitCoefficient c α (c*n 0)*rectangularUnitCoefficient c β (c*n 1)*
    (∫ x : ℝ in Ioi 0, ∏ i : Fin 5, (W i
      (rectangularZeroArguments (boundaryCommonScales c q) (boundaryCommonMainTuple c n) x i):ℂ))=_
  rw [rectangular_unit_coefficient_on_image hc,rectangular_unit_coefficient_on_image hc]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  exact Finset.prod_congr rfl fun i _ => by rw [boundaryCommon_zero_arguments hc]

private theorem common_main_coordinate (q : QuadraticScales) (n : Fin 5 → ℕ)
    (hn : n∈quadraticMainIndexSet q) (j : Fin 5) :
    n j∈Finset.Icc 1 ⌊2*(![q.A,q.B,q.M₁,q.N₁,q.H]:Fin 5 → ℝ) j⌋₊ :=
  (Fintype.mem_piFinset.mp hn) j

theorem boundaryCommon_quadratic_zero_mode {c : ℕ} (hc : 0 < c)
    (q : QuadraticScales) (hq : ∀ j, 0 < q.size j)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (hW₀ : SmoothDyadicWeight (W 0)) :
    quadraticZeroMode q α β W=quadraticZeroMode (boundaryCommonScales c q)
      (rectangularUnitCoefficient c α) (rectangularUnitCoefficient c β) W := by
  have hA : 0 < q.A := by simpa [QuadraticScales.size] using hq 0
  have hB : 0 < q.B := by simpa [QuadraticScales.size] using hq 1
  have hH : 0 < q.H := by simpa [QuadraticScales.size] using hq 6
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast Nat.succ_le_iff.mpr hc
  unfold quadraticZeroMode
  apply Finset.sum_bij_ne_zero (fun n _ _ => boundaryCommonMainTuple c n)
  · intro n hn _
    apply Fintype.mem_piFinset.mpr
    intro j
    have hj := common_main_coordinate q n hn j
    fin_cases j
    · simpa [boundaryCommonMainTuple,boundaryCommonScales] using
        (rectangular_unit_scaled_index_mem hc hA).mpr hj
    · simpa [boundaryCommonMainTuple,boundaryCommonScales] using
        (rectangular_unit_scaled_index_mem hc hB).mpr hj
    · simpa [boundaryCommonMainTuple,boundaryCommonScales] using hj
    · simpa [boundaryCommonMainTuple,boundaryCommonScales] using hj
    · have hn4 := (Nat.le_floor_iff (by positivity : 0≤2*q.H)).mp
        (Finset.mem_Icc.mp hj).2
      apply Finset.mem_Icc.mpr
      refine ⟨by simpa [boundaryCommonMainTuple] using (Finset.mem_Icc.mp hj).1,?_⟩
      apply (Nat.le_floor_iff (by simp [boundaryCommonScales]; positivity)).mpr
      have hm := mul_le_mul_of_nonneg_right hc1 hH.le
      change (n 4 : ℝ) ≤ 2*q.H at hn4
      simp only [one_mul] at hm
      change (n 4 : ℝ) ≤ 2*((c : ℝ)*q.H)
      exact hn4.trans (mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤2))
  · intro n _ _ m _ _ h
    exact boundaryCommon_main_tuple_injective hc h
  · intro n hn ht
    have hα : rectangularUnitCoefficient c α (n 0) ≠ 0 := by
      intro hz
      simp [quadraticZeroModeSummand,hz] at ht
    have hβ : rectangularUnitCoefficient c β (n 1) ≠ 0 := by
      intro hz
      simp [quadraticZeroModeSummand,hz] at ht
    let m := boundaryCommonMainInverse c n
    have he : boundaryCommonMainTuple c m=n :=
      boundaryCommon_main_inverse_right c n (rectangular_unit_coefficient_dvd α hα)
        (rectangular_unit_coefficient_dvd β hβ)
    have hmt : quadraticZeroModeSummand q α β W m≠0 := by
      intro hz
      have hterm := boundaryCommon_zero_summand hc q α β W m
      rw [he,hz] at hterm
      exact ht hterm
    have hcoords (j : Fin 5) := common_main_coordinate _ n hn j
    have h₀ := (rectangular_unit_scaled_index_mem hc hA).mp
      (by simpa [boundaryCommonMainTuple,boundaryCommonScales,←he] using hcoords 0)
    have h₁ := (rectangular_unit_scaled_index_mem hc hB).mp
      (by simpa [boundaryCommonMainTuple,boundaryCommonScales,←he] using hcoords 1)
    have h₂ : m 2∈Finset.Icc 1 ⌊2*q.M₁⌋₊ := by
      simpa [boundaryCommonMainTuple,boundaryCommonScales,←he] using hcoords 2
    have h₃ : m 3∈Finset.Icc 1 ⌊2*q.N₁⌋₊ := by
      simpa [boundaryCommonMainTuple,boundaryCommonScales,←he] using hcoords 3
    have hh : 0 < m 4 := by
      have h := (Finset.mem_Icc.mp (hcoords 4)).1
      have he4 : m 4=n 4 := congrFun he 4
      omega
    have h₄ := rectangular_zero_mode_reduced_gap_mem q α β W hW₀ hH m
      (by have h := (Finset.mem_Icc.mp h₀).1; omega)
      (by have h := (Finset.mem_Icc.mp h₂).1; omega) hh hmt
    have hm : m∈quadraticMainIndexSet q := by
      apply Fintype.mem_piFinset.mpr
      intro j
      fin_cases j
      · simpa using h₀
      · simpa using h₁
      · simpa using h₂
      · simpa using h₃
      · simpa using h₄
    exact ⟨m,hm,hmt,he⟩
  · intro n _ _
    exact (boundaryCommon_zero_summand hc q α β W n).symm

theorem boundaryCommon_complex_zero_mode {c : ℕ} (hc : 0 < c)
    (q : QuadraticScales) (hq : ∀ j, 0 < q.size j)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℂ) (hW : ∀ i, RectangularComplexWeight (W i)) :
    rectangularComplexZeroMode q α β W=
      rectangularComplexZeroMode (boundaryCommonScales c q)
        (rectangularUnitCoefficient c α) (rectangularUnitCoefficient c β) W := by
  have hM₂ : 0 < q.M₂ := by simpa [QuadraticScales.size] using hq 3
  rw [rectangular_complex_zero_mode_expand q hM₂ α β W hW,
    rectangular_complex_zero_mode_expand (boundaryCommonScales c q)
      (by simpa [boundaryCommonScales] using hM₂)
      (rectangularUnitCoefficient c α) (rectangularUnitCoefficient c β) W hW]
  apply Finset.sum_congr rfl
  intro i _
  rw [boundaryCommon_quadratic_zero_mode hc q hq α β (rectangularRealComponent W i)
    (rectangular_component_smooth W hW i 0)]

end
end Sechstmoment
