import Sechstmoment.Analysis.Alternants.LimitExp


namespace Sechstmoment
open Filter
open scoped Topology

set_option maxHeartbeats 0

theorem determinant_row_one_add_scaled {R : Type*} [CommRing R]
    (a b c d : Fin 4 → R) (t : R) :
    (Matrix.of ![a, (fun j => a j+t*b j), c, d]).det =
      t * (Matrix.of ![a,b,c,d]).det := by
  rw [determinant_four_six_minors, determinant_four_six_minors]
  norm_num [matrixMinorTwo, Matrix.of_apply]
  ring

theorem determinant_row_three_add_scaled {R : Type*} [CommRing R]
    (a b c d : Fin 4 → R) (t : R) :
    (Matrix.of ![a,b,c, (fun j => a j+t*b j+t^2*d j)]).det =
      t^2 * (Matrix.of ![a,b,c,d]).det := by
  rw [determinant_four_six_minors, determinant_four_six_minors]
  norm_num [matrixMinorTwo, Matrix.of_apply]
  ring

noncomputable def firstSlopeExpMatrix (q : Fin 4 → ℂ) (e z w : ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ![(fun _ => 1), (fun j => expFirstSlope (q j) e),
    (fun j => Complex.exp (z*q j)), (fun j => Complex.exp (w*q j))]

noncomputable def secondSlopeExpMatrix (q : Fin 4 → ℂ) (z w : ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ![(fun _ => 1), (fun j => q j),
    (fun j => Complex.exp (z*q j)), (fun j => expSecondSlope (q j) w)]

noncomputable def firstConfluentExpKernel (q : Fin 4 → ℂ) (z w : ℂ) : ℂ :=
  (firstSlopeExpMatrix q 0 z w).det / (z^2*w^2*(w-z))

theorem firstSlopeExpMatrix_continuous (q : Fin 4 → ℂ) (z w : ℂ) :
    Continuous (fun e => firstSlopeExpMatrix q e z w) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i
  all_goals simp only [firstSlopeExpMatrix, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.reduceFinMk]
  · exact continuous_const
  · exact expFirstSlope_continuous (q j)
  · exact continuous_const
  · exact continuous_const

theorem secondSlopeExpMatrix_continuous (q : Fin 4 → ℂ) (z : ℂ) :
    Continuous (fun w => secondSlopeExpMatrix q z w) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i
  all_goals simp only [secondSlopeExpMatrix, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.reduceFinMk]
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact expSecondSlope_continuous (q j)

theorem exponentialAlternant_first_regular (q : Fin 4 → ℂ) (e z w : ℂ)
    (he : e ≠ 0) :
    exponentialAlternant (![0,e,z,w]) q =
      Complex.exp e * (firstSlopeExpMatrix q e z w).det /
        (z*w*(z-e)*(w-e)*(w-z)) := by
  have hexp (j : Fin 4) : Complex.exp (e*q j) = 1+e*expFirstSlope (q j) e := by
    rw [expFirstSlope_of_ne _ _ he]
    field_simp
    ring
  have hmat : expAlternantMatrix (![0,e,z,w]) q =
      Matrix.of ![(fun _ => 1), (fun j => 1+e*expFirstSlope (q j) e),
        (fun j => Complex.exp (z*q j)), (fun j => Complex.exp (w*q j))] := by
    ext i j
    fin_cases i <;> simp [expAlternantMatrix, hexp]
  unfold exponentialAlternant
  rw [hmat, determinant_row_one_add_scaled]
  norm_num [fourVandermonde]
  change _ = Complex.exp e * (Matrix.of _).det / _
  have hd : e*z*w*(z-e)*(w-e)*(w-z) = e*(z*w*(z-e)*(w-e)*(w-z)) := by ring
  rw [hd]
  rw [show Complex.exp e * (e*(Matrix.of _).det) =
    e*(Complex.exp e*(Matrix.of _).det) by ring]
  exact mul_div_mul_left _ _ he

theorem exponentialAlternant_first_limit (q : Fin 4 → ℂ) (z w : ℂ)
    (hz : z ≠ 0) (hw : w ≠ 0) (hwz : w ≠ z) :
    Tendsto (fun e => exponentialAlternant (![0,e,z,w]) q)
      (𝓝[≠] 0) (𝓝 (firstConfluentExpKernel q z w)) := by
  have hc : ContinuousAt (fun e : ℂ =>
      Complex.exp e * (firstSlopeExpMatrix q e z w).det /
        (z*w*(z-e)*(w-e)*(w-z))) 0 := by
    apply ContinuousAt.div
    · exact Complex.continuous_exp.continuousAt.mul
        (firstSlopeExpMatrix_continuous q z w).matrix_det.continuousAt
    · fun_prop
    · simpa using mul_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero hz hw) hz) hw) (sub_ne_zero.mpr hwz)
  have hv : Complex.exp (0 : ℂ) * (firstSlopeExpMatrix q 0 z w).det /
      (z*w*(z-0)*(w-0)*(w-z)) = firstConfluentExpKernel q z w := by
    simp only [Complex.exp_zero, one_mul, sub_zero, firstConfluentExpKernel]
    congr 1
    ring
  have ht := hc.tendsto
  change Tendsto _ (𝓝 0) (𝓝 (Complex.exp (0 : ℂ) *
    (firstSlopeExpMatrix q 0 z w).det / (z*w*(z-0)*(w-0)*(w-z)))) at ht
  rw [hv] at ht
  apply (ht.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with e he
  exact (exponentialAlternant_first_regular q e z w he).symm

theorem firstConfluentExpKernel_second_regular (q : Fin 4 → ℂ) (z w : ℂ)
    (hw : w ≠ 0) :
    firstConfluentExpKernel q z w =
      (secondSlopeExpMatrix q z w).det / (z^2*(w-z)) := by
  have hexp (j : Fin 4) : Complex.exp (w*q j) =
      1+w*q j+w^2*expSecondSlope (q j) w := by
    rw [expSecondSlope_of_ne _ _ hw]
    field_simp
    ring
  have hmat : firstSlopeExpMatrix q 0 z w =
      Matrix.of ![(fun _ => 1), (fun j => q j),
        (fun j => Complex.exp (z*q j)),
        (fun j => 1+w*q j+w^2*expSecondSlope (q j) w)] := by
    ext i j
    fin_cases i <;> simp [firstSlopeExpMatrix, expFirstSlope_zero, hexp]
  unfold firstConfluentExpKernel
  rw [hmat, determinant_row_three_add_scaled]
  change _ = (Matrix.of _).det / _
  rw [show z^2*w^2*(w-z) = w^2*(z^2*(w-z)) by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hw)

theorem secondSlopeExpMatrix_det_zero (q : Fin 4 → ℂ) (z : ℂ) :
    (secondSlopeExpMatrix q z 0).det = -(confluentExpMatrix q z).det/2 := by
  rw [determinant_four_six_minors, determinant_four_six_minors]
  norm_num [matrixMinorTwo, secondSlopeExpMatrix, confluentExpMatrix, expSecondSlope_zero]
  ring

theorem firstConfluentExpKernel_second_limit (q : Fin 4 → ℂ) (z : ℂ)
    (hz : z ≠ 0) :
    Tendsto (firstConfluentExpKernel q z) (𝓝[≠] 0)
      (𝓝 (confluentExpGenerator q z)) := by
  have hc : ContinuousAt (fun w : ℂ =>
      (secondSlopeExpMatrix q z w).det / (z^2*(w-z))) 0 := by
    apply ContinuousAt.div
    · exact (secondSlopeExpMatrix_continuous q z).matrix_det.continuousAt
    · fun_prop
    · simpa using mul_ne_zero (pow_ne_zero 2 hz) (neg_ne_zero.mpr hz)
  have hv : (secondSlopeExpMatrix q z 0).det / (z^2*(0-z)) =
      confluentExpGenerator q z := by
    rw [secondSlopeExpMatrix_det_zero, confluentExpGenerator]
    field_simp
    ring
  have ht := hc.tendsto
  change Tendsto _ (𝓝 0) (𝓝 ((secondSlopeExpMatrix q z 0).det /
    (z^2*(0-z)))) at ht
  rw [hv] at ht
  apply (ht.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact (firstConfluentExpKernel_second_regular q z w hw).symm

end Sechstmoment
