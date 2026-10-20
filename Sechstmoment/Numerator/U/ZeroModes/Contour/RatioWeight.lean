import Sechstmoment.Numerator.U.Replacement.GaussianAdmissible


namespace Sechstmoment.Source
open Complex Real Set
open scoped BigOperators
noncomputable section

def a03ZeroModeRatioRoot (α : MomentShifts) (j : Fin 2) : ℂ :=
  ![-(α 0-α 1)/2, -(α 2-α 3)/2] j

def a03ZeroModeRatioWeight (α : MomentShifts) (z : ℂ) : ℂ :=
  exp (z^2)*(1-z^2/(a03ZeroModeRatioRoot α 0)^2)*
    (1-z^2/(a03ZeroModeRatioRoot α 1)^2)

def a03ZeroModeRatioCoefficients (α : MomentShifts) : Fin 3 → ℂ :=
  let r := ((a03ZeroModeRatioRoot α 0)^2)⁻¹
  let q := ((a03ZeroModeRatioRoot α 1)^2)⁻¹
  ![1+r+q-r*q, -r-q, r*q]

theorem a03ZeroModeRatioWeight_basis (α : MomentShifts) (z : ℂ) :
    a03ZeroModeRatioWeight α z =
      ∑ j : Fin 3, a03ZeroModeRatioCoefficients α j*
        fixedGaussianBasis ⟨j.val, by omega⟩ z := by
  simp [Fin.sum_univ_three, a03ZeroModeRatioWeight, a03ZeroModeRatioCoefficients,
    fixedGaussianBasis, div_eq_mul_inv]
  ring

@[simp] theorem a03ZeroModeRatioWeight_zero (α : MomentShifts) :
    a03ZeroModeRatioWeight α 0 = 1 := by
  simp [a03ZeroModeRatioWeight]

theorem a03ZeroModeRatioWeight_even (α : MomentShifts) (z : ℂ) :
    a03ZeroModeRatioWeight α (-z) = a03ZeroModeRatioWeight α z := by
  simp [a03ZeroModeRatioWeight]

theorem a03ZeroModeRatioWeight_differentiable (α : MomentShifts) :
    Differentiable ℂ (a03ZeroModeRatioWeight α) := by
  unfold a03ZeroModeRatioWeight
  fun_prop

theorem a03ZeroModeRatioWeight_at_root (α : MomentShifts) (j : Fin 2)
    (hj : a03ZeroModeRatioRoot α j ≠ 0) :
    a03ZeroModeRatioWeight α (a03ZeroModeRatioRoot α j) = 0 := by
  fin_cases j
  · change a03ZeroModeRatioRoot α 0 ≠ 0 at hj
    change a03ZeroModeRatioWeight α (a03ZeroModeRatioRoot α 0)=0
    unfold a03ZeroModeRatioWeight
    rw [div_self (pow_ne_zero 2 hj)]
    simp
  · change a03ZeroModeRatioRoot α 1 ≠ 0 at hj
    change a03ZeroModeRatioWeight α (a03ZeroModeRatioRoot α 1)=0
    unfold a03ZeroModeRatioWeight
    rw [div_self (pow_ne_zero 2 hj)]
    simp

theorem a03ZeroModeRatioWeight_rapid_strip (α : MomentShifts) (R : ℝ)
    (hR : 0 < R) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |z.re| ≤ R →
      ‖a03ZeroModeRatioWeight α z‖*(1+|z.im|)^N ≤ C := by
  choose C hC hb using (fun j : Fin 3 =>
    fixedGaussianBasis_rapid_strip ⟨j.val, by omega⟩ R hR N)
  refine ⟨∑ j : Fin 3, ‖a03ZeroModeRatioCoefficients α j‖*C j,
    Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (hC j)), ?_⟩
  intro z hz
  rw [a03ZeroModeRatioWeight_basis]
  calc
    _ ≤ (∑ j : Fin 3, ‖a03ZeroModeRatioCoefficients α j*
        fixedGaussianBasis ⟨j.val, by omega⟩ z‖)*(1+|z.im|)^N :=
      mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)
    _ = ∑ j : Fin 3, ‖a03ZeroModeRatioCoefficients α j‖*
        (‖fixedGaussianBasis ⟨j.val, by omega⟩ z‖*(1+|z.im|)^N) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [norm_mul, mul_assoc]
    _ ≤ _ := Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_left (hb j z hz) (norm_nonneg _))

theorem a03ZeroModeRatioWeight_admissible (α : MomentShifts) :
    BBLREntireWeight (a03ZeroModeRatioWeight α) α :=
  ⟨Complex.analyticOnNhd_univ_iff_differentiable.mpr
    (a03ZeroModeRatioWeight_differentiable α),
    a03ZeroModeRatioWeight_even α, a03ZeroModeRatioWeight_zero α,
    a03ZeroModeRatioWeight_rapid_strip α⟩

theorem a03ZeroModeRatioRoot_zero_eq_pure (T : ℝ) (σ : MomentShifts) :
    a03ZeroModeRatioRoot (rawMomentShifts T σ) 0 =
      -purePolarRoot T σ (2,(1,0)) := by
  simp [a03ZeroModeRatioRoot,purePolarRoot,purePolarLeft,purePolarRight,bblrSixShifts]
  ring

theorem a03ZeroModeRatioRoot_one_eq_pure (T : ℝ) (σ : MomentShifts) :
    a03ZeroModeRatioRoot (rawMomentShifts T σ) 1 =
      -purePolarRoot T σ (2,(0,1)) := by
  simp [a03ZeroModeRatioRoot,purePolarRoot,purePolarLeft,purePolarRight,bblrSixShifts]
  ring

theorem a03ZeroModeRatioRoot_norm_lower_bound (T : ℝ) (σ : MomentShifts)
    {κ : ℝ} (hκ : ∀ k : PurePolarIndex, κ≤‖purePolarRoot T σ k‖) (j : Fin 2) :
    κ≤‖a03ZeroModeRatioRoot (rawMomentShifts T σ) j‖ := by
  fin_cases j
  · simpa [a03ZeroModeRatioRoot_zero_eq_pure] using hκ (2,(1,0))
  · simpa [a03ZeroModeRatioRoot_one_eq_pure] using hκ (2,(0,1))

end
end Sechstmoment.Source
