import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.InnerProductSpace.PiL2
import SixthMoment.Numerator.U.Separation.MellinWeights


namespace SixthMoment
open Complex Real Set MeasureTheory
open scoped BigOperators FourierTransform RealInnerProductSpace
noncomputable section
set_option maxHeartbeats 1000000

abbrev A03SixTensorSpace := EuclideanSpace ℝ (Fin 6)

def a03SixTensorLogPoint (x : Fin 6 → ℝ) : A03SixTensorSpace :=
  WithLp.toLp 2 (fun j => Real.log (x j))

def a03SixTensorExponent (ν : A03SixTensorSpace) (j : Fin 6) : ℂ :=
  (2 * Real.pi * ν j : ℝ) * Complex.I

def a03SixTensorWeight (a : A03SixTensorSpace → ℝ) (ν : A03SixTensorSpace)
    (j : Fin 5) (x : ℝ) : ℂ :=
  (a ν : ℂ) * rectangularMellinBlockWeight (a03SixTensorExponent ν j.succ) x

def a03SixTensorCoefficient (f : SchwartzMap A03SixTensorSpace ℂ)
    (a : A03SixTensorSpace → ℝ) (ν : A03SixTensorSpace) : ℂ :=
  (𝓕 f) ν / (a ν : ℂ)^5

theorem a03SixTensorExponent_re (ν : A03SixTensorSpace) (j : Fin 6) :
    (a03SixTensorExponent ν j).re = 0 := by
  simp [a03SixTensorExponent]

theorem a03SixTensorWeight_complexWeight (a : A03SixTensorSpace → ℝ)
    (ν : A03SixTensorSpace) (j : Fin 5) :
    RectangularComplexWeight (a03SixTensorWeight a ν j) := by
  constructor
  · exact contDiff_const.mul (rectangularMellinBlockWeight_complexWeight _).1
  · apply closure_minimal
    · intro x hx
      have hm : rectangularMellinBlockWeight (a03SixTensorExponent ν j.succ) x ≠ 0 := by
        intro hz
        exact hx (by simp [a03SixTensorWeight, hz])
      exact (rectangularMellinBlockWeight_complexWeight _).2 (subset_tsupport _ hm)
    · exact isClosed_Icc

private theorem a03SixTensorPositivePhase (ν : A03SixTensorSpace) (x : Fin 6 → ℝ)
    (hx : ∀ j, 0 < x j) :
    (∏ j, (x j : ℂ) ^ a03SixTensorExponent ν j) =
      Complex.exp ((2 * Real.pi * ⟪ν, a03SixTensorLogPoint x⟫ : ℝ) * Complex.I) := by
  simp_rw [a03SixTensorExponent, Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (hx _).ne'), ← Complex.ofReal_log (hx _).le]
  rw [← Complex.exp_sum]
  congr 1
  simp only [a03SixTensorLogPoint, PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial,
    Complex.ofReal_mul, Complex.ofReal_sum]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem a03SixTensor_pointwise_separation (f : SchwartzMap A03SixTensorSpace ℂ)
    (a : A03SixTensorSpace → ℝ) (ha : ∀ ν, 0 < a ν) (ν : A03SixTensorSpace)
    (x : Fin 6 → ℝ) (hx : ∀ j, 0 < x j) :
    a03SixTensorCoefficient f a ν * ((x 0 : ℂ)^a03SixTensorExponent ν 0 *
      (∏ j, a03SixTensorWeight a ν j (x j.succ))) =
      (∏ j : Fin 5, (rectangularSmoothBlockWeight (x j.succ) : ℂ)) *
        (Complex.exp ((2 * Real.pi * ⟪ν, a03SixTensorLogPoint x⟫ : ℝ) * Complex.I) *
          (𝓕 f) ν) := by
  have ha0 : (a ν : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ha ν).ne'
  simp only [a03SixTensorCoefficient, a03SixTensorWeight, rectangularMellinBlockWeight,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hp := a03SixTensorPositivePhase ν x hx
  rw [Fin.prod_univ_succ] at hp
  rw [← hp]
  field_simp

theorem a03SixTensor_exact_separation (f : SchwartzMap A03SixTensorSpace ℂ)
    (a : A03SixTensorSpace → ℝ) (ha : ∀ ν, 0 < a ν)
    (x : Fin 6 → ℝ) (hx : ∀ j, 0 < x j) :
    (∏ j : Fin 5, (rectangularSmoothBlockWeight (x j.succ) : ℂ)) * f (a03SixTensorLogPoint x) =
      ∫ ν : A03SixTensorSpace,
        a03SixTensorCoefficient f a ν * ((x 0 : ℂ)^a03SixTensorExponent ν 0 *
      (∏ j, a03SixTensorWeight a ν j (x j.succ))) := by
  simp_rw [a03SixTensor_pointwise_separation f a ha _ x hx]
  rw [integral_const_mul]
  congr 1
  have he : 𝓕⁻ (𝓕 (f : A03SixTensorSpace → ℂ)) (a03SixTensorLogPoint x) =
      f (a03SixTensorLogPoint x) :=
    f.integrable.fourierInv_fourier_eq (𝓕 f).integrable f.continuous.continuousAt
  simpa only [fourierInv_eq', smul_eq_mul, ← SchwartzMap.fourier_coe] using he.symm

theorem a03SixTensor_exact_separation_all_real (f : SchwartzMap A03SixTensorSpace ℂ)
    (a : A03SixTensorSpace → ℝ) (ha : ∀ ν, 0 < a ν) (x : Fin 6 → ℝ)
    (hx0 : 0 < x 0) :
    (∏ j : Fin 5, (rectangularSmoothBlockWeight (x j.succ) : ℂ)) *
      f (a03SixTensorLogPoint x) =
      ∫ ν : A03SixTensorSpace,
        a03SixTensorCoefficient f a ν * ((x 0 : ℂ)^a03SixTensorExponent ν 0 *
          (∏ j, a03SixTensorWeight a ν j (x j.succ))) := by
  by_cases hx : ∀ j : Fin 5, 0 < x j.succ
  · exact a03SixTensor_exact_separation f a ha x (Fin.cases hx0 hx)
  · obtain ⟨j, hj⟩ := not_forall.mp hx
    have hz : rectangularSmoothBlockWeight (x j.succ) = 0 :=
      rectangularSmoothBlockWeight_zero_le (by linarith)
    have hp : (∏ i : Fin 5, (rectangularSmoothBlockWeight (x i.succ) : ℂ)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [hz]
    have hi (ν : A03SixTensorSpace) : (∏ i, a03SixTensorWeight a ν i (x i.succ)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [a03SixTensorWeight, rectangularMellinBlockWeight, hz]
    simp only [hp, zero_mul, hi, mul_zero, integral_zero]

theorem a03SixTensorCoefficient_measurable (f : SchwartzMap A03SixTensorSpace ℂ)
    (a : A03SixTensorSpace → ℝ) (ha : Measurable a) :
    Measurable (a03SixTensorCoefficient f a) := by
  unfold a03SixTensorCoefficient
  exact (𝓕 f).continuous.measurable.div ((Complex.measurable_ofReal.comp ha).pow_const 5)

theorem a03SixTensorWeight_uniform_derivative_bounds
    (a : A03SixTensorSpace → ℝ) (ha : ∀ ν, 0 ≤ a ν)
    (hrapid : ∀ j : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ ν, a ν * (1 + ‖ν‖)^j ≤ D) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧ ∀ j ν i x,
      ‖iteratedDeriv j (a03SixTensorWeight a ν i) x‖ ≤ B j := by
  obtain ⟨C, hC, hb⟩ := rectangularMellinBlockWeight_polynomial_derivative_bounds
  choose D hD hd using hrapid
  let B : ℕ → ℝ := fun j => C j * (1 + 2 * Real.pi)^j * D j
  have hB (j : ℕ) : 0 ≤ B j := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (hC j) (by positivity)) (hD j)
  refine ⟨B, hB, ?_⟩
  intro j ν i x
  have hn : ‖a03SixTensorExponent ν i.succ‖ ≤ 2 * Real.pi * ‖ν‖ := by
    simp only [a03SixTensorExponent, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2),
      abs_of_pos Real.pi_pos]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le ν i.succ
  have hscale : 1 + ‖a03SixTensorExponent ν i.succ‖ ≤ (1 + 2 * Real.pi) * (1 + ‖ν‖) := by
    nlinarith [Real.pi_pos, norm_nonneg ν]
  change ‖iteratedDeriv j (fun y : ℝ => (a ν : ℂ) *
    rectangularMellinBlockWeight (a03SixTensorExponent ν i.succ) y) x‖ ≤ B j
  rw [iteratedDeriv_const_mul_field, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (ha ν)]
  calc
    _ ≤ a ν * (C j * (1 + ‖a03SixTensorExponent ν i.succ‖)^j) :=
      mul_le_mul_of_nonneg_left (hb j _ (by rw [a03SixTensorExponent_re]) x) (ha ν)
    _ ≤ a ν * (C j * ((1 + 2 * Real.pi) * (1 + ‖ν‖))^j) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hscale j) (hC j))
        (ha ν)
    _ = (C j * (1 + 2 * Real.pi)^j) * (a ν * (1 + ‖ν‖)^j) := by
      rw [mul_pow]
      ring
    _ ≤ (C j * (1 + 2 * Real.pi)^j) * D j :=
      mul_le_mul_of_nonneg_left (hd j ν) (mul_nonneg (hC j) (by positivity))
    _ = B j := rfl

end
end SixthMoment
