import SixthMoment.Denominator.Measures.DiagonalLaplaceTransform
import SixthMoment.Denominator.Measures.LimitMeasureDefinitions

namespace SixthMoment
open MeasureTheory Set Complex
open scoped BigOperators ENNReal
noncomputable section
set_option maxHeartbeats 0

theorem d01EdgeLaplace_integrable (a b : Fin 3 → ℂ)
    (ha : ∀ i, 0 < (a i).re) (hb : ∀ j, 0 < (b j).re) :
    Integrable (fun x : D01EdgeSpace =>
      ∏ ij : Fin 3 × Fin 3, Complex.exp (-(a ij.1+b ij.2)*(x ij : ℂ))) d01EdgeMeasure := by
  rw [d01EdgeMeasure_pi]
  apply Integrable.fintype_prod (f := fun ij : Fin 3 × Fin 3 =>
    fun u : ℝ => Complex.exp (-(a ij.1+b ij.2)*(u : ℂ)))
  intro ij
  rw [← restrict_Ioi_eq_restrict_Ici]
  exact integrableOn_exp_mul_complex_Ioi (by simp; linarith [ha ij.1, hb ij.2]) 0

theorem d01EdgeLaplace_integral (a b : Fin 3 → ℂ)
    (ha : ∀ i, 0 < (a i).re) (hb : ∀ j, 0 < (b j).re) :
    (∫ x : D01EdgeSpace,
      ∏ ij : Fin 3 × Fin 3, Complex.exp (-(a ij.1+b ij.2)*(x ij : ℂ)) ∂d01EdgeMeasure) =
      ∏ ij : Fin 3 × Fin 3, (a ij.1+b ij.2)⁻¹ := by
  rw [d01EdgeMeasure_pi]
  rw [integral_fintype_prod_eq_prod (fun ij : Fin 3 × Fin 3 =>
    fun u : ℝ => Complex.exp (-(a ij.1+b ij.2)*(u : ℂ)))]
  apply Finset.prod_congr rfl
  intro ij _
  rw [integral_Ici_eq_integral_Ioi,
    integral_exp_mul_complex_Ioi (by simp; linarith [ha ij.1, hb ij.2])]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, div_neg, neg_div, neg_neg, one_div]

theorem d01ComplexLaplaceWeight_rowColumnSums (ab : PolarShiftSpace) (x : D01EdgeSpace) :
    d01ComplexLaplaceWeight ab (d01RowColumnSums x) =
      ∏ ij : Fin 3 × Fin 3, Complex.exp (-(ab.1 ij.1+ab.2 ij.2)*(x ij : ℂ)) := by
  rw [← Complex.exp_sum]
  unfold d01ComplexLaplaceWeight d01RowColumnSums
  congr 1
  simp only [Complex.ofReal_sum, Fintype.sum_prod_type, Finset.mul_sum,
    neg_mul, add_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rw [Finset.sum_comm (f := fun i j => ab.2 j * (x (i,j) : ℂ))]

theorem d01LimitMeasure_complexLaplace_integrable (ab : PolarShiftSpace)
    (ha : ∀ i, 0 < (ab.1 i).re) (hb : ∀ j, 0 < (ab.2 j).re) :
    Integrable (d01ComplexLaplaceWeight ab) d01LimitMeasure := by
  unfold d01LimitMeasure
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  apply (integrable_map_measure
    (d01ComplexLaplaceWeight_continuous ab).stronglyMeasurable.aestronglyMeasurable
    d01RowColumnSums_continuous.measurable.aemeasurable).mpr
  simpa only [Function.comp_def, d01ComplexLaplaceWeight_rowColumnSums] using
    d01EdgeLaplace_integrable ab.1 ab.2 ha hb

theorem d01LimitMeasure_complexLaplace (ab : PolarShiftSpace)
    (ha : ∀ i, 0 < (ab.1 i).re) (hb : ∀ j, 0 < (ab.2 j).re) :
    (∫ y, d01ComplexLaplaceWeight ab y ∂d01LimitMeasure) =
      (arithmeticFactor : ℂ) * ∏ ij : Fin 3 × Fin 3, (ab.1 ij.1+ab.2 ij.2)⁻¹ := by
  rw [d01LimitMeasure_integral (d01ComplexLaplaceWeight_continuous ab).stronglyMeasurable]
  simp_rw [d01ComplexLaplaceWeight_rowColumnSums]
  rw [d01EdgeLaplace_integral ab.1 ab.2 ha hb]
  exact Complex.real_smul

theorem d01LimitMeasure_laplace_integrable (ab : D01LogSpace)
    (ha : ∀ i, 0 < ab.1 i) (hb : ∀ j, 0 < ab.2 j) :
    Integrable (d01LaplaceWeight ab) d01LimitMeasure := by
  have hi := d01LimitMeasure_complexLaplace_integrable
    (fun i => (ab.1 i : ℂ), fun j => (ab.2 j : ℂ)) (by simpa) (by simpa)
  have hc : Integrable (fun y => (d01LaplaceWeight ab y : ℂ)) d01LimitMeasure := by
    apply hi.congr
    exact ae_of_all _ (fun y => d01ComplexLaplaceWeight_ofReal ab y)
  simpa only [RCLike.re_to_complex, Complex.ofReal_re] using hc.re

theorem d01LimitMeasure_laplace (ab : D01LogSpace)
    (ha : ∀ i, 0 < ab.1 i) (hb : ∀ j, 0 < ab.2 j) :
    (∫ y, d01LaplaceWeight ab y ∂d01LimitMeasure) =
      arithmeticFactor * ∏ ij : Fin 3 × Fin 3, (ab.1 ij.1+ab.2 ij.2)⁻¹ := by
  apply Complex.ofReal_injective
  have h := d01LimitMeasure_complexLaplace
    (fun i => (ab.1 i : ℂ), fun j => (ab.2 j : ℂ)) (by simpa) (by simpa)
  simpa only [d01ComplexLaplaceWeight_ofReal, integral_complex_ofReal,
    Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_inv, Complex.ofReal_add] using h

instance d01LimitMeasure_locallyFinite : IsLocallyFiniteMeasure d01LimitMeasure := by
  let ab : D01LogSpace := (fun _ => 1, fun _ => 1)
  have hi := d01LimitMeasure_laplace_integrable ab (by intro i; norm_num [ab])
    (by intro j; norm_num [ab])
  refine ⟨fun x => ⟨{y | d01LaplaceWeight ab x / 2 < d01LaplaceWeight ab y}, ?_, ?_⟩⟩
  · apply (isOpen_lt continuous_const (d01LaplaceWeight_continuous ab)).mem_nhds
    have hx := d01LaplaceWeight_pos ab x
    change d01LaplaceWeight ab x / 2 < d01LaplaceWeight ab x
    linarith
  · have hsub : {y | d01LaplaceWeight ab x / 2 < d01LaplaceWeight ab y} ⊆
        {y | d01LaplaceWeight ab x / 2 ≤ d01LaplaceWeight ab y} := by
      intro y hy
      change d01LaplaceWeight ab x / 2 < d01LaplaceWeight ab y at hy
      exact hy.le
    exact (measure_mono hsub).trans_lt
      (hi.measure_ge_lt_top (div_pos (d01LaplaceWeight_pos ab x) (by norm_num)))

instance d01LimitMeasure_regular : Measure.Regular d01LimitMeasure := inferInstance

def d01TiltedLimitMeasure (ab : D01LogSpace) : Measure D01LogSpace :=
  d01LimitMeasure.withDensity (fun y => ENNReal.ofReal (d01LaplaceWeight ab y))

theorem d01TiltedLimitMeasure_finite (ab : D01LogSpace)
    (ha : ∀ i, 0 < ab.1 i) (hb : ∀ j, 0 < ab.2 j) :
    IsFiniteMeasure (d01TiltedLimitMeasure ab) :=
  isFiniteMeasure_withDensity_ofReal (d01LimitMeasure_laplace_integrable ab ha hb).2

theorem d01TiltedLimitMeasure_mass (ab : D01LogSpace)
    (ha : ∀ i, 0 < ab.1 i) (hb : ∀ j, 0 < ab.2 j) :
    d01TiltedLimitMeasure ab Set.univ =
      ENNReal.ofReal (arithmeticFactor *
        ∏ ij : Fin 3 × Fin 3, (ab.1 ij.1+ab.2 ij.2)⁻¹) := by
  rw [d01TiltedLimitMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal
      (d01LimitMeasure_laplace_integrable ab ha hb)
      (ae_of_all _ (fun y => (d01LaplaceWeight_pos ab y).le)),
    d01LimitMeasure_laplace ab ha hb]

theorem d01TiltedLimitMeasure_mass_pos (ab : D01LogSpace)
    (ha : ∀ i, 0 < ab.1 i) (hb : ∀ j, 0 < ab.2 j) :
    0 < d01TiltedLimitMeasure ab Set.univ := by
  rw [d01TiltedLimitMeasure_mass ab ha hb]
  apply ENNReal.ofReal_pos.mpr
  apply mul_pos arithmeticFactor_wellDefined.2
  apply Finset.prod_pos
  intro ij _
  exact inv_pos.mpr (add_pos (ha ij.1) (hb ij.2))

theorem d01LimitMeasure_compact_test_integrable
    {E : Type*} [NormedAddCommGroup E] (f : D01LogSpace → E)
    (hf : Continuous f) (hK : HasCompactSupport f) : Integrable f d01LimitMeasure :=
  hf.integrable_of_hasCompactSupport hK

end
end SixthMoment
