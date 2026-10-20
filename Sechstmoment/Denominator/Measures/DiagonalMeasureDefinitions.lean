import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Sechstmoment.Numerator.U.Diagonal.DiagonalEulerSixIndices


namespace Sechstmoment
open MeasureTheory Real Complex Set Filter
open scoped BigOperators Topology ENNReal
noncomputable section
set_option maxHeartbeats 0

abbrev D01LogSpace := (Fin 3 → ℝ) × (Fin 3 → ℝ)
abbrev D01EdgeSpace := Fin 3 × Fin 3 → ℝ

def d01LeftIndices (x : DiagonalSixIndices) : Fin 3 → ℕ :=
  ![x.val.1.1, x.val.1.2.1, x.val.1.2.2]

def d01RightIndices (x : DiagonalSixIndices) : Fin 3 → ℕ :=
  ![x.val.2.1, x.val.2.2.1, x.val.2.2.2]

def d01CommonProduct (x : DiagonalSixIndices) : ℕ :=
  x.val.1.1 * (x.val.1.2.1 * x.val.1.2.2)

theorem d01CommonProduct_pos (x : DiagonalSixIndices) : 0 < d01CommonProduct x :=
  Nat.pos_of_ne_zero x.property.2

theorem d01LeftIndices_pos (x : DiagonalSixIndices) (i : Fin 3) :
    0 < d01LeftIndices x i := by
  have h := x.property.2
  simp only [mul_ne_zero_iff] at h
  fin_cases i <;> simp [d01LeftIndices] <;> omega

theorem d01RightIndices_pos (x : DiagonalSixIndices) (i : Fin 3) :
    0 < d01RightIndices x i := by
  have h : x.val.2.1 * (x.val.2.2.1 * x.val.2.2.2) ≠ 0 := by
    rw [← x.property.1]
    exact x.property.2
  simp only [mul_ne_zero_iff] at h
  fin_cases i <;> simp [d01RightIndices] <;> omega

def d01LogPoint (L : ℝ) (x : DiagonalSixIndices) : D01LogSpace :=
  (fun i => Real.log (d01LeftIndices x i : ℝ) / L,
   fun j => Real.log (d01RightIndices x j : ℝ) / L)

def d01AtomicWeight (L : ℝ) (x : DiagonalSixIndices) : ℝ :=
  L⁻¹ ^ 9 / (d01CommonProduct x : ℝ)

def d01DiagonalMeasure (L : ℝ) : Measure D01LogSpace :=
  Measure.sum fun x : DiagonalSixIndices =>
    ENNReal.ofReal (d01AtomicWeight L x) • Measure.dirac (d01LogPoint L x)

def d01PositiveOrthant : Set D01LogSpace :=
  {y | (∀ i, 0 ≤ y.1 i) ∧ (∀ j, 0 ≤ y.2 j)}

def d01LaplaceWeight (ab : D01LogSpace) (y : D01LogSpace) : ℝ :=
  Real.exp (-(∑ i, ab.1 i * y.1 i + ∑ j, ab.2 j * y.2 j))

def d01ComplexLaplaceWeight (ab : PolarShiftSpace) (y : D01LogSpace) : ℂ :=
  Complex.exp (-(∑ i, ab.1 i * (y.1 i : ℂ) + ∑ j, ab.2 j * (y.2 j : ℂ)))

theorem d01AtomicWeight_pos {L : ℝ} (hL : 0 < L) (x : DiagonalSixIndices) :
    0 < d01AtomicWeight L x := by
  unfold d01AtomicWeight
  exact div_pos (pow_pos (inv_pos.mpr hL) _) (by exact_mod_cast d01CommonProduct_pos x)

theorem d01AtomicWeight_nonneg {L : ℝ} (hL : 0 ≤ L) (x : DiagonalSixIndices) :
    0 ≤ d01AtomicWeight L x := by
  unfold d01AtomicWeight
  exact div_nonneg (pow_nonneg (inv_nonneg.mpr hL) _) (Nat.cast_nonneg _)

theorem d01LogPoint_nonneg_left {L : ℝ} (hL : 0 < L)
    (x : DiagonalSixIndices) (i : Fin 3) : 0 ≤ (d01LogPoint L x).1 i := by
  apply div_nonneg _ hL.le
  apply Real.log_nonneg
  exact_mod_cast d01LeftIndices_pos x i

theorem d01LogPoint_nonneg_right {L : ℝ} (hL : 0 < L)
    (x : DiagonalSixIndices) (j : Fin 3) : 0 ≤ (d01LogPoint L x).2 j := by
  apply div_nonneg _ hL.le
  apply Real.log_nonneg
  exact_mod_cast d01RightIndices_pos x j

theorem d01LogPoint_mem_orthant {L : ℝ} (hL : 0 < L) (x : DiagonalSixIndices) :
    d01LogPoint L x ∈ d01PositiveOrthant :=
  ⟨d01LogPoint_nonneg_left hL x, d01LogPoint_nonneg_right hL x⟩

theorem d01PositiveOrthant_isClosed : IsClosed d01PositiveOrthant := by
  unfold d01PositiveOrthant
  have he : {y : D01LogSpace | (∀ i, 0 ≤ y.1 i) ∧ (∀ j, 0 ≤ y.2 j)} =
      ((⋂ i : Fin 3, {y : D01LogSpace | 0 ≤ y.1 i}) ∩
        (⋂ j : Fin 3, {y : D01LogSpace | 0 ≤ y.2 j})) := by
    ext y
    simp
  rw [he]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro i
    exact isClosed_le continuous_const (by fun_prop)
  · apply isClosed_iInter
    intro j
    exact isClosed_le continuous_const (by fun_prop)

theorem d01DiagonalMeasure_ae_orthant {L : ℝ} (hL : 0 < L) :
    ∀ᵐ y ∂d01DiagonalMeasure L, y ∈ d01PositiveOrthant := by
  rw [d01DiagonalMeasure, Measure.ae_sum_iff]
  intro x
  apply Measure.ae_smul_measure
  exact (ae_dirac_iff (d01PositiveOrthant_isClosed.measurableSet)).mpr
    (d01LogPoint_mem_orthant hL x)

theorem d01LaplaceWeight_pos (ab y : D01LogSpace) : 0 < d01LaplaceWeight ab y :=
  Real.exp_pos _

theorem d01LaplaceWeight_continuous (ab : D01LogSpace) :
    Continuous (d01LaplaceWeight ab) := by
  unfold d01LaplaceWeight
  fun_prop

theorem d01ComplexLaplaceWeight_continuous (ab : PolarShiftSpace) :
    Continuous (d01ComplexLaplaceWeight ab) := by
  unfold d01ComplexLaplaceWeight
  fun_prop

theorem d01DiagonalMeasure_integrable_iff {L : ℝ} (hL : 0 ≤ L)
    {E : Type*} [NormedAddCommGroup E] (f : D01LogSpace → E) :
    Integrable f (d01DiagonalMeasure L) ↔
      Summable (fun x : DiagonalSixIndices => d01AtomicWeight L x * ‖f (d01LogPoint L x)‖) := by
  simpa only [d01DiagonalMeasure, ENNReal.toReal_ofReal (d01AtomicWeight_nonneg hL _)] using
    (integrable_sum_dirac_iff (x := d01LogPoint L)
      (c := fun x => ENNReal.ofReal (d01AtomicWeight L x))
      (f := f) (fun _ => ENNReal.ofReal_ne_top))

theorem d01DiagonalMeasure_integral {L : ℝ} (hL : 0 ≤ L)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : D01LogSpace → E) :
    (∫ y, f y ∂d01DiagonalMeasure L) =
      ∑' x : DiagonalSixIndices, d01AtomicWeight L x • f (d01LogPoint L x) := by
  simpa only [d01DiagonalMeasure, ENNReal.toReal_ofReal (d01AtomicWeight_nonneg hL _)] using
    (integral_sum_dirac (x := d01LogPoint L)
      (c := fun x => ENNReal.ofReal (d01AtomicWeight L x))
      (f := f) (fun _ => ENNReal.ofReal_ne_top))

theorem d01DiagonalMeasure_lintegral (L : ℝ) (f : D01LogSpace → ℝ≥0∞) :
    (∫⁻ y, f y ∂d01DiagonalMeasure L) =
      ∑' x : DiagonalSixIndices,
        ENNReal.ofReal (d01AtomicWeight L x) * f (d01LogPoint L x) := by
  simp only [d01DiagonalMeasure, lintegral_sum_measure,
    lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

end
end Sechstmoment
