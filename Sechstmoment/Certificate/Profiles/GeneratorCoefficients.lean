import Sechstmoment.Certificate.Exact.RowIntegral
import Sechstmoment.Numerator.Kernels.GeneratorDerivatives

/-! The actual centered/polar generator operators for the 250 original
certificate rows agree with the independently computed exact numerator. -/

namespace Sechstmoment
open _root_.Sechstmoment.Finite
open scoped BigOperators
noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Concrete endpoint geometry of the supplied original certificate. -/
theorem certificate_numerator_generator_geometry : ∀ d ∈ certificate,
    0 < d.A ∧ 0 < d.B ∧ d.A+d.B < Finite.base := by decide +kernel

def datumNumeratorGenerator (d : TestDatum) : ℂ → ℂ :=
  if d.typ = .U then
    numeratorExpGenerator ((d.A:ℝ)/(Finite.base:ℝ)) ((d.B:ℝ)/(Finite.base:ℝ))
  else
    reflectedPolarGenerator ((d.A:ℝ)/(Finite.base:ℝ)) ((d.B:ℝ)/(Finite.base:ℝ))

def datumNumeratorDifferentialValue (d : TestDatum) : ℂ :=
  ((d.coefficient:ℝ):ℂ)*finiteDifferentialOperator 4
    (fun r => ((coef (cheb d.degree) r.val:ℝ):ℂ)) (datumNumeratorGenerator d) 0

theorem datumNumeratorDifferentialValue_eq_pointKernel {d : TestDatum}
    (hd : d ∈ certificate) :
    datumNumeratorDifferentialValue d = Complex.ofReal ((d.coefficient:ℝ)*
      numeratorPointKernel (fun r => (coef (cheb d.degree) r.val:ℝ))
        ((d.A:ℝ)/(Finite.base:ℝ))
        ((numeratorSecondMass (datumFeature d):ℝ)/(Finite.base:ℝ))) := by
  unfold datumNumeratorDifferentialValue datumNumeratorGenerator
  by_cases htype : d.typ = .U
  · rw [ite_eq_left htype,numeratorExpGenerator_operator_eq_pointKernel]
    simp only [Complex.ofReal_mul]
    congr 1
    simp [numeratorSecondMass,datumFeature,htype]
  · obtain ⟨hA,hB,hAB⟩ := certificate_numerator_generator_geometry d hd
    have hbase : (0:ℝ) < (Finite.base:ℝ) := by norm_num [Finite.base]
    have ha : 0 < (d.A:ℝ)/(Finite.base:ℝ) :=
      div_pos (by exact_mod_cast hA) hbase
    have hb : 0 < (d.B:ℝ)/(Finite.base:ℝ) :=
      div_pos (by exact_mod_cast hB) hbase
    have hab : (d.A:ℝ)/(Finite.base:ℝ)+(d.B:ℝ)/(Finite.base:ℝ) < 1 := by
      rw [← add_div]
      apply (div_lt_one hbase).mpr
      exact_mod_cast hAB
    have hBbase : d.B ≤ Finite.base := by omega
    have hfrac : 1-(d.B:ℝ)/(Finite.base:ℝ) =
        ((Finite.base-d.B:ℕ):ℝ)/(Finite.base:ℝ) := by
      rw [Nat.cast_sub hBbase]
      field_simp
    rw [ite_eq_right htype,reflectedPolarGenerator_operator_eq_pointKernel _ _ _ ha hb hab]
    simp only [Complex.ofReal_mul]
    congr 1
    rw [hfrac]
    simp [numeratorSecondMass,datumFeature,htype]

def certificateNumeratorDifferentialValue : ℂ :=
  (certificate.map datumNumeratorDifferentialValue).sum

/-- The full original 250-row numerical numerator is obtained from actual
generator differential operators; the integer evaluator is not assumed to
describe these generators. -/
theorem certificateNumeratorDifferentialValue_eq_finite :
    certificateNumeratorDifferentialValue = (finiteNumerator:ℂ) := by
  let F : TestDatum → ℝ := fun d => (d.coefficient:ℝ)*
    numeratorPointKernel (fun r => (coef (cheb d.degree) r.val:ℝ))
      ((d.A:ℝ)/(Finite.base:ℝ))
      ((numeratorSecondMass (datumFeature d):ℝ)/(Finite.base:ℝ))
  have hcast (l : List ℝ) : (l.map Complex.ofReal).sum = Complex.ofReal l.sum := by
    induction l with
    | nil => simp
    | cons x xs ih => simp only [List.map_cons,List.sum_cons,Complex.ofReal_add,ih]
  calc
    _ = (certificate.map (fun d => Complex.ofReal (F d))).sum := by
      unfold certificateNumeratorDifferentialValue
      apply congrArg List.sum
      apply List.map_congr_left
      intro d hd
      exact datumNumeratorDifferentialValue_eq_pointKernel hd
    _ = Complex.ofReal (certificate.map F).sum := by
      simpa only [List.map_map,Function.comp_def] using hcast (certificate.map F)
    _ = _ := by
      have h : (certificate.map F).sum = (finiteNumerator:ℝ) := original_numerator_sum_250
      rw [h]
      norm_cast

theorem certificateNumeratorDifferentialValue_re_gt_lower :
    (46159:ℝ) < certificateNumeratorDifferentialValue.re := by
  rw [certificateNumeratorDifferentialValue_eq_finite]
  exact_mod_cast finite_numerator_gt_lower

end
end Sechstmoment
