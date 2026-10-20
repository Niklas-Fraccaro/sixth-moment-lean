import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import SixthMoment.Analysis.Measures.ExponentialTilt
import SixthMoment.Denominator.Measures.DiagonalMeasureDefinitions

namespace SixthMoment
open MeasureTheory Complex
open scoped BigOperators RealInnerProductSpace
noncomputable section

abbrev D01EuclideanSpace := EuclideanSpace ℝ (Fin 3 ⊕ Fin 3)

def d01LogEuclideanHomeomorph : D01LogSpace ≃ₜ D01EuclideanSpace :=
  (Homeomorph.sumArrowHomeomorphProdArrow (X := ℝ)).symm.trans
    (EuclideanSpace.equiv (Fin 3 ⊕ Fin 3) ℝ).toHomeomorph.symm

@[simp] theorem d01LogEuclideanHomeomorph_inl (y : D01LogSpace) (i : Fin 3) :
    d01LogEuclideanHomeomorph y (Sum.inl i) = y.1 i := rfl

@[simp] theorem d01LogEuclideanHomeomorph_inr (y : D01LogSpace) (i : Fin 3) :
    d01LogEuclideanHomeomorph y (Sum.inr i) = y.2 i := rfl

def d01LogTotal (y : D01LogSpace) : ℝ := ∑ i, y.1 i + ∑ j, y.2 j

@[fun_prop] theorem d01LogTotal_continuous : Continuous d01LogTotal := by
  unfold d01LogTotal
  fun_prop

def d01FourierShifts (t : D01EuclideanSpace) : PolarShiftSpace :=
  (fun i => 1 - (t (Sum.inl i) : ℂ) * I,
   fun j => 1 - (t (Sum.inr j) : ℂ) * I)

@[simp] theorem d01FourierShifts_fst_re (t : D01EuclideanSpace) (i : Fin 3) :
    ((d01FourierShifts t).1 i).re = 1 := by simp [d01FourierShifts]

@[simp] theorem d01FourierShifts_snd_re (t : D01EuclideanSpace) (i : Fin 3) :
    ((d01FourierShifts t).2 i).re = 1 := by simp [d01FourierShifts]

theorem d01ComplexLaplaceWeight_fourier (t : D01EuclideanSpace) (y : D01LogSpace) :
    d01ComplexLaplaceWeight (d01FourierShifts t) y =
      (Real.exp (-d01LogTotal y) : ℂ) *
        Complex.exp ((⟪d01LogEuclideanHomeomorph y, t⟫ : ℝ) * I) := by
  unfold d01ComplexLaplaceWeight
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [d01FourierShifts, d01LogTotal,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fintype.sum_sum_type,
    d01LogEuclideanHomeomorph_inl, d01LogEuclideanHomeomorph_inr,
    Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul]
  simp_rw [sub_mul, one_mul, Finset.sum_sub_distrib]
  simp_rw [mul_assoc, mul_comm I, ← mul_assoc]
  simp only [← Finset.sum_mul]
  ring

theorem d01ExponentialTilt_charFun (μ : Measure D01LogSpace) (t : D01EuclideanSpace) :
    charFun (Measure.map d01LogEuclideanHomeomorph
      (d01ExponentialTilt μ d01LogTotal)) t =
        ∫ y, d01ComplexLaplaceWeight (d01FourierShifts t) y ∂μ := by
  rw [charFun_apply, integral_map_of_stronglyMeasurable
    d01LogEuclideanHomeomorph.continuous.measurable (by fun_prop)]
  rw [d01ExponentialTilt, integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun y => ENNReal.ofReal (Real.exp (-d01LogTotal y))) by fun_prop)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  exact (d01ComplexLaplaceWeight_fourier t y).symm

end
end SixthMoment
