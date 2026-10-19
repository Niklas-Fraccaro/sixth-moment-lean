import Sechstmoment.Numerator.V.Contour.ShiftedChiFactor
import Sechstmoment.Numerator.V.PolynomialDefinitions

/-! Exact identification of the actual V generator with a single shifted chi
moment. The phase and the original polynomial amplifiers are retained. -/

namespace Sechstmoment.Source
open Complex Real Set MeasureTheory
open scoped BigOperators
noncomputable section

def noDPVSingleChiShifts (u : ℂ) : Fin 4 → ℂ := ![0,0,0,-u]

theorem noDPVSingleChiShifts_norm (u : ℂ) (j : Fin 4) :
    ‖noDPVSingleChiShifts u j‖ ≤ ‖u‖ := by
  fin_cases j <;> simp [noDPVSingleChiShifts]

theorem vPolynomialMixedIntegrand_single_chi (T t : ℝ) (f g Φ : ℝ → ℝ) (z : ℂ)
    (hu : ‖z/(Real.log T:ℂ)‖ ≤ 1/8) :
    vPolynomialMixedAmplitude T f g Φ t*zetaCMinus T t z =
      Complex.exp (z/2)*(shiftedChiProfileFactor T (z/(Real.log T:ℂ))
        (noDPVSingleChiShifts (z/(Real.log T:ℂ))) f g (criticalLinePoint t)*(Φ (t/T):ℂ)) := by
  have hre := abs_le.mp ((Complex.abs_re_le_norm (z/(Real.log T:ℂ))).trans hu)
  have hlo : 0 < (1-criticalLinePoint t+z/(Real.log T:ℂ)).re := by
    simp only [add_re,sub_re,one_re,criticalLinePoint_re]
    linarith [hre.1]
  have hhi : (1-criticalLinePoint t+z/(Real.log T:ℂ)).re < 1 := by
    simp only [add_re,sub_re,one_re,criticalLinePoint_re]
    linarith [hre.2]
  unfold vPolynomialMixedAmplitude zetaCMinus shiftedZetaGenerator
  rw [riemannZeta_strip_functional_equation hlo hhi,
    show 1-(1-criticalLinePoint t+z/(Real.log T:ℂ)) =
      criticalLinePoint t-z/(Real.log T:ℂ) by ring]
  simp only [shiftedChiProfileFactor,shiftedChiZetaFactor]
  simp [noDPVSingleChiShifts,Fin.prod_univ_succ,sub_eq_add_neg]
  ring

theorem vPolynomialMixedGenerator_single_chi (T : ℝ) (f g Φ : ℝ → ℝ) (z : ℂ)
    (hu : ‖z/(Real.log T:ℂ)‖ ≤ 1/8) :
    vPolynomialMixedGenerator T f g Φ z =
      Complex.exp (z/2)*(∫ t : ℝ, shiftedChiProfileFactor T (z/(Real.log T:ℂ))
        (noDPVSingleChiShifts (z/(Real.log T:ℂ))) f g (criticalLinePoint t)*(Φ (t/T):ℂ)) := by
  unfold vPolynomialMixedGenerator
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall
    (fun t => vPolynomialMixedIntegrand_single_chi T t f g Φ z hu))

end
end Sechstmoment.Source
