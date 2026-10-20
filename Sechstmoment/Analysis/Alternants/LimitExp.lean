import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Instances.Matrix
import Sechstmoment.Analysis.Alternants.Confluent


namespace Sechstmoment
open scoped Topology

set_option maxHeartbeats 0

noncomputable def expFirstSlope (q : ℂ) : ℂ → ℂ :=
  dslope (fun t : ℂ => Complex.exp (t*q)) 0

noncomputable def expSecondSlope (q : ℂ) : ℂ → ℂ := dslope (expFirstSlope q) 0

theorem expFirstSlope_zero (q : ℂ) : expFirstSlope q 0 = q := by
  unfold expFirstSlope
  rw [dslope_same]
  have hd := (Complex.hasDerivAt_exp (0*q)).comp 0
    ((hasDerivAt_id (0 : ℂ)).mul_const q)
  simpa only [Function.comp_def, id_eq, zero_mul, Complex.exp_zero, one_mul] using hd.deriv

theorem expFirstSlope_of_ne (q t : ℂ) (ht : t ≠ 0) :
    expFirstSlope q t = (Complex.exp (t*q)-1)/t := by
  simp [expFirstSlope, dslope_of_ne _ ht, slope_def_field]

theorem expFirstSlope_continuous (q : ℂ) : Continuous (expFirstSlope q) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t = 0
  · subst t
    exact continuousAt_dslope_same.mpr (by fun_prop)
  · exact (continuousAt_dslope_of_ne ht).mpr (by fun_prop)

theorem expScaled_powerSeries (q : ℂ) :
    HasFPowerSeriesAt (fun t : ℂ => Complex.exp (t*q))
      ((NormedSpace.expSeries ℂ ℂ).compContinuousLinearMap
        (q • ContinuousLinearMap.id ℂ ℂ)) 0 := by
  have h := (NormedSpace.exp_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt NormedSpace.exp (NormedSpace.expSeries ℂ ℂ) 0)
  have h' : HasFPowerSeriesAt NormedSpace.exp (NormedSpace.expSeries ℂ ℂ)
      ((q • ContinuousLinearMap.id ℂ ℂ) 0) := by simpa using h
  simpa [Complex.exp_eq_exp_ℂ, Function.comp_def, smul_eq_mul, mul_comm] using
    h'.compContinuousLinearMap

theorem expSecondSlope_zero (q : ℂ) : expSecondSlope q 0 = q^2/2 := by
  have hp := (expScaled_powerSeries q).has_fpower_series_dslope_fslope.has_fpower_series_dslope_fslope
  have hc : (((NormedSpace.expSeries ℂ ℂ).compContinuousLinearMap
      (q • ContinuousLinearMap.id ℂ ℂ)).fslope.fslope).coeff 0 =
      expSecondSlope q 0 := hp.coeff_zero 1
  rw [← hc]
  rw [FormalMultilinearSeries.coeff_fslope, FormalMultilinearSeries.coeff_fslope]
  simp [FormalMultilinearSeries.coeff, FormalMultilinearSeries.compContinuousLinearMap,
    NormedSpace.expSeries_apply_eq, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    smul_eq_mul, div_eq_mul_inv, mul_comm, -FormalMultilinearSeries.apply_eq_prod_smul_coeff]

theorem expSecondSlope_of_ne (q t : ℂ) (ht : t ≠ 0) :
    expSecondSlope q t = (Complex.exp (t*q)-1-t*q)/t^2 := by
  rw [expSecondSlope, dslope_of_ne _ ht, slope_def_field,
    expFirstSlope_zero, expFirstSlope_of_ne _ _ ht]
  simp only [sub_zero]
  field_simp

theorem expSecondSlope_continuous (q : ℂ) : Continuous (expSecondSlope q) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t = 0
  · subst t
    apply continuousAt_dslope_same.mpr
    exact (expScaled_powerSeries q).has_fpower_series_dslope_fslope.differentiableAt
  · exact (continuousAt_dslope_of_ne ht).mpr (expFirstSlope_continuous q).continuousAt

end Sechstmoment
