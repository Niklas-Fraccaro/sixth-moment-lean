import Sechstmoment.Analysis.Measures.Levy
import Sechstmoment.Denominator.Measures.DiagonalMeasureFinite
import Sechstmoment.Denominator.Measures.EuclideanLaplace
import Sechstmoment.Denominator.Measures.LimitMeasureIntegral


namespace Sechstmoment
open MeasureTheory Filter Set
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 0

theorem d01DiagonalMeasure_fixedTilt_finite {L : ℝ} (hL : 0 < L) :
    IsFiniteMeasure (d01ExponentialTilt (d01DiagonalMeasure L) d01LogTotal) := by
  simpa only [d01ExponentialTilt, d01LogTotal, d01LaplaceWeight, one_mul] using
    d01DiagonalMeasure_finite_laplace_density hL ((fun _ => 1), (fun _ => 1))
      (by intro i; norm_num) (by intro j; norm_num)

theorem d01LimitMeasure_fixedTilt_finite :
    IsFiniteMeasure (d01ExponentialTilt d01LimitMeasure d01LogTotal) := by
  simpa only [d01ExponentialTilt, d01LogTotal, d01TiltedLimitMeasure, d01LaplaceWeight,
    one_mul] using
    d01TiltedLimitMeasure_finite ((fun _ => 1), (fun _ => 1))
      (by intro i; norm_num) (by intro j; norm_num)

def d01TiltedDiagonalFiniteMeasure (L : ℝ) : FiniteMeasure D01LogSpace :=
  if hL : 0 < L then
    ⟨d01ExponentialTilt (d01DiagonalMeasure L) d01LogTotal,
      d01DiagonalMeasure_fixedTilt_finite hL⟩ else 0

def d01TiltedLimitFiniteMeasure : FiniteMeasure D01LogSpace :=
  ⟨d01ExponentialTilt d01LimitMeasure d01LogTotal, d01LimitMeasure_fixedTilt_finite⟩

theorem d01TiltedDiagonalFiniteMeasure_toMeasure {L : ℝ} (hL : 0 < L) :
    (d01TiltedDiagonalFiniteMeasure L : Measure D01LogSpace) =
      d01ExponentialTilt (d01DiagonalMeasure L) d01LogTotal := by
  have he : d01TiltedDiagonalFiniteMeasure L =
      (⟨d01ExponentialTilt (d01DiagonalMeasure L) d01LogTotal,
        d01DiagonalMeasure_fixedTilt_finite hL⟩ : FiniteMeasure D01LogSpace) := by
    exact dite_eq_left hL
  exact congrArg FiniteMeasure.toMeasure he

theorem d01TiltedLimitFiniteMeasure_toMeasure :
    (d01TiltedLimitFiniteMeasure : Measure D01LogSpace) =
      d01ExponentialTilt d01LimitMeasure d01LogTotal := rfl

theorem d01TiltedLimitFiniteMeasure_ne_zero : d01TiltedLimitFiniteMeasure ≠ 0 := by
  intro hz
  have hzM : d01ExponentialTilt d01LimitMeasure d01LogTotal = 0 := by
    have h := congrArg FiniteMeasure.toMeasure hz
    simpa only [d01TiltedLimitFiniteMeasure_toMeasure, FiniteMeasure.toMeasure_zero] using h
  have hzν : d01LimitMeasure = 0 := by
    apply d01ExponentialTilt_injective d01LogTotal d01LogTotal_continuous.measurable
    simpa only [d01ExponentialTilt, withDensity_zero_left] using hzM
  have he := d01LimitMeasure_laplace ((fun _ => 1), (fun _ => 1))
    (by intro i; norm_num) (by intro j; norm_num)
  rw [hzν, integral_zero_measure] at he
  have hp : 0 < arithmeticFactor *
      ∏ _ij : Fin 3 × Fin 3, ((1 : ℝ)+1)⁻¹ := by
    apply mul_pos arithmeticFactor_wellDefined.2
    apply Finset.prod_pos
    intro ij _
    norm_num
  exact (ne_of_gt hp) he.symm

theorem d01TiltedDiagonalFiniteMeasure_charFun_tendsto (t : D01EuclideanSpace) :
    Tendsto (fun L : ℝ => charFun
      ((d01TiltedDiagonalFiniteMeasure L).map d01LogEuclideanHomeomorph :
        Measure D01EuclideanSpace) t) atTop
      (𝓝 (charFun (d01TiltedLimitFiniteMeasure.map d01LogEuclideanHomeomorph :
        Measure D01EuclideanSpace) t)) := by
  have ha : ∀ i, 0 < ((d01FourierShifts t).1 i).re := by intro i; simp
  have hb : ∀ j, 0 < ((d01FourierShifts t).2 j).re := by intro j; simp
  have hlim := d01LimitMeasure_complexLaplace (d01FourierShifts t) ha hb
  simp only [← one_div] at hlim
  have h := d01DiagonalMeasure_complexLaplace_tendsto
    (d01FourierShifts t).1 (d01FourierShifts t).2 ha hb
  rw [← hlim] at h
  have hν : charFun (d01TiltedLimitFiniteMeasure.map d01LogEuclideanHomeomorph :
      Measure D01EuclideanSpace) t =
        ∫ y, d01ComplexLaplaceWeight (d01FourierShifts t) y ∂d01LimitMeasure := by
    rw [FiniteMeasure.toMeasure_map, d01TiltedLimitFiniteMeasure_toMeasure]
    exact d01ExponentialTilt_charFun _ _
  rw [hν]
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  rw [FiniteMeasure.toMeasure_map, d01TiltedDiagonalFiniteMeasure_toMeasure hL]
  exact (d01ExponentialTilt_charFun _ _).symm

theorem d01TiltedDiagonalFiniteMeasure_mass_tendsto :
    Tendsto (fun L : ℝ => (d01TiltedDiagonalFiniteMeasure L).mass) atTop
      (𝓝 d01TiltedLimitFiniteMeasure.mass) := by
  have h := d01TiltedDiagonalFiniteMeasure_charFun_tendsto 0
  simp only [charFun_zero] at h
  have hr := Complex.continuous_re.continuousAt.tendsto.comp h
  simp only [Function.comp_def, Complex.ofReal_re] at hr
  change Tendsto (fun L : ℝ =>
    (((d01TiltedDiagonalFiniteMeasure L).map d01LogEuclideanHomeomorph).mass : ℝ))
      atTop (𝓝 (((d01TiltedLimitFiniteMeasure.map d01LogEuclideanHomeomorph).mass : ℝ))) at hr
  simp only [d01_finiteMeasure_mass_map_homeomorph] at hr
  exact NNReal.tendsto_coe.mp hr

theorem d01DiagonalMeasure_tilted_tendsto :
    Tendsto d01TiltedDiagonalFiniteMeasure atTop (𝓝 d01TiltedLimitFiniteMeasure) := by
  exact d01_finiteMeasure_tendsto_of_mapped_charFun d01LogEuclideanHomeomorph
    d01TiltedLimitFiniteMeasure_ne_zero d01TiltedDiagonalFiniteMeasure_mass_tendsto
    d01TiltedDiagonalFiniteMeasure_charFun_tendsto

end
end Sechstmoment
