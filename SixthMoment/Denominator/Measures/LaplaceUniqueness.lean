import SixthMoment.Analysis.Measures.Levy
import SixthMoment.Denominator.Measures.EuclideanLaplace

namespace SixthMoment
open MeasureTheory
noncomputable section

theorem d01_measure_eq_of_complexLaplace (μ ν : Measure D01LogSpace)
    (hμ : IsFiniteMeasure (d01ExponentialTilt μ d01LogTotal))
    (hν : IsFiniteMeasure (d01ExponentialTilt ν d01LogTotal))
    (heq : ∀ ab : PolarShiftSpace,
      (∀ i, 0 < (ab.1 i).re) → (∀ j, 0 < (ab.2 j).re) →
      (∫ y, d01ComplexLaplaceWeight ab y ∂μ) = ∫ y, d01ComplexLaplaceWeight ab y ∂ν) :
    μ = ν := by
  let m : FiniteMeasure D01LogSpace := ⟨d01ExponentialTilt μ d01LogTotal, hμ⟩
  let n : FiniteMeasure D01LogSpace := ⟨d01ExponentialTilt ν d01LogTotal, hν⟩
  have hm : m = n := d01_finiteMeasure_eq_of_mapped_charFun
    d01LogEuclideanHomeomorph m n (fun t => by
      change charFun (Measure.map d01LogEuclideanHomeomorph
        (d01ExponentialTilt μ d01LogTotal)) t =
          charFun (Measure.map d01LogEuclideanHomeomorph
            (d01ExponentialTilt ν d01LogTotal)) t
      rw [d01ExponentialTilt_charFun, d01ExponentialTilt_charFun]
      exact heq (d01FourierShifts t) (by intro i; simp) (by intro j; simp))
  apply d01ExponentialTilt_injective d01LogTotal d01LogTotal_continuous.measurable
  exact congrArg Subtype.val hm

end
end SixthMoment
