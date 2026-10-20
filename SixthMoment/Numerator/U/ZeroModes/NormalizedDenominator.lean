import SixthMoment.Numerator.U.ZeroModes.PhysicalBound

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section

theorem a03ZeroModeRealQuadDenominator_normalized_inv_norm_le
    {T C κ R : ℝ} (hT : 0<T) (hlog : 1≤Real.log T) (hC : 1≤C) (hR : 0≤R)
    (α : MomentShifts) (hα : ∀ j,‖α j‖≤R/Real.log T) (z : ℂ) (hz : 0≤z.re)
    (x : Fin 4→ℝ) (hx : ∀ j,1≤x j) (hcut : (∏ j : Fin 4,x j)≤C*T^κ) :
    ‖(a03ZeroModeRealQuadDenominator α z x)⁻¹‖≤
      Real.exp (R*(Real.log C+κ))/Real.sqrt (∏ j : Fin 4,x j) := by
  have hprod : 0<∏ j : Fin 4,x j := Finset.prod_pos (fun j _ => zero_lt_one.trans_le (hx j))
  calc
    _≤(∏ j : Fin 4,x j)^(R/Real.log T)/Real.sqrt (∏ j : Fin 4,x j) :=
      a03ZeroModeRealQuadDenominator_inv_norm_le_product α z hz x hx (fun j =>
        (abs_le.mp ((Complex.abs_re_le_norm _).trans (hα j))).1)
    _≤_ := div_le_div_of_nonneg_right
      (bblrRawShift_product_rpow_le hT hlog hC hR hprod hcut) (Real.sqrt_nonneg _)

end
end SixthMoment
