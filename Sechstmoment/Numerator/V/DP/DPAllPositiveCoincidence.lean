import Sechstmoment.Numerator.Polar.WeightedCoincidence
import Sechstmoment.Numerator.V.DP.DPAllPositiveBoundary
import Sechstmoment.Numerator.V.DP.DPAllPositiveHolomorphy

/-! A genuine DP moment asymptotic at coincident shifts, with its actual
polynomial polar generator. The only external input is the literal sharp
DP-v2 estimate; all functional equations, smoothing, holomorphy and collision
transfer are theorems of the present formalization. -/

namespace Sechstmoment.Source
open Complex MeasureTheory Set Polynomial Filter
open scoped Topology
noncomputable section

theorem dpAllPositiveMoment_coincident_uniform_smoothing (hsource : DPv2SharpInput)
    (η : ℝ) (hη : 0 < η) (hηu : η < 1/4) (P : ℝ[X]) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ σ ∈ rectangularClosedPolydisc dpCauchyRadii,
      ∀ Φ : ℝ → ℝ, SmoothDyadicWeight Φ → WeightSeminormBound 1 B Φ →
      ‖dpAllPositiveMoment T η P σ Φ-
        (T : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*dpAllPositiveRegularLeadingDensity T η P σ‖ ≤
          C*T*(Real.log T)^8 := by
  obtain ⟨C,hC,hbound⟩ := dpAllPositiveMoment_regular_boundary_bound hsource η hη hηu P B hB
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16 : ℝ))]
    with T hbound hT hL σ hσ Φ hΦ hseminorm
  have hR : ∀ j, 2*dpCauchyRadii j < Real.log T := by
    intro j
    have hr : dpCauchyRadii j ≤ (8 : ℝ) := by fin_cases j <;> norm_num [dpCauchyRadii]
    linarith
  have hm := dpAllPositiveMoment_differentiableOn_polydisc hT dpCauchyRadii hR η P Φ hΦ
  have hf := hm.sub ((dpAllPositiveRegularLeadingDensity_differentiableOn hη.le T P).const_mul
    ((T : ℂ)*(∫ x : ℝ, (Φ x : ℂ))))
  exact rectangular_polydisc_norm_le dpCauchyRadii dpCauchyRadii_positive _ hf
    (fun τ hτ => hbound τ hτ Φ hΦ hseminorm) σ hσ

theorem dpAllPositiveMoment_coincident_normalized_tendsto (hsource : DPv2SharpInput)
    (η : ℝ) (hη : 0 < η) (hηu : η < 1/4) (P : ℝ[X])
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (σ : MomentShifts)
    (hσ : σ ∈ rectangularClosedPolydisc dpCauchyRadii) :
    Tendsto (fun T : ℝ => dpAllPositiveMoment T η P σ Φ/
      ((T : ℂ)*(Real.log T : ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*dpAllPositiveRegularKernel η P σ)) := by
  obtain ⟨B,hB,hseminorm⟩ := smoothDyadicWeight_seminorm_one_bound Φ hΦ
  obtain ⟨C,_,hbound⟩ := dpAllPositiveMoment_coincident_uniform_smoothing hsource η hη hηu P B hB
  let E : ℝ → ℂ := fun T => dpAllPositiveMoment T η P σ Φ-
    (T : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*dpAllPositiveRegularLeadingDensity T η P σ
  have hE := logNormalizedRemainder_tendsto E C
    (hbound.mono (fun T h => h σ hσ Φ hΦ hseminorm))
  have ht := (tendsto_const_nhds (x := (arithmeticFactor : ℂ)*
    (∫ x : ℝ, (Φ x : ℂ))*dpAllPositiveRegularKernel η P σ)).add hE
  simp only [add_zero] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  have hT0 : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hT).ne'
  have hL0 : (Real.log T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hT).ne'
  dsimp [E,dpAllPositiveRegularLeadingDensity]
  field_simp
  ring

/-- The actual one-variable coincident tuple used for the polar numerator. -/
def dpCoincidentShifts (z : ℂ) : MomentShifts := ![0,0,-z,0]

theorem dpCoincidentShifts_differentiable : Differentiable ℂ dpCoincidentShifts := by
  apply differentiable_pi.mpr
  intro j
  fin_cases j
  · change Differentiable ℂ (fun _ : ℂ => (0 : ℂ))
    fun_prop
  · change Differentiable ℂ (fun _ : ℂ => (0 : ℂ))
    fun_prop
  · change Differentiable ℂ (fun z : ℂ => -z)
    fun_prop
  · change Differentiable ℂ (fun _ : ℂ => (0 : ℂ))
    fun_prop

theorem dpCoincidentShifts_mem_polydisc {z : ℂ} (hz : ‖z‖ ≤ 4) :
    dpCoincidentShifts z ∈ rectangularClosedPolydisc dpCauchyRadii := by
  intro j
  fin_cases j <;> simp [dpCoincidentShifts,dpCauchyRadii,hz]

/-- The exponential from the exact functional equations cancels the source
outer-contour phase. This equality includes z=0. -/
theorem dpAllPositiveRegularKernel_coincident (η : ℝ) (P : ℝ[X]) (z : ℂ)
    (hz : ‖z‖ < 16) :
    dpAllPositiveRegularKernel η P (dpCoincidentShifts z) = polarPolynomialJ η P z := by
  have hknots : polarSourceKnots (dpCoincidentShifts z) = ![0,0,-z,0] := by
    funext j
    fin_cases j <;> simp [polarSourceKnots,dpCoincidentShifts]
  unfold dpAllPositiveRegularKernel dpRegularKernel
  rw [hknots,polarGeneralGeneratorContour_coincident η P z 16 16 hz hz]
  change Complex.exp (-z+0)*(Complex.exp z*polarPolynomialJ η P z)=_
  rw [add_zero,← mul_assoc,← Complex.exp_add]
  simp

/-- The genuine all-positive moment tends to the actual polynomial polar
generator for coincident shifts, including z=0, after T log^9(T) normalization. -/
theorem dpAllPositiveMoment_polarPolynomialJ_tendsto (hsource : DPv2SharpInput)
    (η : ℝ) (hη : 0 < η) (hηu : η < 1/4) (P : ℝ[X])
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (z : ℂ) (hz : ‖z‖ ≤ 4) :
    Tendsto (fun T : ℝ => dpAllPositiveMoment T η P (dpCoincidentShifts z) Φ/
      ((T : ℂ)*(Real.log T : ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*polarPolynomialJ η P z)) := by
  have h := dpAllPositiveMoment_coincident_normalized_tendsto hsource η hη hηu P Φ hΦ
    (dpCoincidentShifts z) (dpCoincidentShifts_mem_polydisc hz)
  rw [dpAllPositiveRegularKernel_coincident η P z (by linarith)] at h
  exact h

end
end Sechstmoment.Source
