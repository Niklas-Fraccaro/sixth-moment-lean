import Sechstmoment.Analysis.Complex.CauchyBounds
import Sechstmoment.Arithmetic.QuadraticDivisor.Definitions
import Sechstmoment.Numerator.V.DP.DPCoincidentTransfer

namespace Sechstmoment
open Complex Set Metric Filter MeasureTheory Polynomial
open scoped Topology
noncomputable section

def momentShiftLine (v : MomentShifts) (z : ℂ) : MomentShifts := fun j => z*v j

theorem momentShiftLine_differentiable (v : MomentShifts) :
    Differentiable ℂ (momentShiftLine v) := by
  unfold momentShiftLine
  apply differentiable_pi.mpr
  intro j
  fun_prop

theorem momentShiftLine_mem_polydisc (R : Fin 4 → ℝ) (v : MomentShifts)
    (hv : v ∈ rectangularClosedPolydisc R) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    momentShiftLine v z ∈ rectangularClosedPolydisc R := by
  intro j
  change ‖z*v j‖ ≤ R j
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg (v j)) hz).trans (hv j)

theorem shiftLine_cauchy_polydisc_bound (n : ℕ) (R : Fin 4 → ℝ)
    (v : MomentShifts) (hv : v ∈ rectangularClosedPolydisc R)
    (f : MomentShifts → ℂ) (hf : DifferentiableOn ℂ f (rectangularClosedPolydisc R))
    {M : ℝ} (hbound : ∀ σ ∈ rectangularClosedPolydisc R, ‖f σ‖ ≤ M) :
    ‖iteratedDeriv n (fun z => f (momentShiftLine v z)) 0‖ ≤ (n.factorial : ℝ)*M := by
  have hdiff : DifferentiableOn ℂ (fun z => f (momentShiftLine v z)) (closedBall 0 1) :=
    hf.comp (momentShiftLine_differentiable v).differentiableOn (by
      intro z hz
      apply momentShiftLine_mem_polydisc R v hv
      simpa only [mem_closedBall,dist_zero_right] using hz)
  have hc := cauchy_iteratedDeriv_bound n (by norm_num : (0:ℝ)<1)
    (hdiff.diffContOnCl_ball Subset.rfl) (fun z hz => hbound _
      (momentShiftLine_mem_polydisc R v hv (by
        simpa only [mem_sphere,dist_zero_right] using le_of_eq hz)))
  simpa only [one_pow,div_one] using hc

namespace Source

def dpActualMomentShiftLineError (T η : ℝ) (P : ℝ[X]) (Φ : ℝ → ℝ)
    (v : MomentShifts) (z : ℂ) : ℂ :=
  chiTwistedFourthMoment T (rawMomentShifts T (momentShiftLine v z))
    (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) Φ-
    (T : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*dpRegularLeadingDensity T η P (momentShiftLine v z)

theorem dpActualMoment_shiftLine_uniform_derivative_bound (n : ℕ)
    (hsource : DPv2SharpInput) (η : ℝ) (hη : 0 < η) (hηu : η < 1/4)
    (P : ℝ[X]) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ v ∈ rectangularClosedPolydisc dpCauchyRadii,
      ∀ Φ : ℝ → ℝ, SmoothDyadicWeight Φ → (∀ x, |deriv Φ x| ≤ B) →
      ‖iteratedDeriv n (dpActualMomentShiftLineError T η P Φ v) 0‖ ≤
        C*T*(Real.log T)^8 := by
  obtain ⟨C,hC,hbound⟩ := dpActualMoment_coincident_uniform_smoothing hsource η hη hηu P B hB
  refine ⟨(n.factorial : ℝ)*C,mul_nonneg (by positivity) hC,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16 : ℝ))]
    with T hbound hT hL v hv Φ hΦ hderiv
  have hR : ∀ j, 2*dpCauchyRadii j < Real.log T := by
    intro j
    have hr : dpCauchyRadii j ≤ (8 : ℝ) := by fin_cases j <;> norm_num [dpCauchyRadii]
    linarith
  have hm := chiTwistedFourthMoment_differentiableOn_polydisc hT dpCauchyRadii hR
    η η (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) Φ
    (dpProfile_zero_above η P) (dpProfile_zero_above η P) hΦ
  have hf := hm.sub ((dpRegularLeadingDensity_differentiableOn hη.le T P).const_mul
    ((T : ℂ)*(∫ x : ℝ, (Φ x : ℂ))))
  have hh := shiftLine_cauchy_polydisc_bound n dpCauchyRadii v hv _ hf
    (fun σ hσ => hbound σ hσ Φ hΦ hderiv)
  change ‖iteratedDeriv n (dpActualMomentShiftLineError T η P Φ v) 0‖ ≤ _ at hh
  convert hh using 1; ring

end Source
end
end Sechstmoment
