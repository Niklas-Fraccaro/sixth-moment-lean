import Sechstmoment.Numerator.U.ZeroModes.RatioTimeFourierContour

/-! The literal ratio/time Fourier mode equals its genuine positive-line
Mellin contour, including power profiles for the actual dual branch. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 700000

theorem a03RatioTimeFourierMode_integrable_eq {Φ : ℝ→ℂ} (hΦ : Continuous Φ)
    (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) {c : ℝ} (hc : 0<c) (T : ℝ) (σ : MomentShifts)
    (A b ξ : ℝ) (ρ : ℂ) :
    Integrable (a03RatioTimeFourierMode Φ T σ A b ξ ρ) ∧
    (∫t : ℝ,a03RatioTimeFourierMode Φ T σ A b ξ ρ t)=
      a03RatioTimeFourierContour Φ T σ c A b ξ ρ := by
  have hi := a03RatioTimeFourierJoint_integrable hΦ hSupp hc T σ A b ξ ρ
  have ht (t : ℝ) : a03RatioTimeFourierMode Φ T σ A b ξ ρ t=
      (1/(2*Real.pi):ℂ)*∫v : ℝ,a03RatioTimeFourierJoint Φ T σ c A b ξ ρ v t := by
    unfold a03RatioTimeFourierMode
    rw [a03ZeroModeRatioPartition_positive_contour (Real.exp_pos _) hc _ (rawMomentShifts T σ)
      (polarPoleKiller_BBLREntireWeight T σ _)]
    unfold verticalIntegral a03ZeroModeRatioKernel
    rw [←mul_assoc,mul_comm (Complex.exp ((ξ:ℂ)*I*(t:ℂ))*Φ t*Complex.exp (ρ*(Real.log t:ℂ)))
      (1/(2*Real.pi):ℂ),mul_assoc,←integral_const_mul]
    congr 1
    apply integral_congr_ae
    apply ae_of_all
    intro v
    dsimp only
    unfold a03RatioTimeFourierJoint
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
      ←Complex.ofReal_log (Real.exp_pos _).le,Real.log_exp]
    have he : Complex.exp (ρ*(Real.log t:ℂ))*
        Complex.exp (((A+b*Real.log t:ℝ):ℂ)*-((c:ℂ)+(v:ℂ)*I))=
      Complex.exp (-((c:ℂ)+(v:ℂ)*I)*(A:ℂ))*
        Complex.exp ((ρ-(b:ℂ)*((c:ℂ)+(v:ℂ)*I))*(Real.log t:ℂ)) := by
      rw [←Complex.exp_add,←Complex.exp_add]
      congr 1
      push_cast
      ring
    calc
      _=Complex.exp ((ξ:ℂ)*I*(t:ℂ))*(polarPoleKiller T σ ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I))*Φ t*
        (Complex.exp (ρ*(Real.log t:ℂ))*Complex.exp (((A+b*Real.log t:ℝ):ℂ)*-((c:ℂ)+(v:ℂ)*I))) := by ring
      _=_ := by rw [he]; ring
  have hfun := funext ht
  refine ⟨by rw [hfun]; exact hi.integral_prod_right.const_mul _,?_⟩
  rw [hfun,integral_const_mul,←integral_integral_swap hi]
  unfold a03RatioTimeFourierContour
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro v
  dsimp only
  let z : ℂ := (c:ℂ)+(v:ℂ)*I
  have hp (t : ℝ) : a03RatioTimeFourierJoint Φ T σ c A b ξ ρ v t=
      (Complex.exp (-z*(A:ℂ))*(polarPoleKiller T σ z/z))*
        (Complex.exp ((ξ:ℂ)*I*(t:ℂ))*Φ t*(t:ℂ)^(ρ-(b:ℂ)*z)) := by
    by_cases hzero : Φ t=0
    · simp [a03RatioTimeFourierJoint,hzero]
    · have htp : 0<t := zero_lt_one.trans_le (hSupp (subset_tsupport _ hzero)).1
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr htp.ne'),←Complex.ofReal_log htp.le]
      unfold a03RatioTimeFourierJoint
      dsimp only [z]
      ring
  rw [funext hp,integral_const_mul]
  unfold profileLaplaceTransform a03ProfileProduct
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro t
  dsimp only [z]
  ring

end
end Sechstmoment
