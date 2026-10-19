import Sechstmoment.Numerator.U.Separation.TimePowerProfileFourier
import Sechstmoment.Numerator.U.ZeroModes.ForwardMellin
import Sechstmoment.Numerator.U.ZeroModes.Transforms.PositiveTimeGaussianConvolution

/-! Actual positive-line ratio/time Fourier reconstruction. All vertical/time
interchanges are justified by the explicit Gaussian and compact-time majorant. -/
namespace Sechstmoment
open Complex Real Source Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 700000

def a03RatioTimeFourierJoint (Φ : ℝ→ℂ) (T : ℝ) (σ : MomentShifts)
    (c A b ξ : ℝ) (ρ : ℂ) (v t : ℝ) : ℂ :=
  let z : ℂ := (c:ℂ)+(v:ℂ)*I
  Complex.exp ((ξ:ℂ)*I*(t:ℂ))*Complex.exp (-z*(A:ℂ))*(polarPoleKiller T σ z/z)*Φ t*
    Complex.exp ((ρ-(b:ℂ)*z)*(Real.log t:ℂ))

def a03RatioTimeFourierMode (Φ : ℝ→ℂ) (T : ℝ) (σ : MomentShifts)
    (A b ξ : ℝ) (ρ : ℂ) (t : ℝ) : ℂ :=
  Complex.exp ((ξ:ℂ)*I*(t:ℂ))*Φ t*Complex.exp (ρ*(Real.log t:ℂ))*
    a03ZeroModeRatioPartition (polarPoleKiller T σ) (Real.exp (A+b*Real.log t))

def a03RatioTimeFourierContour (Φ : ℝ→ℂ) (T : ℝ) (σ : MomentShifts)
    (c A b ξ : ℝ) (ρ : ℂ) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫v : ℝ,
    Complex.exp (-((c:ℂ)+(v:ℂ)*I)*(A:ℂ))*(polarPoleKiller T σ ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I))*
      profileLaplaceTransform (a03ProfileProduct Φ
        (fun t : ℝ => (t:ℂ)^(ρ-(b:ℂ)*((c:ℂ)+(v:ℂ)*I)))) ((ξ:ℂ)*I)

theorem a03PolarPositiveLineDiv_bound {c : ℝ} (hc : 0<c) (T : ℝ) (σ : MomentShifts) (v : ℝ) :
    ‖polarPoleKiller T σ ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I)‖≤
      polarGaussianConstant T σ c/c*(1+|v|)^48*Real.exp (-(1/2)*v^2) := by
  have hz : c≤‖(c:ℂ)+(v:ℂ)*I‖ := by simpa using Complex.re_le_norm ((c:ℂ)+(v:ℂ)*I)
  have hG := polarPoleKiller_vertical_norm_le T σ c v
  have hCG := polarGaussianConstant_nonneg T σ c
  rw [norm_div]
  calc
    _≤‖polarPoleKiller T σ ((c:ℂ)+(v:ℂ)*I)‖/c := div_le_div_of_nonneg_left (norm_nonneg _) hc hz
    _≤(polarGaussianConstant T σ c*(1+|v|)^48*Real.exp (-v^2))/c := div_le_div_of_nonneg_right hG hc.le
    _≤_ := by
      have he := Real.exp_le_exp.mpr (show -v^2≤-(1/2)*v^2 by nlinarith only [sq_nonneg v])
      convert mul_le_mul_of_nonneg_left he (by positivity : 0≤polarGaussianConstant T σ c/c*(1+|v|)^48) using 1
      ring

theorem a03RatioTimeFourierJoint_integrable {Φ : ℝ→ℂ} (hΦ : Continuous Φ)
    (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) {c : ℝ} (hc : 0<c) (T : ℝ) (σ : MomentShifts)
    (A b ξ : ℝ) (ρ : ℂ) :
    Integrable (Function.uncurry (a03RatioTimeFourierJoint Φ T σ c A b ξ ρ)) (volume.prod volume) := by
  let M : ℝ := Real.exp (|ρ.re-b*c| * Real.log 2)
  let B : ℝ := Real.exp (-c*A)*polarGaussianConstant T σ c/c*M
  have hCG := polarGaussianConstant_nonneg T σ c
  have hB : 0≤B := by dsimp [B,M]; positivity
  have hΦK : HasCompactSupport Φ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hSupp
  have hΦI : Integrable Φ := hΦ.integrable_of_hasCompactSupport hΦK
  have hm : AEStronglyMeasurable
      (Function.uncurry (a03RatioTimeFourierJoint Φ T σ c A b ξ ρ)) (volume.prod volume) := by
    have hz : Continuous (fun p : ℝ×ℝ => (c:ℂ)+(p.1:ℂ)*I) := by fun_prop
    have hz0 (p : ℝ×ℝ) : (c:ℂ)+(p.1:ℂ)*I≠0 := by
      intro he
      have hh := congrArg Complex.re he
      simp at hh
      linarith only [hh,hc]
    have hG := ((polarPoleKiller_differentiable T σ).continuous.comp hz).div hz hz0
    have hlog : Measurable (fun p : ℝ×ℝ => (Real.log p.2:ℂ)) := by fun_prop
    have hphase : Continuous (fun p : ℝ×ℝ => Complex.exp ((ξ:ℂ)*I*(p.2:ℂ))) := by fun_prop
    exact ((((hphase.measurable.mul (hz.neg.mul continuous_const).cexp.measurable).mul hG.measurable).mul
      (hΦ.measurable.comp measurable_snd)).mul
        ((((continuous_const : Continuous (fun _p : ℝ×ℝ => ρ)).sub (hz.const_mul (b:ℂ))).measurable.mul hlog).cexp)).aestronglyMeasurable
  apply (((gaussian_polynomial_half_integrable 48).mul_prod hΦI.norm).const_mul B).mono' hm
  apply ae_of_all
  intro p
  by_cases ht : Φ p.2=0
  · simp only [a03RatioTimeFourierJoint,Function.uncurry,ht,mul_zero,zero_mul,norm_zero]
    positivity
  · have hs := hSupp (subset_tsupport _ ht)
    have htp : 0<p.2 := zero_lt_one.trans_le hs.1
    have hlog0 := Real.log_nonneg hs.1
    have hlog2 := Real.log_le_log htp hs.2
    have hpower : ‖Complex.exp ((ρ-(b:ℂ)*((c:ℂ)+(p.1:ℂ)*I))*(Real.log p.2:ℂ))‖≤M := by
      rw [Complex.norm_exp]
      have he : ((ρ-(b:ℂ)*((c:ℂ)+(p.1:ℂ)*I))*(Real.log p.2:ℂ)).re=(ρ.re-b*c)*Real.log p.2 := by simp
      rw [he]
      apply Real.exp_le_exp.mpr
      exact (mul_le_mul_of_nonneg_right (le_abs_self _) hlog0).trans
        (mul_le_mul_of_nonneg_left hlog2 (abs_nonneg _))
    have hphase : ‖Complex.exp ((ξ:ℂ)*I*(p.2:ℂ))‖=1 := by
      rw [Complex.norm_exp]
      simp
    have hscalar : ‖Complex.exp (-((c:ℂ)+(p.1:ℂ)*I)*(A:ℂ))‖=Real.exp (-c*A) := by
      rw [Complex.norm_exp]
      congr 1
      simp
    unfold Function.uncurry a03RatioTimeFourierJoint
    rw [norm_mul,norm_mul,norm_mul,norm_mul,hphase,one_mul,hscalar]
    calc
      _≤Real.exp (-c*A)*(polarGaussianConstant T σ c/c*(1+|p.1|)^48*Real.exp (-(1/2)*p.1^2))*‖Φ p.2‖*M := by
        gcongr
        exact a03PolarPositiveLineDiv_bound hc T σ p.1
      _=_ := by dsimp only [B]; ring

end
end Sechstmoment
