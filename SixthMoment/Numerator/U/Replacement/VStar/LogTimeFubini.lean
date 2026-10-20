import SixthMoment.Numerator.U.ZeroModes.RatioGlobalLogDerivatives
import SixthMoment.Numerator.U.ZeroModes.Transforms.PositiveTimeGaussianConvolution

namespace SixthMoment
open Complex Real Source Set MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 700000

def a03VStarLogTimeJoint (Φ : ℝ→ℂ) (T : ℝ) (σ : MomentShifts)
    (A b : ℝ) (q : ℂ) (v t : ℝ) : ℂ :=
  let z : ℂ := 1+(v:ℂ)*I
  Complex.exp (-z*(A:ℂ))*(polarPoleKiller T σ z/z)*Φ t*
    Complex.exp ((q-(b:ℂ)*z)*(Real.log t:ℂ))

def a03VStarLogTimeMode (Φ : ℝ→ℂ) (T : ℝ) (σ : MomentShifts)
    (A b : ℝ) (q : ℂ) (t : ℝ) : ℂ :=
  Φ t*Complex.exp (q*(Real.log t:ℂ))*
    a03ZeroModeRatioLogDerivative (polarPoleKiller T σ) 0 (A+b*Real.log t)

theorem a03VStarLogTimeJoint_integrable {Φ : ℝ→ℂ} (hΦ : Continuous Φ)
    (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) (T : ℝ) (σ : MomentShifts)
    (A b : ℝ) (q : ℂ) :
    Integrable (Function.uncurry (a03VStarLogTimeJoint Φ T σ A b q)) (volume.prod volume) := by
  let M : ℝ := Real.exp (|q.re-b| *Real.log 2)
  let B : ℝ := Real.exp (-A)*polarGaussianConstant T σ 1*M
  have hCG := polarGaussianConstant_nonneg T σ 1
  have hB : 0≤B := by dsimp [B,M]; positivity
  have hΦK : HasCompactSupport Φ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hSupp
  have hΦI : Integrable Φ := hΦ.integrable_of_hasCompactSupport hΦK
  have hm : AEStronglyMeasurable
      (Function.uncurry (a03VStarLogTimeJoint Φ T σ A b q)) (volume.prod volume) := by
    have hz : Continuous (fun p : ℝ×ℝ => (1:ℂ)+(p.1:ℂ)*I) := by fun_prop
    have hz0 (p : ℝ×ℝ) : (1:ℂ)+(p.1:ℂ)*I≠0 := by
      intro he
      have hh := congrArg Complex.re he
      norm_num at hh
    have hG := ((polarPoleKiller_differentiable T σ).continuous.comp hz).div hz hz0
    have hlog : Measurable (fun p : ℝ×ℝ => (Real.log p.2:ℂ)) := by fun_prop
    exact (((hz.neg.mul continuous_const).cexp.measurable.mul hG.measurable).mul
      (hΦ.measurable.comp measurable_snd)).mul
        ((((continuous_const : Continuous (fun _p : ℝ×ℝ => q)).sub (hz.const_mul (b:ℂ))).measurable.mul hlog).cexp) |>.aestronglyMeasurable
  apply (((gaussian_polynomial_half_integrable 48).mul_prod hΦI.norm).const_mul B).mono' hm
  apply ae_of_all
  intro p
  by_cases ht : Φ p.2=0
  · simp only [a03VStarLogTimeJoint,Function.uncurry,ht,mul_zero,zero_mul,norm_zero]
    positivity
  · have hs := hSupp (subset_tsupport _ ht)
    have htp : 0<p.2 := zero_lt_one.trans_le hs.1
    have hlog0 : 0≤Real.log p.2 := Real.log_nonneg hs.1
    have hlog2 : Real.log p.2≤Real.log 2 := Real.log_le_log htp hs.2
    have hlog20 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
    have hpower : ‖Complex.exp ((q-(b:ℂ)*(1+(p.1:ℂ)*I))*(Real.log p.2:ℂ))‖≤M := by
      rw [Complex.norm_exp]
      have he : ((q-(b:ℂ)*(1+(p.1:ℂ)*I))*(Real.log p.2:ℂ)).re=(q.re-b)*Real.log p.2 := by simp
      rw [he]
      apply Real.exp_le_exp.mpr
      exact (mul_le_mul_of_nonneg_right (le_abs_self _) hlog0).trans
        (mul_le_mul_of_nonneg_left hlog2 (abs_nonneg _))
    have hphase : ‖Complex.exp (-(1+(p.1:ℂ)*I)*(A:ℂ))‖=Real.exp (-A) := by
      rw [Complex.norm_exp]
      congr 1
      simp
    unfold Function.uncurry a03VStarLogTimeJoint
    rw [norm_mul,norm_mul,norm_mul,hphase]
    calc
      _≤Real.exp (-A)*(polarGaussianConstant T σ 1*(1+|p.1|)^48*Real.exp (-(1/2)*p.1^2))*‖Φ p.2‖*M := by
        gcongr
        exact a03PolarLineOneDiv_bound T σ p.1
      _=_ := by dsimp only [B]; ring

theorem a03PositiveTime_logged_integral_eq_mellin {Φ : ℝ→ℂ}
    (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) (q : ℂ) :
    (∫t : ℝ,Φ t*Complex.exp (q*(Real.log t:ℂ)))=mellin Φ (q+1) := by
  unfold mellin
  rw [show q+1-1=q by ring]
  rw [←integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  by_cases ht : t∈Ioi (0:ℝ)
  · rw [indicator_of_mem ht,smul_eq_mul,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'),
      ←Complex.ofReal_log ht.le]
    ring
  · have hzero : Φ t=0 := by
      by_contra hh
      exact ht (zero_lt_one.trans_le (hSupp (subset_tsupport _ hh)).1)
    simp [indicator_of_notMem ht,hzero]

theorem a03VStarLogTimeMode_integrable_eq {Φ : ℝ→ℂ} (hΦ : Continuous Φ)
    (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) (T : ℝ) (σ : MomentShifts)
    (A b : ℝ) (q : ℂ) :
    Integrable (a03VStarLogTimeMode Φ T σ A b q) ∧
    (∫t : ℝ,a03VStarLogTimeMode Φ T σ A b q t)=
      a03GaussianPositiveTimeMellinIntegral Φ T σ A (1+q.re-b) (-b) q.im := by
  have hi := a03VStarLogTimeJoint_integrable hΦ hSupp T σ A b q
  have ht (t : ℝ) : a03VStarLogTimeMode Φ T σ A b q t=
      (1/(2*Real.pi):ℂ)*∫v : ℝ,a03VStarLogTimeJoint Φ T σ A b q v t := by
    unfold a03VStarLogTimeMode a03ZeroModeRatioLogDerivative a03ZeroModeRatioLogIntegrand
    rw [←mul_assoc,mul_comm (Φ t*Complex.exp (q*(Real.log t:ℂ))) (1/(2*Real.pi):ℂ),
      mul_assoc,←integral_const_mul]
    congr 1
    apply integral_congr_ae
    apply ae_of_all
    intro v
    unfold a03VStarLogTimeJoint
    simp only [pow_zero,one_mul]
    have he : Complex.exp (q*(Real.log t:ℂ))*Complex.exp (-(1+(v:ℂ)*I)*((A+b*Real.log t:ℝ):ℂ))=
        Complex.exp (-(1+(v:ℂ)*I)*(A:ℂ))*
          Complex.exp ((q-(b:ℂ)*(1+(v:ℂ)*I))*(Real.log t:ℂ)) := by
      rw [←Complex.exp_add,←Complex.exp_add]
      congr 1
      push_cast
      ring
    calc
      _=(polarPoleKiller T σ (1+(v:ℂ)*I)/(1+(v:ℂ)*I))*Φ t*
        (Complex.exp (q*(Real.log t:ℂ))*Complex.exp (-(1+(v:ℂ)*I)*((A+b*Real.log t:ℝ):ℂ))) := by ring
      _=_ := by rw [he]; ring
  have hfun := funext ht
  refine ⟨by rw [hfun]; exact hi.integral_prod_right.const_mul _,?_⟩
  rw [hfun,integral_const_mul,←integral_integral_swap hi]
  unfold a03GaussianPositiveTimeMellinIntegral
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro v
  unfold a03VStarLogTimeJoint
  simp_rw [mul_assoc]
  rw [integral_const_mul,integral_const_mul]
  have he := a03PositiveTime_logged_integral_eq_mellin hSupp (q-(b:ℂ)*(1+(v:ℂ)*I))
  rw [he]
  have harg : q-(b:ℂ)*(1+(v:ℂ)*I)+1=
      ((1+q.re-b:ℝ):ℂ)+((q.im+(-b)*v:ℝ):ℂ)*I := by
    apply Complex.ext <;> simp <;> ring
  rw [harg]


end
end SixthMoment
