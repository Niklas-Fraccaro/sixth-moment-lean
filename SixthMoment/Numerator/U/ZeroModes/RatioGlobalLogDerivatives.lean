import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import SixthMoment.Numerator.U.ZeroModes.Contour.RatioSmooth
import SixthMoment.Numerator.U.ZeroModes.Ratio.ContourBounds

namespace SixthMoment.Source
open Complex Real Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 0

theorem a03ZeroModeRatioLogDerivative_partition (G : ℂ→ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (w : ℝ) :
    a03ZeroModeRatioLogDerivative G 0 w+a03ZeroModeRatioLogDerivative G 0 (-w)=1 := by
  have he := a03ZeroModeRatioPartition_identity (Real.exp_pos w) G α hG
  rw [a03ZeroModeRatioPartition_eq_logDerivative G (Real.exp_pos w),Real.log_exp] at he
  have hInv : (Real.exp w)⁻¹=Real.exp (-w) := (Real.exp_neg w).symm
  rw [hInv,a03ZeroModeRatioPartition_eq_logDerivative G (Real.exp_pos (-w)),Real.log_exp] at he
  exact he

theorem a03ZeroModeRatioLogDerivative_reflection (G : ℂ→ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (n : ℕ) (w : ℝ) :
    a03ZeroModeRatioLogDerivative G n w+(-1:ℂ)^n*a03ZeroModeRatioLogDerivative G n (-w)=
      if n=0 then 1 else 0 := by
  induction n generalizing w with
  | zero => simpa using a03ZeroModeRatioLogDerivative_partition G α hG w
  | succ n ih =>
    have he : (fun u : ℝ => a03ZeroModeRatioLogDerivative G n u+
        (-1:ℂ)^n*a03ZeroModeRatioLogDerivative G n (-u))=
        fun _ => (if n=0 then (1:ℂ) else 0) := funext ih
    have hn : HasDerivAt (fun u : ℝ => a03ZeroModeRatioLogDerivative G n (-u))
        (-a03ZeroModeRatioLogDerivative G (n+1) (-w)) w := by
      simpa only [Function.comp_def,neg_one_smul] using
        (a03ZeroModeRatioLogDerivative_hasDerivAt G α hG n (-w)).scomp w (hasDerivAt_neg w)
    have hd := (a03ZeroModeRatioLogDerivative_hasDerivAt G α hG n w).add (hn.const_mul ((-1:ℂ)^n))
    have hz : deriv (fun _ : ℝ => (if n=0 then (1:ℂ) else 0)) w=0 := deriv_const _ _
    have hvalue := congrArg (fun f : ℝ→ℂ => deriv f w) he
    change deriv (a03ZeroModeRatioLogDerivative G n+(fun u : ℝ =>
      (-1:ℂ)^n*a03ZeroModeRatioLogDerivative G n (-u))) w=_ at hvalue
    rw [hd.deriv,hz] at hvalue
    simp only [pow_succ,Nat.succ_ne_zero,ite_false]
    convert hvalue using 1
    ring

theorem a03ZeroModeRatioLogIntegrand_nonnegative_bound (α : MomentShifts) (n : ℕ)
    {w : ℝ} (hw : 0≤w) (v : ℝ) :
    ‖a03ZeroModeRatioLogIntegrand (a03ZeroModeRatioWeight α) n w v‖≤
      a03ZeroModeRatioGaussianConstant α 1*(1+|v|)^(n+4)*Real.exp (-(1/2)*v^2) := by
  let z : ℂ := 1+(v:ℂ)*I
  have hC := a03ZeroModeRatioGaussianConstant_nonneg α 1
  have hz : ‖z‖≤1+|v| := by simpa [z] using Complex.norm_le_abs_re_add_abs_im z
  have hz1 : 1≤‖z‖ := by simpa [z] using Complex.re_le_norm z
  have hG := a03ZeroModeRatioWeight_gaussian_bound α (by norm_num : (0:ℝ)≤1) (z := z) (by simp [z])
  have hExp : ‖Complex.exp (-z*(w:ℂ))‖≤1 := by
    rw [Complex.norm_exp]
    have hre : (-z*(w:ℂ)).re=-w := by simp [z]
    rw [hre]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hw)
  unfold a03ZeroModeRatioLogIntegrand
  change ‖(-z)^n*(a03ZeroModeRatioWeight α z/z)*Complex.exp (-z*(w:ℂ))‖≤_
  rw [norm_mul,norm_mul,norm_pow,norm_neg,norm_div]
  calc
    _≤(1+|v|)^n*(a03ZeroModeRatioGaussianConstant α 1*(1+|v|)^4*Real.exp (-v^2)/1)*1 := by
      gcongr
      simpa [z] using hG
    _≤a03ZeroModeRatioGaussianConstant α 1*(1+|v|)^(n+4)*Real.exp (-(1/2)*v^2) := by
      rw [pow_add]
      have he := Real.exp_le_exp.mpr (show -v^2≤-(1/2)*v^2 by nlinarith [sq_nonneg v])
      simp only [div_one,mul_one]
      nlinarith [mul_le_mul_of_nonneg_left he (show 0≤(1+|v|)^n*(a03ZeroModeRatioGaussianConstant α 1*(1+|v|)^4) by positivity)]

theorem a03ZeroModeRatioLogDerivative_nonnegative_bound (α : MomentShifts) (n : ℕ)
    {w : ℝ} (hw : 0≤w) :
    ‖a03ZeroModeRatioLogDerivative (a03ZeroModeRatioWeight α) n w‖≤
      (gaussianTailConstant (n+4)/(2*Real.pi))*a03ZeroModeRatioGaussianConstant α 1 := by
  unfold a03ZeroModeRatioLogDerivative
  rw [norm_mul,show ‖(1/(2*Real.pi):ℂ)‖=1/(2*Real.pi) by simp [Complex.norm_real,abs_of_pos Real.pi_pos]]
  have hb := norm_integral_le_of_norm_le
    ((gaussian_polynomial_half_integrable (n+4)).const_mul (a03ZeroModeRatioGaussianConstant α 1))
    (Eventually.of_forall (fun v => by simpa only [mul_assoc] using
      a03ZeroModeRatioLogIntegrand_nonnegative_bound α n hw v))
  apply (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq
  rw [integral_const_mul]
  unfold gaussianTailConstant
  ring

theorem a03ZeroModeRatioLogDerivative_global_bound (α : MomentShifts) (n : ℕ) (w : ℝ) :
    ‖a03ZeroModeRatioLogDerivative (a03ZeroModeRatioWeight α) n w‖≤
      1+(gaussianTailConstant (n+4)/(2*Real.pi))*a03ZeroModeRatioGaussianConstant α 1 := by
  let B := (gaussianTailConstant (n+4)/(2*Real.pi))*a03ZeroModeRatioGaussianConstant α 1
  have hB : 0≤B := by dsimp [B]; exact mul_nonneg (div_nonneg (gaussianTailConstant_nonneg _) (by positivity)) (a03ZeroModeRatioGaussianConstant_nonneg _ _)
  by_cases hw : 0≤w
  · exact (a03ZeroModeRatioLogDerivative_nonnegative_bound α n hw).trans (by dsimp [B] at hB; linarith)
  · have hw' : 0≤-w := by linarith
    have hb := a03ZeroModeRatioLogDerivative_nonnegative_bound α n hw'
    have he := a03ZeroModeRatioLogDerivative_reflection _ α (a03ZeroModeRatioWeight_admissible α) n w
    have hv : a03ZeroModeRatioLogDerivative (a03ZeroModeRatioWeight α) n w=
        (if n=0 then (1:ℂ) else 0)-(-1:ℂ)^n*a03ZeroModeRatioLogDerivative (a03ZeroModeRatioWeight α) n (-w) := by
      linear_combination he
    rw [hv]
    have hc : ‖(if n=0 then (1:ℂ) else 0)‖≤1 := by split_ifs <;> norm_num
    have hm : ‖(-1:ℂ)^n*a03ZeroModeRatioLogDerivative (a03ZeroModeRatioWeight α) n (-w)‖=
        ‖a03ZeroModeRatioLogDerivative (a03ZeroModeRatioWeight α) n (-w)‖ := by simp
    exact (norm_sub_le _ _).trans (by rw [hm]; exact add_le_add hc hb)

theorem a03ZeroModeRatioLogDerivative_global_log_growth {T κ : ℝ}
    (hT : 1<T) (hL : 1≤Real.log T) (hκ : 0<κ) (σ : MomentShifts)
    (hρ : ∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) (n : ℕ) (w : ℝ) :
    ‖a03ZeroModeRatioLogDerivative (a03ZeroModeRatioWeight (rawMomentShifts T σ)) n w‖≤
      (1+(gaussianTailConstant (n+4)/(2*Real.pi))*
        (Real.exp 1*16*(1+1/κ^2)^2))*(Real.log T)^4 := by
  have hC := a03ZeroModeRatioGaussianConstant_log_growth hT hL hκ σ hρ
  have hD : 0≤gaussianTailConstant (n+4)/(2*Real.pi) :=
    div_nonneg (gaussianTailConstant_nonneg _) (by positivity)
  have hpow : 1≤(Real.log T)^4 := one_le_pow₀ hL
  exact (a03ZeroModeRatioLogDerivative_global_bound _ n w).trans (by nlinarith [mul_le_mul_of_nonneg_left hC hD])


theorem a03ZeroModeRatioLogDerivative_iteratedDeriv (G : ℂ→ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (n : ℕ) :
    iteratedDeriv n (a03ZeroModeRatioLogDerivative G 0)=a03ZeroModeRatioLogDerivative G n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext w
    exact (a03ZeroModeRatioLogDerivative_hasDerivAt G α hG n w).deriv

theorem a03ZeroModeRatioPartition_log_iteratedDeriv (G : ℂ→ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (n : ℕ) (w : ℝ) :
    iteratedDeriv n (fun u : ℝ => a03ZeroModeRatioPartition G (Real.exp u)) w=
      a03ZeroModeRatioLogDerivative G n w := by
  have he : (fun u : ℝ => a03ZeroModeRatioPartition G (Real.exp u))=a03ZeroModeRatioLogDerivative G 0 := by
    funext u
    simpa only [Real.log_exp] using a03ZeroModeRatioPartition_eq_logDerivative G (Real.exp_pos u)
  rw [he,a03ZeroModeRatioLogDerivative_iteratedDeriv G α hG n]

end
end SixthMoment.Source
