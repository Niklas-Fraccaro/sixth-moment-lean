import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Sechstmoment.Numerator.U.ZeroModes.Contour.RatioPartition


namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 0

def a03ZeroModeRatioLogIntegrand (G : ℂ → ℂ) (n : ℕ) (w v : ℝ) : ℂ :=
  let z : ℂ := 1+(v:ℂ)*I
  (-z)^n*(G z/z)*Complex.exp (-z*(w:ℂ))

def a03ZeroModeRatioLogDerivative (G : ℂ → ℂ) (n : ℕ) (w : ℝ) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫ v : ℝ, a03ZeroModeRatioLogIntegrand G n w v

theorem a03ZeroModeRatioLogIntegrand_continuous (G : ℂ → ℂ) (hG : Continuous G)
    (n : ℕ) (w : ℝ) : Continuous (a03ZeroModeRatioLogIntegrand G n w) := by
  unfold a03ZeroModeRatioLogIntegrand
  apply Continuous.mul
  · apply Continuous.mul (by fun_prop)
    apply (hG.comp (by fun_prop : Continuous (fun v : ℝ => 1+(v:ℂ)*I))).div (by fun_prop)
    intro v hv
    have he := congrArg Complex.re hv
    norm_num at he
  · fun_prop

theorem a03ZeroModeRatioLogIntegrand_local_bound (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (n : ℕ) (w₀ : ℝ) :
    ∃ D : ℝ, 0≤D ∧ ∀ w∈Icc (w₀-1) (w₀+1), ∀ v : ℝ,
      ‖a03ZeroModeRatioLogIntegrand G n w v‖≤D*(1+v^2)⁻¹ := by
  obtain ⟨C,hC,hWeight⟩ := hG.2.2.2 1 (by norm_num) (n+2)
  let D : ℝ := C*Real.exp (1-w₀)
  refine ⟨D,by dsimp [D]; positivity,?_⟩
  intro w hw v
  let z : ℂ := 1+(v:ℂ)*I
  let W : ℝ := 1+|v|
  have hW : 1≤W := by dsimp [W]; linarith [abs_nonneg v]
  have hzn : 1≤‖z‖ := by simpa [z] using Complex.re_le_norm z
  have hzw : ‖z‖≤W := by simpa [z,W] using Complex.norm_le_abs_re_add_abs_im z
  have hInv : ‖z‖⁻¹≤1 := inv_le_one_of_one_le₀ hzn
  have hExp : ‖Complex.exp (-z*(w:ℂ))‖≤Real.exp (1-w₀) := by
    rw [Complex.norm_exp]
    have hre : (-z*(w:ℂ)).re=-w := by simp [z]
    rw [hre]
    exact Real.exp_le_exp.mpr (by linarith [hw.1])
  have hN : ‖a03ZeroModeRatioLogIntegrand G n w v‖≤
      ‖G z‖*W^n*Real.exp (1-w₀) := by
    unfold a03ZeroModeRatioLogIntegrand
    change ‖(-z)^n*(G z/z)*Complex.exp (-z*(w:ℂ))‖≤_
    rw [norm_mul,norm_mul,norm_pow,norm_neg,norm_div,div_eq_mul_inv]
    calc
      _ ≤ W^n*(‖G z‖*1)*Real.exp (1-w₀) := by gcongr
      _ = _ := by ring
  have hGN : ‖G z‖*W^(n+2)≤C := by simpa [z,W] using hWeight z (by simp [z])
  have hFull : ‖a03ZeroModeRatioLogIntegrand G n w v‖*W^2≤D := by
    calc
      _ ≤ (‖G z‖*W^n*Real.exp (1-w₀))*W^2 := mul_le_mul_of_nonneg_right hN (sq_nonneg _)
      _ = (‖G z‖*W^(n+2))*Real.exp (1-w₀) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hGN (Real.exp_pos _).le
  have hSq : 1+v^2≤W^2 := by dsimp [W]; nlinarith [sq_abs v,abs_nonneg v]
  have hProd := (mul_le_mul_of_nonneg_left hSq
    (norm_nonneg (a03ZeroModeRatioLogIntegrand G n w v))).trans hFull
  rw [←div_eq_mul_inv]
  exact (le_div_iff₀ (by positivity : 0<1+v^2)).mpr hProd

theorem a03ZeroModeRatioLogIntegrand_integrable (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (n : ℕ) (w : ℝ) :
    Integrable (a03ZeroModeRatioLogIntegrand G n w) := by
  obtain ⟨D,hD,hb⟩ := a03ZeroModeRatioLogIntegrand_local_bound G α hG n w
  apply (integrable_inv_one_add_sq.const_mul D).mono'
    (a03ZeroModeRatioLogIntegrand_continuous G
      (Complex.analyticOnNhd_univ_iff_differentiable.mp hG.1).continuous n w).aestronglyMeasurable
  exact Eventually.of_forall (fun v => hb w ⟨by linarith,by linarith⟩ v)

theorem a03ZeroModeRatioLogIntegrand_hasDerivAt (G : ℂ → ℂ) (n : ℕ)
    (w v : ℝ) :
    HasDerivAt (fun w : ℝ => a03ZeroModeRatioLogIntegrand G n w v)
      (a03ZeroModeRatioLogIntegrand G (n+1) w v) w := by
  let z : ℂ := 1+(v:ℂ)*I
  have hw : HasDerivAt (fun w : ℝ => (w:ℂ)) 1 w := Complex.ofRealCLM.hasDerivAt
  have he := (hw.const_mul (-z)).cexp
  have h := he.const_mul ((-z)^n*(G z/z))
  convert h using 1
  · funext y
    rfl
  · unfold a03ZeroModeRatioLogIntegrand
    change (-z)^(n+1)*(G z/z)*Complex.exp (-z*(w:ℂ)) = _
    rw [pow_succ]
    ring

theorem a03ZeroModeRatioLogDerivative_hasDerivAt (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (n : ℕ) (w₀ : ℝ) :
    HasDerivAt (a03ZeroModeRatioLogDerivative G n)
      (a03ZeroModeRatioLogDerivative G (n+1) w₀) w₀ := by
  obtain ⟨D,hD,hb⟩ := a03ZeroModeRatioLogIntegrand_local_bound G α hG (n+1) w₀
  have hmeas (n : ℕ) (w : ℝ) :
      AEStronglyMeasurable (a03ZeroModeRatioLogIntegrand G n w) volume :=
    (a03ZeroModeRatioLogIntegrand_continuous G
      (Complex.analyticOnNhd_univ_iff_differentiable.mp hG.1).continuous n w).aestronglyMeasurable
  have hIntegral := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w v => a03ZeroModeRatioLogIntegrand G n w v)
    (F' := fun w v => a03ZeroModeRatioLogIntegrand G (n+1) w v)
    (s := Icc (w₀-1) (w₀+1)) (bound := fun v : ℝ => D*(1+v^2)⁻¹)
    (Icc_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall (fun w => hmeas n w))
    (a03ZeroModeRatioLogIntegrand_integrable G α hG n w₀) (hmeas (n+1) w₀)
    (Eventually.of_forall (fun v w hw => hb w hw v))
    (integrable_inv_one_add_sq.const_mul D)
    (Eventually.of_forall (fun v w _ => a03ZeroModeRatioLogIntegrand_hasDerivAt G n w v))
  exact hIntegral.2.const_mul (1/(2*Real.pi):ℂ)

theorem a03ZeroModeRatioLogDerivative_contDiff (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) : ContDiff ℝ ∞ (a03ZeroModeRatioLogDerivative G 0) := by
  have hi (n : ℕ) : iteratedDeriv n (a03ZeroModeRatioLogDerivative G 0)=
      a03ZeroModeRatioLogDerivative G n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iteratedDeriv_succ,ih]
      funext w
      exact (a03ZeroModeRatioLogDerivative_hasDerivAt G α hG n w).deriv
  apply contDiff_of_differentiable_iteratedDeriv
  intro n hn
  rw [hi]
  exact fun w => (a03ZeroModeRatioLogDerivative_hasDerivAt G α hG n w).differentiableAt

theorem a03ZeroModeRatioPartition_eq_logDerivative (G : ℂ → ℂ)
    {x : ℝ} (hx : 0<x) :
    a03ZeroModeRatioPartition G x=a03ZeroModeRatioLogDerivative G 0 (Real.log x) := by
  unfold a03ZeroModeRatioPartition verticalIntegral a03ZeroModeRatioLogDerivative
  congr 1
  apply integral_congr_ae
  filter_upwards [] with v
  unfold a03ZeroModeRatioKernel a03ZeroModeRatioLogIntegrand
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ←Complex.ofReal_log hx.le]
  simp only [pow_zero,one_mul,Complex.ofReal_one]
  rw [show (Real.log x:ℂ)*-(1+(v:ℂ)*I)=-(1+(v:ℂ)*I)*(Real.log x:ℂ) by ring]
  ring

theorem a03ZeroModeRatioPartition_contDiffOn (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) :
    ContDiffOn ℝ ∞ (a03ZeroModeRatioPartition G) (Ioi 0) := by
  have hs : ContDiffOn ℝ ∞ (fun x : ℝ =>
      a03ZeroModeRatioLogDerivative G 0 (Real.log x)) (Ioi 0) := by
    intro x hx
    exact ((a03ZeroModeRatioLogDerivative_contDiff G α hG).contDiffAt.comp x
      (Real.contDiffAt_log.mpr (ne_of_gt hx))).contDiffWithinAt
  apply hs.congr
  intro x hx
  exact a03ZeroModeRatioPartition_eq_logDerivative G hx

theorem a03ZeroModeRatioPartition_actual_contDiffOn (α : MomentShifts) :
    ContDiffOn ℝ ∞ (a03ZeroModeRatioPartition (a03ZeroModeRatioWeight α)) (Ioi 0) :=
  a03ZeroModeRatioPartition_contDiffOn _ α (a03ZeroModeRatioWeight_admissible α)

end
end Sechstmoment.Source
