import Sechstmoment.Numerator.U.Replacement.TimeGamma.Subpower
import Sechstmoment.Numerator.U.Replacement.TimeGammaError

/-! The actual Gamma replacement-error amplitude has all normalized-time
seminorms O(T^(epsilon-1)), uniformly on separated normalized shift sets. -/
namespace Sechstmoment.Source
open Complex Set Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000

def bblrGaussianTimeReplacementAmplitude (T : ℝ) (σ α : MomentShifts)
    (z : ℂ) (y : ℝ) : ℂ :=
  (polarPoleKiller T σ z/z*(Real.pi:ℂ)^(-2*z))*
    (bblrGammaQuotient (T*y) α z-(T*y/2:ℂ)^(2*z))

theorem bblrGaussianTimeReplacementAmplitude_contDiffAt {T : ℝ} (hT : 10≤T)
    (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) {z : ℂ}
    (hz : 192*(‖z‖+‖z‖^2)<T) {x : ℝ} (hx : x∈Icc (1:ℝ) 2) :
    ContDiffAt ℝ ⊤ (bblrGaussianTimeReplacementAmplitude T σ α z) x := by
  unfold bblrGaussianTimeReplacementAmplitude
  exact contDiffAt_const.mul
    (bblrGammaReplacementError_normalizedTime_contDiffAt (by norm_num : (0:ℝ)≤1/4)
      (by norm_num; exact hT) α hα hz hx)

theorem bblrGaussianTimeReplacementAmplitude_derivative_gaussian_bound (n : ℕ)
    {T c : ℝ} (hT : 10≤T) (hc : 0<c) (hc1 : c≤1)
    (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) (v : ℝ)
    (hz : 192*(‖(c:ℂ)+(v:ℂ)*I‖+‖(c:ℂ)+(v:ℂ)*I‖^2)<T)
    {x : ℝ} (hx : x∈Icc (1:ℝ) 2) :
    ‖iteratedDeriv n (bblrGaussianTimeReplacementAmplitude T σ α ((c:ℂ)+(v:ℂ)*I)) x‖≤
      ((n.factorial:ℝ)/(1/4:ℝ)^n)*(2892*(2*T)^(2*c)*polarGaussianConstant T σ c/(c*T))*
        ((1+|v|)^50*Real.exp (2*Real.pi*|v|-v^2)) := by
  have hTp : 0<T := by linarith
  have hGC := polarGaussianConstant_nonneg T σ c
  let z : ℂ := (c:ℂ)+(v:ℂ)*I
  have hzr : z.re=c := by simp [z]
  have hzi : z.im=v := by simp [z]
  have hzn : c≤‖z‖ := by simpa only [hzr,abs_of_pos hc] using Complex.abs_re_le_norm z
  have hnup : ‖z‖≤1+|v| := by
    calc
      _≤‖(c:ℂ)‖+‖(v:ℂ)*I‖ := norm_add_le _ _
      _=c+|v| := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc]
      _≤_ := by linarith
  have hpoly : 1440*(‖z‖+‖z‖^2)+12*‖z‖≤2892*(1+|v|)^2 := by
    have h1 : 1≤1+|v| := by linarith [abs_nonneg v]
    nlinarith [norm_nonneg z]
  have hphase : (8+16*(1/4:ℝ))*‖z‖≤T := by
    norm_num only [show (8:ℝ)+16*(1/4)=12 by norm_num]
    change 192*(‖z‖+‖z‖^2)<T at hz
    nlinarith [norm_nonneg z,sq_nonneg ‖z‖]
  have hpi : ‖(Real.pi:ℂ)^(-2*z)‖≤1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have he : (-2*z).re=-2*c := by simp [hzr]
    rw [he]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
  have hg := polarPoleKiller_vertical_norm_le T σ c v
  have hs : ‖polarPoleKiller T σ z/z*(Real.pi:ℂ)^(-2*z)‖≤
      polarGaussianConstant T σ c*(1+|v|)^48*Real.exp (-v^2)/c := by
    rw [norm_mul,norm_div]
    calc
      _≤(polarGaussianConstant T σ c*(1+|v|)^48*Real.exp (-v^2)/c)*1 := by
        apply mul_le_mul
        · exact div_le_div₀ (by positivity) hg hc hzn
        · exact hpi
        · exact norm_nonneg _
        · positivity
      _=_ := mul_one _
  have hq := bblrGammaReplacementError_normalizedTime_derivative_bound n
    (by norm_num : (0:ℝ)≤1/4) (by norm_num; exact hT) α hα
    (by rw [hzr]; exact hc.le) hz hphase hx
  rw [hzr,hzi] at hq
  norm_num only [show (8:ℝ)+16*(1/4)=12 by norm_num] at hq
  have hq' : ‖iteratedDeriv n (fun y : ℝ => bblrGammaQuotient (T*y) α z-(T*y/2:ℂ)^(2*z)) x‖≤
      ((n.factorial:ℝ)/(1/4:ℝ)^n)*(2*T)^(2*c)*Real.exp (2*Real.pi*|v|)*
        (2892*(1+|v|)^2/T) := by
    apply hq.trans
    gcongr
  unfold bblrGaussianTimeReplacementAmplitude
  rw [iteratedDeriv_const_mul_field,norm_mul]
  apply (mul_le_mul hs hq' (norm_nonneg _) (by positivity)).trans_eq
  have he : Real.exp (-v^2)*Real.exp (2*Real.pi*|v|)=Real.exp (2*Real.pi*|v|-v^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hp : (1+|v|)^50=(1+|v|)^48*(1+|v|)^2 := by rw [← pow_add]
  rw [hp,← he]
  ring

theorem bblrGaussianTimeReplacementAmplitude_uniform_derivative_bounds
    {c : ℝ} (hc : 0<c) (hc1 : c≤1) :
    ∃ D : ℝ, 0<D ∧ ∀ (n : ℕ) (T : ℝ) (σ α : MomentShifts) (v x : ℝ),
      10≤T → (∀ j, ‖α j‖≤1/4) →
      192*(‖(c:ℂ)+(v:ℂ)*I‖+‖(c:ℂ)+(v:ℂ)*I‖^2)<T → x∈Icc (1:ℝ) 2 →
      ‖iteratedDeriv n (bblrGaussianTimeReplacementAmplitude T σ α ((c:ℂ)+(v:ℂ)*I)) x‖≤
        ((n.factorial:ℝ)/(1/4:ℝ)^n)*D*(2*T)^(2*c)*polarGaussianConstant T σ c/T := by
  obtain ⟨E,hE,he⟩ := gaussianPolynomialExponential_uniform_bound 50 (2*Real.pi)
  refine ⟨2892*E/c,by positivity,?_⟩
  intro n T σ α v x hT hα hz hx
  have hTp : 0<T := by linarith
  have hGC := polarGaussianConstant_nonneg T σ c
  apply (bblrGaussianTimeReplacementAmplitude_derivative_gaussian_bound n hT hc hc1 σ α hα v hz hx).trans
  calc
    _≤((n.factorial:ℝ)/(1/4:ℝ)^n)*(2892*(2*T)^(2*c)*polarGaussianConstant T σ c/(c*T))*E := by
      exact mul_le_mul_of_nonneg_left (he v) (by positivity)
    _=_ := by ring

theorem bblrGaussianTimeReplacementAmplitude_uniform_subpower_derivatives
    {c ε κ : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε) (hκ : 0<κ) :
    ∃ B : ℕ→ℝ, (∀ n, 0≤B n) ∧
      ∀ (T : ℝ) (σ α : MomentShifts) (v x : ℝ),
      10≤T → 1≤Real.log T → (∀ j, ‖α j‖≤1/4) →
      (∀ k : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ k‖) →
      192*(‖(c:ℂ)+(v:ℂ)*I‖+‖(c:ℂ)+(v:ℂ)*I‖^2)<T → x∈Icc (1:ℝ) 2 → ∀ n : ℕ,
      ‖iteratedDeriv n (bblrGaussianTimeReplacementAmplitude T σ α ((c:ℂ)+(v:ℂ)*I)) x‖≤
        B n*T^(ε-1) := by
  obtain ⟨D,hD,hd⟩ := bblrGaussianTimeReplacementAmplitude_uniform_derivative_bounds hc hc1
  let L : ℝ := ((48:ℕ).factorial:ℝ)/(ε-2*c)^48*Real.exp (ε-2*c)
  let H : ℝ := Real.exp (c^2)*(1+|c|)^48*(1+1/κ^2)^24
  let B : ℕ→ℝ := fun n => ((n.factorial:ℝ)/(1/4:ℝ)^n)*D*4*H*L
  have hL : 0≤L := by dsimp [L]; positivity
  have hH : 0≤H := by dsimp [H]; positivity
  refine ⟨B,fun n => by dsimp [B]; positivity,?_⟩
  intro T σ α v x hT hlog hα hroot hz hx n
  have hT1 : 1<T := by linarith
  have hTp : 0<T := by linarith
  have hGC := polarGaussianConstant_nonneg T σ c
  have hpow : (2*T)^(2*c)≤4*T^(2*c) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hTp.le]
    have h2 : (2:ℝ)^(2*c)≤4 := by
      calc
        _≤(2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _=_ := by norm_num
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have hg : polarGaussianConstant T σ c≤H*(Real.log T)^48 :=
    polarGaussianConstant_log_growth hT1 hlog hκ σ c hroot
  have hl : (Real.log T)^48≤L*T^(ε-2*c) := by
    calc
      _≤(1+Real.log T)^48 := pow_le_pow_left₀ (by linarith) (by linarith) 48
      _≤_ := Sechstmoment.logarithmic_power_le_rpow (by linarith) hT1.le 48
  have he : T^(2*c)*T^(ε-2*c)/T=T^(ε-1) := by
    rw [← Real.rpow_add hTp]
    have hs : 2*c+(ε-2*c)=ε := by ring
    rw [hs,Real.rpow_sub hTp,Real.rpow_one]
  calc
    _≤((n.factorial:ℝ)/(1/4:ℝ)^n)*D*(2*T)^(2*c)*polarGaussianConstant T σ c/T :=
      hd n T σ α v x hT hα hz hx
    _≤((n.factorial:ℝ)/(1/4:ℝ)^n)*D*(4*T^(2*c))*(H*(L*T^(ε-2*c)))/T := by
      apply div_le_div_of_nonneg_right _ hTp.le
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hpow (by positivity)
      · exact hg.trans (mul_le_mul_of_nonneg_left hl hH)
      · exact hGC
      · positivity
    _=B n*T^(ε-1) := by
      dsimp [B]
      rw [show ((n.factorial:ℝ)/(1/4:ℝ)^n)*D*(4*T^(2*c))*(H*(L*T^(ε-2*c)))/T=
        (((n.factorial:ℝ)/(1/4:ℝ)^n)*D*4*H*L)*(T^(2*c)*T^(ε-2*c)/T) by ring,he]

end
end Sechstmoment.Source
