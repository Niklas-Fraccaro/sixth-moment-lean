import Sechstmoment.Analysis.Gaussian.Decay
import Sechstmoment.Numerator.Polar.GaussianLogGrowth
import Sechstmoment.Numerator.U.Replacement.TimeGamma.Derivatives

namespace Sechstmoment.Source
open Complex Set Metric Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

def bblrGaussianTimeAmplitude (T : ℝ) (σ α : MomentShifts) (z : ℂ) (y : ℝ) : ℂ :=
  (polarPoleKiller T σ z/z*(Real.pi : ℂ)^(-2*z))*bblrGammaQuotient (T*y) α z

theorem gaussianPolynomialExponential_uniform_bound (n : ℕ) (a : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : ℝ,
      (1+|v|)^n*Real.exp (a*|v|-v^2) ≤ C := by
  let f : ℝ → ℝ := fun v => (1+|v|)^n*Real.exp (a*|v|-v^2)
  have hf : Continuous f := by fun_prop
  have he : ∀ᶠ v : ℝ in cocompact ℝ, f v ≤ 1 :=
    (Sechstmoment.gaussianPolynomialExponential_tendsto_zero n a).eventually_le_const (by norm_num)
  obtain ⟨K,hK,hout⟩ := mem_cocompact.mp he
  obtain ⟨D,hD⟩ := hK.bddAbove_image hf.continuousOn
  refine ⟨max 1 D+1,by have := le_max_left (1 : ℝ) D; linarith,?_⟩
  intro v
  by_cases hv : v ∈ K
  · exact (hD (mem_image_of_mem f hv)).trans (by have := le_max_right (1 : ℝ) D; linarith)
  · exact (hout hv).trans (by have := le_max_left (1 : ℝ) D; linarith)

theorem bblrGaussianTimeAmplitude_contDiffAt {T A : ℝ}
    (hA : 0 ≤ A) (hT : 8*(A+1) ≤ T) (σ α : MomentShifts)
    (hα : ∀ j, ‖α j‖ ≤ A) {z : ℂ}
    (hlarge : 192*(‖z‖+‖z‖^2) < T)
    {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) :
    ContDiffAt ℝ ⊤ (bblrGaussianTimeAmplitude T σ α z) x := by
  unfold bblrGaussianTimeAmplitude
  exact contDiffAt_const.mul
    (bblrGammaQuotient_normalizedTime_contDiffAt hA hT α hα hlarge hx)

theorem bblrGaussianTimeAmplitude_derivative_gaussian_bound (n : ℕ)
    {T A c : ℝ} (hA : 0 ≤ A) (hT : 8*(A+1) ≤ T) (hc : 0 < c)
    (σ α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ A) (v : ℝ)
    (hlarge : 192*(‖(c : ℂ)+(v : ℂ)*I‖+‖(c : ℂ)+(v : ℂ)*I‖^2) < T)
    {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) :
    ‖iteratedDeriv n (bblrGaussianTimeAmplitude T σ α ((c : ℂ)+(v : ℂ)*I)) x‖ ≤
      ((n.factorial : ℝ)/(1/4 : ℝ)^n)*
        (16*(2*T)^(2*c)*polarGaussianConstant T σ c/c)*
        ((1+|v|)^48*Real.exp (2*Real.pi*|v|-v^2)) := by
  have hGC := polarGaussianConstant_nonneg T σ c
  let z : ℂ := (c : ℂ)+(v : ℂ)*I
  have hzr : z.re=c := by simp [z]
  have hzi : z.im=v := by simp [z]
  have hzn : c ≤ ‖z‖ := by
    simpa only [hzr,abs_of_pos hc] using Complex.abs_re_le_norm z
  have hpi : ‖(Real.pi : ℂ)^(-2*z)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have he : (-2*z).re = -2*c := by simp [hzr]
    rw [he]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
  have hg := polarPoleKiller_vertical_norm_le T σ c v
  have hs : ‖polarPoleKiller T σ z/z*(Real.pi : ℂ)^(-2*z)‖ ≤
      polarGaussianConstant T σ c*(1+|v|)^48*Real.exp (-v^2)/c := by
    rw [norm_mul,norm_div]
    calc
      _ ≤ (polarGaussianConstant T σ c*(1+|v|)^48*Real.exp (-v^2)/c)*1 := by
        apply mul_le_mul
        · exact div_le_div₀ (by positivity) hg hc hzn
        · exact hpi
        · exact norm_nonneg _
        · positivity
      _ = _ := mul_one _
  have hq := bblrGammaQuotient_normalizedTime_derivative_bound n hA hT α hα
    (by rw [hzr]; exact hc.le) hlarge hx
  unfold bblrGaussianTimeAmplitude
  rw [iteratedDeriv_const_mul_field,norm_mul]
  apply (mul_le_mul hs hq (norm_nonneg _) (by positivity)).trans_eq
  rw [hzr,hzi]
  have he : Real.exp (-v^2)*Real.exp (2*Real.pi*|v|) =
      Real.exp (2*Real.pi*|v|-v^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = ((n.factorial : ℝ)/(1/4 : ℝ)^n)*
        (16*(2*T)^(2*c)*polarGaussianConstant T σ c/c)*
        ((1+|v|)^48*(Real.exp (-v^2)*Real.exp (2*Real.pi*|v|))) := by ring
    _ = _ := by rw [he]

theorem bblrGaussianTimeAmplitude_uniform_derivative_bounds {c : ℝ} (hc : 0 < c) :
    ∃ D : ℝ, 0 < D ∧ ∀ (n : ℕ) (T A : ℝ) (σ α : MomentShifts) (v x : ℝ),
      0 ≤ A → 8*(A+1) ≤ T → (∀ j, ‖α j‖ ≤ A) →
      192*(‖(c : ℂ)+(v : ℂ)*I‖+‖(c : ℂ)+(v : ℂ)*I‖^2) < T →
      x ∈ Icc (1 : ℝ) 2 →
      ‖iteratedDeriv n (bblrGaussianTimeAmplitude T σ α ((c : ℂ)+(v : ℂ)*I)) x‖ ≤
        ((n.factorial : ℝ)/(1/4 : ℝ)^n)*D*(2*T)^(2*c)*polarGaussianConstant T σ c := by
  obtain ⟨E,hE,he⟩ := gaussianPolynomialExponential_uniform_bound 48 (2*Real.pi)
  refine ⟨16*E/c,by positivity,?_⟩
  intro n T A σ α v x hA hT hα hlarge hx
  have hT0 : 0 < T := by linarith
  have hGC := polarGaussianConstant_nonneg T σ c
  have hh := bblrGaussianTimeAmplitude_derivative_gaussian_bound n hA hT hc σ α hα v hlarge hx
  apply hh.trans
  calc
    _ ≤ ((n.factorial : ℝ)/(1/4 : ℝ)^n)*
        (16*(2*T)^(2*c)*polarGaussianConstant T σ c/c)*E := by
      exact mul_le_mul_of_nonneg_left (he v) (by positivity)
    _ = _ := by ring

end
end Sechstmoment.Source
