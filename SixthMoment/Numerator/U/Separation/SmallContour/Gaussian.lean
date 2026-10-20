import SixthMoment.Numerator.U.Separation.LogarithmicGaussianTail
import SixthMoment.Numerator.U.Separation.SmallContour.Definitions

namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

def bblrGaussianSmallVCore (c T : ℝ) (σ α : MomentShifts) (x t R : ℝ) : ℂ :=
  (1/(2*Real.pi) : ℂ)*∫ v in {v : ℝ | R < |v|}ᶜ,
    bblrVKernel (polarPoleKiller T σ) α x t ((c : ℂ)+(v : ℂ)*I)

def bblrGaussianSmallVTail (c T : ℝ) (σ α : MomentShifts) (x t R : ℝ) : ℂ :=
  (1/(2*Real.pi) : ℂ)*∫ v in {v : ℝ | R < |v|},
    bblrVKernel (polarPoleKiller T σ) α x t ((c : ℂ)+(v : ℂ)*I)

theorem bblrGaussianSmallV_core_add_tail {c t x : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (ht : 0 ≤ t) (hx : 0 < x)
    (T : ℝ) (σ α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ 1/4) (R : ℝ) :
    bblrV (polarPoleKiller T σ) α x t =
      bblrGaussianSmallVCore c T σ α x t R+bblrGaussianSmallVTail c T σ α x t R := by
  have hi := bblrVKernel_small_vertical_integrable ht hx hc hc1 (polarPoleKiller T σ) α
    (polarPoleKiller_BBLREntireWeight T σ α) hα
  have hs : MeasurableSet {v : ℝ | R < |v|} :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  have he := integral_add_compl hs hi
  rw [bblrV_small_positive_contour ht hx hc hc1 _ _ (polarPoleKiller_BBLREntireWeight T σ α) hα]
  unfold verticalIntegral bblrGaussianSmallVCore bblrGaussianSmallVTail
  rw [← he]
  ring

theorem bblrGaussianVCore_small_positive_contour {c t x : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (ht : 0 ≤ t) (hx : 0 < x)
    (T : ℝ) (σ α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ 1/4) (R : ℝ) :
    bblrGaussianVCore T σ α x t R = bblrGaussianSmallVCore c T σ α x t R+
      (bblrGaussianSmallVTail c T σ α x t R-bblrGaussianVTail T σ α x t R) := by
  have h1 := bblrGaussianV_core_add_tail T σ α x t R hx hα
  have hc' := bblrGaussianSmallV_core_add_tail hc hc1 ht hx T σ α hα R
  linear_combination hc'-h1

theorem bblrVKernel_small_gaussian_majorant :
    ∃ D : ℝ, 0 < D ∧ ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ T : ℝ, ∀ σ α : MomentShifts,
      (∀ j, ‖α j‖ ≤ 1/4) → ∀ t x v : ℝ, 0 ≤ t → 0 < x →
      ‖bblrVKernel (polarPoleKiller T σ) α x t ((c : ℂ)+(v : ℂ)*I)‖ ≤
        (D*polarGaussianConstant T σ c*(2+t)^8*x^(-c)/c)*
          (1+|v|)^56*Real.exp (-v^2) := by
  obtain ⟨C,hC,hΓ⟩ := bblrGammaQuotient_polynomial_positive_strip_bound
  refine ⟨C,hC,?_⟩
  intro c hc hc1 T σ α hα t x v ht hx
  have hCG := polarGaussianConstant_nonneg T σ c
  let z : ℂ := (c : ℂ)+(v : ℂ)*I
  have hz : c ≤ ‖z‖ := by simpa [z,abs_of_pos hc] using Complex.abs_re_le_norm z
  have hg : ‖polarPoleKiller T σ z/z‖ ≤
      polarGaussianConstant T σ c*(1+|v|)^48*Real.exp (-v^2)/c := by
    rw [norm_div]
    exact div_le_div₀ (by positivity) (polarPoleKiller_vertical_norm_le T σ c v) hc hz
  have hπ : ‖(Real.pi : ℂ)^(-2*z)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have he : (-2*z).re = -2*c := by simp [z]
    rw [he]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
  have hxp : ‖(x : ℂ)^(-z)‖ = x^(-c) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    congr 1
    simp [z]
  have hp : (2+t+|v|)^8 ≤ (2+t)^8*(1+|v|)^8 := by
    rw [← mul_pow]
    gcongr
    nlinarith [abs_nonneg v]
  unfold bblrVKernel
  rw [norm_mul,norm_mul,norm_mul,hxp]
  calc
    _ ≤ (polarGaussianConstant T σ c*(1+|v|)^48*Real.exp (-v^2)/c)*
        (C*((2+t)^8*(1+|v|)^8))*1*x^(-c) := by
      gcongr
      exact (hΓ t v c ht hc.le hc1 α hα).trans (mul_le_mul_of_nonneg_left hp hC.le)
    _ = _ := by rw [show (1+|v|)^56=(1+|v|)^48*(1+|v|)^8 by rw [← pow_add]]; ring

theorem bblrGaussianSmallVTail_norm_le :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ T : ℝ, ∀ σ α : MomentShifts,
      (∀ j, ‖α j‖ ≤ 1/4) → ∀ t x R : ℝ, 0 ≤ t → 0 < x → 0 ≤ R →
      ‖bblrGaussianSmallVTail c T σ α x t R‖ ≤
        D*polarGaussianConstant T σ c*(2+t)^8*x^(-c)/c*Real.exp (-(1/2)*R^2) := by
  obtain ⟨C,hC,hbound⟩ := bblrVKernel_small_gaussian_majorant
  have hJ := gaussianTailConstant_nonneg 56
  refine ⟨C*gaussianTailConstant 56/(2*Real.pi),by positivity,?_⟩
  intro c hc hc1 T σ α hα t x R ht hx hR
  have hfi := bblrVKernel_small_vertical_integrable ht hx hc hc1 (polarPoleKiller T σ) α
    (polarPoleKiller_BBLREntireWeight T σ α) hα
  have hCG := polarGaussianConstant_nonneg T σ c
  have htail := gaussian_integral_tail_norm_le
    (fun v => bblrVKernel (polarPoleKiller T σ) α x t ((c : ℂ)+(v : ℂ)*I)) hfi 56
    (by positivity : 0 ≤ C*polarGaussianConstant T σ c*(2+t)^8*x^(-c)/c) hR
    (fun v => hbound c hc hc1 T σ α hα t x v ht hx)
  unfold bblrGaussianSmallVTail
  rw [norm_mul]
  have hn : ‖(1/(2*Real.pi) : ℂ)‖ = 1/(2*Real.pi) := by
    simp [Complex.norm_real,abs_of_pos Real.pi_pos]
  rw [hn]
  calc
    _ ≤ (1/(2*Real.pi))*(C*polarGaussianConstant T σ c*(2+t)^8*x^(-c)/c*
        gaussianTailConstant 56*Real.exp (-(1/2)*R^2)) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = _ := by ring

end
end SixthMoment.Source
