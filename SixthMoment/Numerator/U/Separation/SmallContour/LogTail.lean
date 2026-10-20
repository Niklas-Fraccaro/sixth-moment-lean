import SixthMoment.Numerator.Polar.GaussianLogGrowth
import SixthMoment.Numerator.U.Separation.SmallContour.Gaussian

namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem bblrGaussianSmallVTail_uniform_logarithmic_power_bound
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (K : Set MomentShifts)
    (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ σ ∈ K, ∀ k : PurePolarIndex, δ ≤ ‖normalizedPurePolarRoot σ k‖)
    {θ : ℝ} (hθ : 0 < θ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ α : MomentShifts,
      (∀ j, ‖α j‖ ≤ 1/4) → ∀ t ∈ Icc T (2*T), ∀ x : ℝ, 0 < x →
      ‖bblrGaussianSmallVTail c T σ α x t (θ*Real.log T)‖ ≤ C*T^(-(N : ℝ))*x^(-c) := by
  obtain ⟨D,hD,hbound⟩ := bblrGaussianSmallVTail_norm_le
  let E : ℝ := Real.exp (c^2)*(1+|c|)^48*(1+1/δ^2)^24
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hlog : ∀ᶠ T : ℝ in atTop, (Real.log T)^48 ≤ T := by
    have h := (log_pow_isLittleO_rpow 48 (δ := 1) zero_lt_one).bound zero_lt_one
    filter_upwards [h,eventually_gt_atTop (1 : ℝ)] with T hT hpos
    simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_pos (zero_lt_one.trans hpos),
      abs_of_nonneg (by positivity : 0 ≤ (Real.log T)^48),one_mul] using hT
  refine ⟨D*E*4^8/c,by positivity,?_⟩
  filter_upwards [hlog,polynomial_gaussian_logarithmic_eventually_le hθ 9 N,
    eventually_gt_atTop (1 : ℝ),Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (1 : ℝ))] with T hlog hdec hT hL
  intro σ hσ α hα t ht x hx
  have hCG := polarGaussianConstant_nonneg T σ c
  have hCGb : polarGaussianConstant T σ c ≤ E*T :=
    (SixthMoment.polarGaussianConstant_log_growth hT hL hδ σ c (hρ σ hσ)).trans
      (mul_le_mul_of_nonneg_left hlog hE)
  have htpos : 0 ≤ t := by linarith [ht.1]
  have htime : (2+t)^8 ≤ 4^8*T^8 := by
    rw [← mul_pow]
    gcongr
    linarith [ht.2]
  have hb := hbound c hc hc1 T σ α hα t x (θ*Real.log T) htpos hx
    (mul_nonneg hθ.le (by linarith : 0 ≤ Real.log T))
  calc
    _ ≤ D*(E*T)*(4^8*T^8)*x^(-c)/c*Real.exp (-(1/2)*(θ*Real.log T)^2) := by
      apply hb.trans
      gcongr
    _ = (D*E*4^8/c*x^(-c))*(T^9*Real.exp (-(1/2)*(θ*Real.log T)^2)) := by ring
    _ ≤ (D*E*4^8/c*x^(-c))*T^(-(N : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      convert hdec using 1
      norm_num
    _ = _ := by ring

theorem bblrGaussianVCore_small_positive_uniform_logarithmic_error
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (K : Set MomentShifts)
    (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ σ ∈ K, ∀ k : PurePolarIndex, δ ≤ ‖normalizedPurePolarRoot σ k‖)
    {θ : ℝ} (hθ : 0 < θ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ α : MomentShifts,
      (∀ j, ‖α j‖ ≤ 1/4) → ∀ t ∈ Icc T (2*T), ∀ x : ℝ, 1 ≤ x →
      ‖bblrGaussianVCore T σ α x t (θ*Real.log T)-
        bblrGaussianSmallVCore c T σ α x t (θ*Real.log T)‖ ≤ C*T^(-(N : ℝ))*x^(-c) := by
  obtain ⟨C₀,hC₀,hb₀⟩ := bblrGaussianSmallVTail_uniform_logarithmic_power_bound hc hc1 K δ hδ hρ hθ N
  obtain ⟨C₁,hC₁,hb₁⟩ := bblrGaussianVTail_uniform_logarithmic_power_bound K δ hδ hρ hθ N
  refine ⟨C₀+C₁,by positivity,?_⟩
  filter_upwards [hb₀,hb₁,eventually_gt_atTop (0 : ℝ)] with T hsmall hlarge hT
  intro σ hσ α hα t ht x hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hxp : 1/x ≤ x^(-c) := by
    rw [one_div,← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  rw [bblrGaussianVCore_small_positive_contour hc hc1 ht0 hx0 T σ α hα (θ*Real.log T),
    add_sub_cancel_left]
  calc
    _ ≤ ‖bblrGaussianSmallVTail c T σ α x t (θ*Real.log T)‖+
        ‖bblrGaussianVTail T σ α x t (θ*Real.log T)‖ := norm_sub_le _ _
    _ ≤ C₀*T^(-(N : ℝ))*x^(-c)+C₁*T^(-(N : ℝ))/x :=
      add_le_add (hsmall σ hσ α hα t ht x hx0) (hlarge σ hσ α hα t ht x hx0)
    _ ≤ C₀*T^(-(N : ℝ))*x^(-c)+C₁*T^(-(N : ℝ))*x^(-c) := by
      apply add_le_add le_rfl
      rw [div_eq_mul_inv,← one_div]
      exact mul_le_mul_of_nonneg_left hxp (by positivity)
    _ = _ := by ring

end
end SixthMoment.Source
