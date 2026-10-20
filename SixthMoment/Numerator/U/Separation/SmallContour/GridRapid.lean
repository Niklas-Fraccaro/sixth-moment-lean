import SixthMoment.Numerator.U.Separation.SmallContour.GridBounds

namespace SixthMoment
open Complex Source Real MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem rectangular_actual_finite_small_contour_uniform_rapid_error
    {c ε θ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hε : 0 < ε) (hθ : 0 < θ)
    (K : Set MomentShifts) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ σ ∈ K, ∀ k : PurePolarIndex, δ ≤ ‖normalizedPurePolarRoot σ k‖)
    (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ α : MomentShifts,
      (∀ j, ‖α j‖ ≤ 1/4) → ∀ t ∈ Icc T (2*T),
      ‖rectangularFiniteGaussianCore T σ α t (T^(2+ε)) (θ*Real.log T)-
        rectangularFiniteSmallGaussianCore c T σ α t (T^(2+ε)) (θ*Real.log T)‖ ≤ C*T^(-M) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (M+3+ε)
  obtain ⟨C₀,hC₀,hV⟩ := bblrGaussianVCore_small_positive_uniform_logarithmic_error
    hc hc1 K δ hδ hρ hθ N
  obtain ⟨D,hD,hcard⟩ := rectangular_small_contour_grid_uniform_polynomial_card hε
  refine ⟨C₀*D,mul_nonneg hC₀ hD,?_⟩
  filter_upwards [hV,hcard,eventually_ge_atTop (1 : ℝ)] with T hV hcard hT
  intro σ hσ α hα t ht
  have ht0 : 0 < T := zero_lt_one.trans_le hT
  have hB : 0 ≤ C₀*T^(-(N : ℝ)) := by positivity
  have hV' (x : ℝ) (hx : 1 ≤ x) : ‖bblrGaussianVCore T σ α x t (θ*Real.log T)-
      bblrGaussianSmallVCore c T σ α x t (θ*Real.log T)‖ ≤ C₀*T^(-(N : ℝ)) := by
    have hp := Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith : -c ≤ 0)
    exact (hV σ hσ α hα t ht x hx).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hB)
  calc
    _ ≤ (C₀*T^(-(N : ℝ)))*(∑ k∈rectangularAFEProductScaleGrid (T^(2+ε)),
        ((rectangularAFESmoothBox k).card : ℝ)) :=
      rectangular_actual_finite_small_contour_error_card_le c T σ α t _ _ hα hB hV'
    _ ≤ (C₀*T^(-(N : ℝ)))*(D*T^(3+ε)) := mul_le_mul_of_nonneg_left hcard hB
    _ = (C₀*D)*T^((3+ε)-(N : ℝ)) := by
      rw [sub_eq_add_neg,Real.rpow_add ht0 (3+ε) (-(N:ℝ))]
      ring
    _ ≤ (C₀*D)*T^(-M) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC₀ hD)
      exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)

theorem rectangular_actual_AFE_finite_small_gaussian_grid
    (c T : ℝ) (σ α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ 1/4) (t X R : ℝ) :
    bblrAFESum (polarPoleKiller T σ) α t =
      rectangularFiniteSmallGaussianCore c T σ α t X R+
        (rectangularFiniteGaussianRemainder T σ α t X R+
          (rectangularFiniteGaussianCore T σ α t X R-
            rectangularFiniteSmallGaussianCore c T σ α t X R)) := by
  rw [rectangular_actual_AFE_finite_gaussian_grid T σ α hα t X R]
  ring

end
