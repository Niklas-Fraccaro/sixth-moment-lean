import SixthMoment.Numerator.U.Separation.SmallContour.Grid
import SixthMoment.Numerator.U.Separation.SmallContour.LogTail

namespace SixthMoment
open Complex Source Real MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 1000000

theorem rectangular_small_contour_box_card_le (k : Fin 4 → ℕ) :
    ((rectangularAFESmoothBox k).card : ℝ) ≤
      16*∏ j : Fin 4, rectangularAFESmoothScale (k j) := by
  have hs (j : Fin 4) : 0 ≤ 2*rectangularAFESmoothScale (k j) := by
    unfold rectangularAFESmoothScale
    positivity
  have hp := Finset.prod_le_prod₀
    (s := Finset.univ) (f := fun j : Fin 4 => (⌊2*rectangularAFESmoothScale (k j)⌋₊ : ℝ))
    (g := fun j : Fin 4 => 2*rectangularAFESmoothScale (k j))
    (fun _ _ => Nat.cast_nonneg _) (fun j _ => Nat.floor_le (hs j))
  unfold rectangularAFESmoothBox
  rw [Fintype.card_piFinset]
  push_cast
  simpa [Finset.prod_mul_distrib,show (2:ℝ)^4 = 16 by norm_num] using hp

theorem rectangular_small_contour_grid_card_le (X : ℝ) :
    (∑ k∈rectangularAFEProductScaleGrid X, ((rectangularAFESmoothBox k).card : ℝ)) ≤
      16*X*((rectangularAFEProductScaleGrid X).card : ℝ) := by
  calc
    _ ≤ ∑ _k∈rectangularAFEProductScaleGrid X, 16*X := by
      apply Finset.sum_le_sum
      intro k hk
      exact (rectangular_small_contour_box_card_le k).trans
        (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hk).2 (by norm_num))
    _ = _ := by simp [mul_comm]

theorem rectangular_small_contour_grid_uniform_polynomial_card {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      (∑ k∈rectangularAFEProductScaleGrid (T^(2+ε)), ((rectangularAFESmoothBox k).card : ℝ)) ≤
        C*T^(3+ε) := by
  obtain ⟨D,hD,hgrid⟩ := rectangular_AFE_product_scale_grid_uniform_log_card hε
  refine ⟨16*D*(24*Real.exp 1),by positivity,?_⟩
  filter_upwards [hgrid,eventually_ge_atTop (1 : ℝ)] with T hcard hT
  have ht : 0 < T := zero_lt_one.trans_le hT
  have hlog : (1+Real.log T)^4 ≤ (24*Real.exp 1)*T := by
    convert logarithmic_power_le_rpow (κ := 1) zero_lt_one hT 4 using 1
    norm_num
  calc
    _ ≤ 16*T^(2+ε)*((rectangularAFEProductScaleGrid (T^(2+ε))).card : ℝ) :=
      rectangular_small_contour_grid_card_le _
    _ ≤ 16*T^(2+ε)*(D*((24*Real.exp 1)*T)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hcard.trans (mul_le_mul_of_nonneg_left hlog hD)
    _ = (16*D*(24*Real.exp 1))*T^(3+ε) := by
      rw [show (3 : ℝ)+ε = (2+ε)+1 by ring,Real.rpow_add ht (2+ε) 1,Real.rpow_one]
      ring

theorem rectangular_small_contour_smooth_weight_le_one (k n : Fin 4 → ℕ) :
    rectangularAFESmoothWeight k n ≤ 1 := by
  unfold rectangularAFESmoothWeight
  have h := Finset.prod_le_prod₀
    (fun j (_ : j∈(Finset.univ : Finset (Fin 4))) => rectangularSmoothBlockWeight_nonneg _)
    (fun j (_ : j∈(Finset.univ : Finset (Fin 4))) => rectangularSmoothBlockWeight_le_one
      ((3/2)*(n j+1:ℝ)/(3/2)^(k j)))
  simpa only [Finset.prod_const_one] using h

theorem rectangular_actual_small_contour_summand_error_le
    (c T : ℝ) (σ α : MomentShifts) (t R : ℝ) (hα : ∀ j, ‖α j‖ ≤ 1/4)
    {B : ℝ} (hB : 0 ≤ B)
    (hV : ∀ x : ℝ, 1 ≤ x → ‖bblrGaussianVCore T σ α x t R-
      bblrGaussianSmallVCore c T σ α x t R‖ ≤ B)
    (n : Fin 4 → ℕ) :
    ‖bblrGaussianAFECoreSummand T σ α t R n-
      bblrGaussianSmallAFECoreSummand c T σ α t R n‖ ≤ B := by
  have hn (j : Fin 4) : 1 ≤ (n j+1 : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) (n j)]
  have hx : 1 ≤ (positiveQuadProduct n : ℝ) := by
    rw [positiveQuadProduct_eq_prod]
    push_cast
    have hh := Finset.prod_le_prod₀ (s := Finset.univ)
      (f := fun _ : Fin 4 => (1:ℝ)) (g := fun j => (n j+1:ℝ))
      (fun _ _ => zero_le_one) (fun j _ => hn j)
    simpa only [Finset.prod_const_one] using hh
  have hcp (j : Fin 4) : ‖(n j+1 : ℂ)^(1/2+α j)‖ =
      (n j+1 : ℝ)^(1/2+(α j).re) := by
    rw [show (n j+1 : ℂ) = ((n j+1 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le (hn j))]
    congr 1
    simp
  have hden : 1 ≤ ‖∏ j : Fin 4, (n j+1 : ℂ)^(1/2+α j)‖ := by
    rw [norm_prod]
    simp_rw [hcp]
    have hh := Finset.prod_le_prod₀ (s := Finset.univ)
      (f := fun _ : Fin 4 => (1:ℝ))
      (g := fun j => (n j+1:ℝ)^(1/2+(α j).re)) (fun _ _ => zero_le_one) (fun j _ => by
        have ha := (abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))).1
        exact Real.one_le_rpow (hn j) (by linarith))
    simpa only [Finset.prod_const_one] using hh
  have he : bblrGaussianAFECoreSummand T σ α t R n-
      bblrGaussianSmallAFECoreSummand c T σ α t R n =
      rectangularAFEOscillation t n*(bblrGaussianVCore T σ α (positiveQuadProduct n) t R-
        bblrGaussianSmallVCore c T σ α (positiveQuadProduct n) t R)/
          ∏ j : Fin 4, (n j+1 : ℂ)^(1/2+α j) := by
    unfold bblrGaussianAFECoreSummand bblrGaussianSmallAFECoreSummand rectangularAFEOscillation
    ring
  rw [he,norm_div,norm_mul]
  have ho : ‖rectangularAFEOscillation t n‖ = 1 := bblrAFE_oscillation_norm_one n t
  rw [ho,one_mul]
  exact (div_le_div_of_nonneg_right (hV _ hx) (zero_lt_one.trans_le hden).le).trans
    (div_le_self hB hden)

theorem rectangular_actual_finite_small_contour_error_card_le
    (c T : ℝ) (σ α : MomentShifts) (t X R : ℝ) (hα : ∀ j, ‖α j‖ ≤ 1/4)
    {B : ℝ} (hB : 0 ≤ B)
    (hV : ∀ x : ℝ, 1 ≤ x → ‖bblrGaussianVCore T σ α x t R-
      bblrGaussianSmallVCore c T σ α x t R‖ ≤ B) :
    ‖rectangularFiniteGaussianCore T σ α t X R-
      rectangularFiniteSmallGaussianCore c T σ α t X R‖ ≤
      B*(∑ k∈rectangularAFEProductScaleGrid X, ((rectangularAFESmoothBox k).card : ℝ)) := by
  unfold rectangularFiniteGaussianCore rectangularFiniteSmallGaussianCore
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib,← mul_sub]
  calc
    _ ≤ ∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
        ‖(rectangularAFESmoothWeight k n : ℂ)*(bblrGaussianAFECoreSummand T σ α t R n-
          bblrGaussianSmallAFECoreSummand c T σ α t R n)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => norm_sum_le _ _))
    _ ≤ ∑ k∈rectangularAFEProductScaleGrid X, ∑ _n∈rectangularAFESmoothBox k, B := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro n _
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (rectangular_AFE_smooth_weight_nonneg k n)]
      calc
        _ ≤ rectangularAFESmoothWeight k n*B := mul_le_mul_of_nonneg_left
          (rectangular_actual_small_contour_summand_error_le c T σ α t R hα hB hV n)
          (rectangular_AFE_smooth_weight_nonneg k n)
        _ ≤ B := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right
            (rectangular_small_contour_smooth_weight_le_one k n) hB
    _ = _ := by simp [Finset.mul_sum,mul_comm]

end
