import Sechstmoment.Numerator.U.Separation.FiniteGaussianGrid
import Sechstmoment.Numerator.U.Separation.LogarithmicMellinWeights


namespace Sechstmoment
open Complex Source Real Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 1000000

theorem rectangularAFESmoothWeight_scaled_arguments (k n : Fin 4 → ℕ) :
    rectangularAFESmoothWeight k n=
      ∏ j : Fin 4, rectangularSmoothBlockWeight ((n j+1 : ℝ)/rectangularAFESmoothScale (k j)) := by
  apply Finset.prod_congr rfl
  intro j _
  unfold rectangularAFESmoothScale
  congr 1
  field_simp

theorem positive_cpow_scale_identity (s : ℂ) {M x : ℝ} (hM : 0<M) (hx : 0<x) :
    (x:ℂ)^s=(M:ℂ)^s*((x/M:ℝ):ℂ)^s := by
  rw [← Complex.mul_cpow_ofReal_nonneg hM.le (div_nonneg hx.le hM.le) s,
    ← Complex.ofReal_mul]
  congr 1
  rw [mul_div_cancel₀ x hM.ne']

theorem rectangular_actual_smooth_AFE_Mellin_weights (G : ℂ → ℂ)
    (α : MomentShifts) (t : ℝ) (k n : Fin 4 → ℕ) (z : ℂ) :
    (rectangularAFESmoothWeight k n : ℂ)*rectangularAFEMellinKernel G α t n z=
      (G z/z*bblrGammaQuotient t α z*(Real.pi:ℂ)^(-2*z))*
        (∏ j : Fin 4, (rectangularAFESmoothScale (k j):ℂ)^(-(1/2+α j+z)))*
        (rectangularAFEOscillation t n*∏ j : Fin 4,
          rectangularActualMellinBlockWeight α z j
            ((n j+1 : ℝ)/rectangularAFESmoothScale (k j))) := by
  have hp :
      (∏ j : Fin 4, (rectangularAFESmoothScale (k j):ℂ)^(-(1/2+α j+z)))*
        (∏ j : Fin 4, rectangularActualMellinBlockWeight α z j
          ((n j+1 : ℝ)/rectangularAFESmoothScale (k j))) =
      (rectangularAFESmoothWeight k n : ℂ)*
        ∏ j : Fin 4, (n j+1 : ℂ)^(-(1/2+α j+z)) := by
    rw [rectangularAFESmoothWeight_scaled_arguments]
    push_cast
    rw [← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    have hM : 0<rectangularAFESmoothScale (k j) := by unfold rectangularAFESmoothScale; positivity
    have he := positive_cpow_scale_identity (-(1/2+α j+z)) hM (by positivity : 0<(n j+1:ℝ))
    push_cast at he
    unfold rectangularActualMellinBlockWeight rectangularMellinBlockWeight
    push_cast
    rw [he]
    ring
  unfold rectangularAFEMellinKernel
  rw [div_eq_mul_inv,← Finset.prod_inv_distrib]
  simp_rw [← Complex.cpow_neg]
  calc
    _ = (G z/z*bblrGammaQuotient t α z*(Real.pi:ℂ)^(-2*z))*
      rectangularAFEOscillation t n*((rectangularAFESmoothWeight k n : ℂ)*
        ∏ j : Fin 4, (n j+1:ℂ)^(-(1/2+α j+z))) := by ring
    _ = _ := by rw [← hp]; ring

theorem rectangular_actual_Gaussian_core_summand_Mellin (T : ℝ) (σ α : MomentShifts)
    (t R : ℝ) (n : Fin 4 → ℕ) :
    bblrGaussianAFECoreSummand T σ α t R n=(1/(2*Real.pi):ℂ)*
      ∫ v in Icc (-R) R, rectangularAFEMellinKernel (polarPoleKiller T σ) α t n (1+(v:ℂ)*I) := by
  have hset : { v : ℝ | R < |v| }ᶜ=Icc (-R) R := by
    ext v
    simp only [Set.mem_compl_iff,Set.mem_ofPred_eq,not_lt,Set.mem_Icc]
    exact abs_le
  unfold bblrGaussianAFECoreSummand bblrGaussianVCore
  rw [hset]
  simp_rw [rectangular_AFE_Mellin_kernel_line]
  rw [integral_const_mul]
  unfold rectangularAFEOscillation
  ring

theorem rectangular_actual_finite_Gaussian_grid_Mellin (T : ℝ) (σ α : MomentShifts)
    (hα : ∀ j, -1/2<(α j).re) (t X R : ℝ) :
    rectangularFiniteGaussianCore T σ α t X R=(1/(2*Real.pi):ℂ)*
      ∫ v in Icc (-R) R, ∑ k∈rectangularAFEProductScaleGrid X,
        ∑ n∈rectangularAFESmoothBox k, (rectangularAFESmoothWeight k n : ℂ)*
          rectangularAFEMellinKernel (polarPoleKiller T σ) α t n (1+(v:ℂ)*I) := by
  have hi (k n : Fin 4 → ℕ) : IntegrableOn (fun v : ℝ =>
      (rectangularAFESmoothWeight k n : ℂ)*
        rectangularAFEMellinKernel (polarPoleKiller T σ) α t n (1+(v:ℂ)*I)) (Icc (-R) R) :=
    ((rectangular_AFE_Mellin_kernel_integrable _ α (polarPoleKiller_BBLREntireWeight T σ α)
      t hα n).const_mul _).integrableOn
  rw [integral_finsetSum]
  · simp_rw [integral_finsetSum _ (fun n _ => hi _ n)]
    unfold rectangularFiniteGaussianCore
    simp_rw [rectangular_actual_Gaussian_core_summand_Mellin,integral_const_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro n _
    ring
  · intro k _
    exact integrable_finsetSum _ (fun n _ => hi k n)

theorem rectangular_actual_finite_Gaussian_grid_separated (T : ℝ) (σ α : MomentShifts)
    (hα : ∀ j, -1/2<(α j).re) (t X R : ℝ) :
    rectangularFiniteGaussianCore T σ α t X R=(1/(2*Real.pi):ℂ)*
      ∫ v in Icc (-R) R, ∑ k∈rectangularAFEProductScaleGrid X,
        (polarPoleKiller T σ (1+(v:ℂ)*I)/(1+(v:ℂ)*I)*
          bblrGammaQuotient t α (1+(v:ℂ)*I)*(Real.pi:ℂ)^(-2*(1+(v:ℂ)*I)))*
        (∏ j : Fin 4, (rectangularAFESmoothScale (k j):ℂ)^(-(1/2+α j+(1+(v:ℂ)*I))))*
        ∑ n∈rectangularAFESmoothBox k, rectangularAFEOscillation t n*
          ∏ j : Fin 4, rectangularActualMellinBlockWeight α (1+(v:ℂ)*I) j
            ((n j+1 : ℝ)/rectangularAFESmoothScale (k j)) := by
  rw [rectangular_actual_finite_Gaussian_grid_Mellin T σ α hα t X R]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with v
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [rectangular_actual_smooth_AFE_Mellin_weights]
  rw [Finset.mul_sum]

end
end Sechstmoment
