import SixthMoment.Numerator.U.Separation.ActualSeparatedMellinGrid
import SixthMoment.Numerator.U.Separation.SmallContour.Gaussian

namespace SixthMoment
open Complex Source Real MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 1000000

def bblrGaussianSmallAFECoreSummand (c T : ℝ) (σ α : MomentShifts)
    (t R : ℝ) (n : Fin 4 → ℕ) : ℂ :=
  rectangularAFEOscillation t n*bblrGaussianSmallVCore c T σ α (positiveQuadProduct n) t R/
    ∏ j : Fin 4, (n j+1 : ℂ)^(1/2+α j)

def rectangularFiniteSmallGaussianCore (c T : ℝ) (σ α : MomentShifts) (t X R : ℝ) : ℂ :=
  ∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
    (rectangularAFESmoothWeight k n : ℂ)*bblrGaussianSmallAFECoreSummand c T σ α t R n

theorem rectangular_AFE_Mellin_kernel_general_line (G : ℂ → ℂ) (α : MomentShifts)
    (t : ℝ) (n : Fin 4 → ℕ) (z : ℂ) :
    rectangularAFEMellinKernel G α t n z =
      (rectangularAFEOscillation t n/∏ j : Fin 4, (n j+1 : ℂ)^(1/2+α j))*
        bblrVKernel G α (positiveQuadProduct n) t z := by
  have hpow := rectangular_AFE_Mellin_powers α n z
  dsimp [rectangularAFEMellinKernel,bblrVKernel]
  have hp := congrArg (fun w : ℂ =>
    (G z/z*bblrGammaQuotient t α z*(Real.pi : ℂ)^(-2*z)*rectangularAFEOscillation t n)*w) hpow
  convert hp.symm using 1 <;> ring

theorem rectangular_AFE_Mellin_kernel_small_line_integrable {c t : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (ht : 0 ≤ t)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, ‖α j‖ ≤ 1/4) (n : Fin 4 → ℕ) :
    Integrable (fun v : ℝ => rectangularAFEMellinKernel G α t n ((c : ℂ)+(v : ℂ)*I)) := by
  have hx : 0 < (positiveQuadProduct n : ℝ) := by unfold positiveQuadProduct; positivity
  have hi := bblrVKernel_small_vertical_integrable ht hx hc hc1 G α hG hα
  simpa only [rectangular_AFE_Mellin_kernel_general_line] using hi.const_mul
    (rectangularAFEOscillation t n/∏ j : Fin 4, (n j+1 : ℂ)^(1/2+α j))

theorem rectangular_actual_small_Gaussian_core_summand_Mellin (c T : ℝ)
    (σ α : MomentShifts) (t R : ℝ) (n : Fin 4 → ℕ) :
    bblrGaussianSmallAFECoreSummand c T σ α t R n = (1/(2*Real.pi) : ℂ)*
      ∫ v in Icc (-R) R,
        rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c : ℂ)+(v : ℂ)*I) := by
  have hset : {v : ℝ | R < |v|}ᶜ = Icc (-R) R := by
    ext v
    simp only [Set.mem_compl_iff,Set.mem_ofPred_eq,not_lt,Set.mem_Icc]
    exact abs_le
  unfold bblrGaussianSmallAFECoreSummand bblrGaussianSmallVCore
  rw [hset]
  simp_rw [rectangular_AFE_Mellin_kernel_general_line]
  rw [integral_const_mul]
  ring

theorem rectangular_actual_finite_small_Gaussian_grid_Mellin {c t : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (ht : 0 ≤ t) (T : ℝ) (σ α : MomentShifts)
    (hα : ∀ j, ‖α j‖ ≤ 1/4) (X R : ℝ) :
    rectangularFiniteSmallGaussianCore c T σ α t X R = (1/(2*Real.pi) : ℂ)*
      ∫ v in Icc (-R) R, ∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
        (rectangularAFESmoothWeight k n : ℂ)*
          rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c : ℂ)+(v : ℂ)*I) := by
  have hi (k n : Fin 4 → ℕ) : IntegrableOn (fun v : ℝ =>
      (rectangularAFESmoothWeight k n : ℂ)*
        rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c : ℂ)+(v : ℂ)*I)) (Icc (-R) R) :=
    ((rectangular_AFE_Mellin_kernel_small_line_integrable hc hc1 ht _ α
      (polarPoleKiller_BBLREntireWeight T σ α) hα n).const_mul _).integrableOn
  rw [integral_finsetSum]
  · simp_rw [integral_finsetSum _ (fun n _ => hi _ n)]
    unfold rectangularFiniteSmallGaussianCore
    simp_rw [rectangular_actual_small_Gaussian_core_summand_Mellin,integral_const_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro n _
    ring
  · intro k _
    exact integrable_finsetSum _ (fun n _ => hi k n)

end
