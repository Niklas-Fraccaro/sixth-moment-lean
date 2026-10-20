import Mathlib.Analysis.Calculus.ContDiff.Bounds
import SixthMoment.Numerator.U.Separation.Tensor.CompactSeminorms
import SixthMoment.Numerator.U.Separation.Tensor.LogCutoff

namespace SixthMoment
open Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem phase_localized_kernel_contDiff {χ P : E → ℂ} {U : Set E}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hU : IsOpen U)
    (hs : tsupport χ ⊆ U) (hP : ContDiffOn ℝ (⊤ : ℕ∞) P U) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y*P y) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x∈tsupport χ
  · exact hχ.contDiffAt.mul ((hP x (hs hx)).contDiffAt (hU.mem_nhds (hs hx)))
  · have he : (fun y => χ y*P y)=ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
      have hz : χ y=0 := Function.notMem_support.mp (fun hh => hy (subset_tsupport _ hh))
      simp only [hz, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

def phaseLocalizedKernelDerivativeBudget (C B : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i∈Finset.range (n+1), (n.choose i:ℝ)*C i*B (n-i)

theorem phase_localized_kernel_derivative_bound {χ P : E → ℂ} {U : Set E}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hU : IsOpen U)
    (hs : tsupport χ ⊆ U) (hP : ContDiffOn ℝ (⊤ : ℕ∞) P U)
    (C B : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n) (hB : ∀ n, 0 ≤ B n)
    (hχd : ∀ n x, ‖iteratedFDeriv ℝ n χ x‖ ≤ C n)
    {D : ℝ} (hD : 0 ≤ D)
    (hPd : ∀ n x, x∈tsupport χ → ‖iteratedFDeriv ℝ n P x‖ ≤ B n*D)
    (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => χ y*P y) x‖ ≤
      phaseLocalizedKernelDerivativeBudget C B n*D := by
  have hb : 0 ≤ phaseLocalizedKernelDerivativeBudget C B n := by
    unfold phaseLocalizedKernelDerivativeBudget
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC i)) (hB (n-i)))
  by_cases hx : x∈tsupport χ
  · have hxU := hs hx
    have hm := norm_iteratedFDerivWithin_mul_le hχ.contDiffOn hP
      hU.uniqueDiffOn hxU (n := n) (by simp)
    simp_rw [iteratedFDerivWithin_of_isOpen _ hU hxU] at hm
    apply hm.trans
    calc
      _ ≤ ∑ i∈Finset.range (n+1), (n.choose i:ℝ)*C i*(B (n-i)*D) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hχd i x) (Nat.cast_nonneg _))
          (hPd (n-i) x hx) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hC i))
      _ = _ := by unfold phaseLocalizedKernelDerivativeBudget; rw [Finset.sum_mul]; congr 1; ext i; ring
  · have hz : iteratedFDeriv ℝ n (fun y => χ y*P y) x=0 := by
      apply Function.notMem_support.mp
      intro hh
      apply hx
      exact (tsupport_mul_subset_left.trans (by rfl))
        (tsupport_iteratedFDeriv_subset n (subset_tsupport _ hh))
    rw [hz, norm_zero]
    exact mul_nonneg hb hD

theorem phase_localized_uniform_schwartz_family {ι : Type*}
    (χ : E → ℂ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hK : HasCompactSupport χ)
    {U : Set E} (hU : IsOpen U) (hs : tsupport χ ⊆ U)
    (P : ι → E → ℂ) (hP : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (P i) U)
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n)
    (hPd : ∀ n i x, x∈tsupport χ → ‖iteratedFDeriv ℝ n (P i) x‖ ≤ B n)
    {R : ℝ} (hR : 0 ≤ R) (hball : ∀ x, x∈tsupport χ → ‖x‖ ≤ R) :
    ∃ f : ι → SchwartzMap E ℂ,
      (∀ i x, f i x=χ x*P i x) ∧
      ∀ k n : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ i,
        SchwartzMap.seminorm ℂ k n (f i) ≤ D := by
  have hc (i : ι) : HasCompactSupport (fun x => χ x*P i x) := hK.mul_right
  have hd (i : ι) : ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x*P i x) :=
    phase_localized_kernel_contDiff hχ hU hs (hP i)
  let g : SchwartzMap E ℂ := hK.toSchwartzMap hχ
  let C : ℕ → ℝ := fun n => SchwartzMap.seminorm ℂ 0 n g
  have hC (n : ℕ) : 0 ≤ C n := apply_nonneg _ _
  have hCd (n : ℕ) (x : E) : ‖iteratedFDeriv ℝ n χ x‖ ≤ C n :=
    g.norm_iteratedFDeriv_le_seminorm ℂ n x
  refine ⟨fun i => (hc i).toSchwartzMap (hd i), fun _ _ => rfl, ?_⟩
  apply a03Compact_uniform_schwartz_seminorms _ hc hd hR
  · intro i x hx
    exact hball x (tsupport_mul_subset_left hx)
  · intro n
    have hbudget : 0 ≤ phaseLocalizedKernelDerivativeBudget C B n := by
      unfold phaseLocalizedKernelDerivativeBudget
      exact Finset.sum_nonneg (fun i _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC i)) (hB (n-i)))
    refine ⟨phaseLocalizedKernelDerivativeBudget C B n, hbudget, ?_⟩
    intro i x
    simpa only [mul_one] using phase_localized_kernel_derivative_bound hχ hU hs
      (hP i) C B hC hB hCd (by norm_num : (0:ℝ) ≤ 1)
      (fun j y hy => by simpa only [mul_one] using hPd j i y hy) n x

end
end SixthMoment
