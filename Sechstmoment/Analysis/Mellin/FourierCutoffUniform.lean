import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Sechstmoment.Analysis.Mellin.FourierCutoff

/-! Uniform derivative masses for the concrete frequency truncations.
Together with the unweighted tail estimate these control the full-time
truncation error by splitting at a large polynomial time cutoff. -/

namespace Sechstmoment.Source
open Complex Real Set MeasureTheory
open scoped ContDiff BigOperators
noncomputable section

def noDPFrequencyBumpSchwartz : SchwartzMap ℝ ℂ := by
  let f : ℝ → ℂ := fun x => (noDPFrequencyBump x:ℂ)
  have hsub : tsupport f ⊆ tsupport (noDPFrequencyBump:ℝ → ℝ) := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    apply subset_tsupport
    intro hzero
    apply hx
    simp [f,hzero]
  have hK : HasCompactSupport f :=
    noDPFrequencyBump.hasCompactSupport.of_isClosed_subset (isClosed_tsupport f) hsub
  exact hK.toSchwartzMap (Complex.ofRealCLM.contDiff.comp noDPFrequencyBump.contDiff)

@[simp] theorem noDPFrequencyBumpSchwartz_coe :
    (noDPFrequencyBumpSchwartz : ℝ → ℂ) = fun x => (noDPFrequencyBump x:ℂ) := rfl

theorem scaled_frequency_bump_derivative_bound {H : ℝ} (hH : 1 ≤ H) (n : ℕ) (ξ : ℝ) :
    ‖iteratedDeriv n (fun x : ℝ => (noDPFrequencyBump (x/H):ℂ)) ξ‖ ≤
      SchwartzMap.seminorm ℂ 0 n noDPFrequencyBumpSchwartz := by
  have hH0 : 0 < H := by linarith
  have he : (fun x : ℝ => (noDPFrequencyBump (x/H):ℂ)) =
      fun x : ℝ => noDPFrequencyBumpSchwartz (H⁻¹*x) := by
    funext x
    rw [noDPFrequencyBumpSchwartz_coe]
    congr 2
    ring
  have hd := congrFun
    (iteratedDeriv_comp_const_smul (noDPFrequencyBumpSchwartz.smooth n) (H⁻¹)) ξ
  have hscale : ‖H⁻¹‖ ≤ 1 := by
    rw [Real.norm_eq_abs,abs_inv,abs_of_pos hH0,← one_div]
    exact (div_le_one hH0).mpr hH
  have hbase : ‖iteratedDeriv n noDPFrequencyBumpSchwartz (H⁻¹*ξ)‖ ≤
      SchwartzMap.seminorm ℂ 0 n noDPFrequencyBumpSchwartz := by
    simpa only [pow_zero,one_mul] using
      SchwartzMap.le_seminorm' ℂ 0 n noDPFrequencyBumpSchwartz (H⁻¹*ξ)
  rw [he,hd,norm_smul,norm_pow]
  calc
    _ ≤ 1^n*SchwartzMap.seminorm ℂ 0 n noDPFrequencyBumpSchwartz :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hscale n) hbase (norm_nonneg _) (by positivity)
    _ = _ := by simp

theorem schwartz_iteratedDeriv_norm_integrable (h : SchwartzMap ℝ ℂ) (n : ℕ) :
    Integrable (fun ξ : ℝ => ‖iteratedDeriv n h ξ‖) := by
  simpa only [pow_zero,one_mul,norm_iteratedFDeriv_eq_norm_iteratedDeriv] using
    h.integrable_pow_mul_iteratedFDeriv volume 0 n

def noDPFourierCutoffDerivativeMajorant (h : SchwartzMap ℝ ℂ) (n : ℕ) (ξ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), (n.choose j:ℝ)*
    SchwartzMap.seminorm ℂ 0 (n-j) noDPFrequencyBumpSchwartz*‖iteratedDeriv j h ξ‖

theorem noDPFourierCutoff_derivative_pointwise (h : SchwartzMap ℝ ℂ)
    {H : ℝ} (hH : 1 ≤ H) (n : ℕ) (ξ : ℝ) :
    ‖iteratedDeriv n (noDPFourierCutoff h H) ξ‖ ≤ noDPFourierCutoffDerivativeMajorant h n ξ := by
  let b : ℝ → ℂ := fun x => (noDPFrequencyBump (x/H):ℂ)
  have hb : ContDiff ℝ ∞ b := Complex.ofRealCLM.contDiff.comp
    (noDPFrequencyBump.contDiff.comp (by fun_prop))
  change ‖iteratedDeriv n ((h:ℝ → ℂ)*b) ξ‖ ≤ _
  rw [iteratedDeriv_mul (h.smooth n).contDiffAt (hb.of_le (by simp)).contDiffAt]
  apply (norm_sum_le _ _).trans
  unfold noDPFourierCutoffDerivativeMajorant
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul,norm_mul,Complex.norm_natCast]
  calc
    _ ≤ (n.choose j:ℝ)*‖iteratedDeriv j h ξ‖*
        SchwartzMap.seminorm ℂ 0 (n-j) noDPFrequencyBumpSchwartz := by
      apply mul_le_mul_of_nonneg_left (scaled_frequency_bump_derivative_bound hH (n-j) ξ)
      positivity
    _ = _ := by ring

theorem noDPFourierCutoff_uniform_derivative_mass (h : SchwartzMap ℝ ℂ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 1 ≤ H →
      (∫ ξ : ℝ, ‖iteratedDeriv n (noDPFourierCutoff h H) ξ‖) ≤ C := by
  have hi : Integrable (noDPFourierCutoffDerivativeMajorant h n) := by
    apply integrable_finsetSum
    intro j _
    exact (schwartz_iteratedDeriv_norm_integrable h j).const_mul _
  let J := ∫ ξ : ℝ, noDPFourierCutoffDerivativeMajorant h n ξ
  refine ⟨max 1 J,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro H hH
  have hH0 : 0 < H := by linarith
  have hd := schwartz_iteratedDeriv_norm_integrable (noDPFourierCutoffSchwartz h H hH0) n
  have hd' : Integrable (fun ξ : ℝ => ‖iteratedDeriv n (noDPFourierCutoff h H) ξ‖) := hd
  apply (integral_mono hd' hi (noDPFourierCutoff_derivative_pointwise h hH n)).trans
  exact le_max_right _ _

end
end Sechstmoment.Source
