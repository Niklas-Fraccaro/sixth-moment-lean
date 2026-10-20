import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic
import Mathlib.Topology.UniformSpace.UniformConvergence


namespace SixthMoment

open Complex Filter Set
open scoped Topology

noncomputable section

def polarRegularizedZeta : ℂ → ℂ :=
  Function.update (fun s : ℂ => (s-1)*riemannZeta s) 1 1

@[simp] theorem polarRegularizedZeta_one : polarRegularizedZeta 1 = 1 := by
  simp [polarRegularizedZeta]

theorem polarRegularizedZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    polarRegularizedZeta s = (s-1)*riemannZeta s := by
  simp [polarRegularizedZeta, Function.update_of_ne hs]

theorem polarRegularizedZeta_continuousAt_one :
    ContinuousAt polarRegularizedZeta 1 := by
  exact continuousAt_update_same.mpr riemannZeta_residue_one

theorem polarRegularizedZeta_differentiableAt_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ polarRegularizedZeta s := by
  have heq : polarRegularizedZeta =ᶠ[𝓝 s] (fun w : ℂ => (w-1)*riemannZeta w) := by
    filter_upwards [eventually_ne_nhds hs] with w hw
    exact polarRegularizedZeta_of_ne_one hw
  exact (((differentiableAt_id.sub_const 1).mul
    (differentiableAt_riemannZeta hs)).congr_of_eventuallyEq heq)

theorem polarRegularizedZeta_differentiable : Differentiable ℂ polarRegularizedZeta := by
  intro s
  by_cases hs : s = 1
  · subst s
    apply (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      ?_ polarRegularizedZeta_continuousAt_one).differentiableAt
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact polarRegularizedZeta_differentiableAt_of_ne_one hs
  · exact polarRegularizedZeta_differentiableAt_of_ne_one hs

theorem polarRegularizedZeta_continuous : Continuous polarRegularizedZeta :=
  polarRegularizedZeta_differentiable.continuous

theorem scaled_riemannZeta_eq_regularized {L : ℝ} (hL : L ≠ 0)
    {w : ℂ} (hw : w ≠ 0) :
    riemannZeta (1+w/(L:ℂ))/(L:ℂ) = polarRegularizedZeta (1+w/(L:ℂ))/w := by
  have hLc : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  have hs : 1+w/(L:ℂ) ≠ 1 := by
    simpa using div_ne_zero hw hLc
  rw [polarRegularizedZeta_of_ne_one hs]
  field_simp
  ring

theorem polarRegularizedZeta_scaled_uniform {K : Set ℂ} (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn (fun L : ℝ => fun w : ℂ => polarRegularizedZeta (1+w/(L:ℂ)))
      (fun _ => 1) atTop K := by
  obtain ⟨C, hC, hbound⟩ := hK.exists_pos_norm_le
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp
    polarRegularizedZeta_continuousAt_one ε hε
  filter_upwards [eventually_gt_atTop (max 1 (C/δ))] with L hL w hw
  have hLp : 0 < L := lt_trans zero_lt_one (lt_of_le_of_lt (le_max_left _ _) hL)
  have hLC : C/δ < L := lt_of_le_of_lt (le_max_right _ _) hL
  have hsmall : dist (1+w/(L:ℂ)) 1 < δ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_div, Complex.norm_real,
      Real.norm_of_nonneg hLp.le]
    apply (div_le_div_of_nonneg_right (hbound w hw) hLp.le).trans_lt
    rw [div_lt_iff₀ hLp]
    simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hLC
  simpa only [polarRegularizedZeta_one, dist_comm] using hcont hsmall

theorem scaled_riemannZeta_tendsto {w : ℂ} (hw : w ≠ 0) :
    Tendsto (fun L : ℝ => riemannZeta (1+w/(L:ℂ))/(L:ℂ)) atTop (𝓝 (1/w)) := by
  have hreg := (polarRegularizedZeta_scaled_uniform
    (isCompact_singleton.isBounded : Bornology.IsBounded ({w} : Set ℂ))).tendsto_at
      (mem_singleton w)
  apply Filter.Tendsto.congr' _ (hreg.div_const w)
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  exact (scaled_riemannZeta_eq_regularized hL.ne' hw).symm

theorem scaled_riemannZeta_uniform {K : Set ℂ} (hK : Bornology.IsBounded K)
    {r : ℝ} (hr : 0 < r) (hsep : ∀ w ∈ K, r ≤ ‖w‖) :
    TendstoUniformlyOn (fun L : ℝ => fun w : ℂ => riemannZeta (1+w/(L:ℂ))/(L:ℂ))
      (fun w => 1/w) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hreg := (Metric.tendstoUniformlyOn_iff.mp
    (polarRegularizedZeta_scaled_uniform hK)) (ε*r) (mul_pos hε hr)
  filter_upwards [hreg, eventually_gt_atTop (0:ℝ)] with L hreg hL w hw
  have hwn : w ≠ 0 := norm_pos_iff.mp (hr.trans_le (hsep w hw))
  rw [scaled_riemannZeta_eq_regularized hL.ne' hwn, dist_eq_norm,
    ← sub_div, norm_div]
  apply (div_lt_iff₀ (norm_pos_iff.mpr hwn)).mpr
  have hnum : ‖1-polarRegularizedZeta (1+w/(L:ℂ))‖ < ε*r := by
    simpa only [dist_eq_norm] using hreg w hw
  exact hnum.trans_le (mul_le_mul_of_nonneg_left (hsep w hw) hε.le)

def polarLeftArguments (u z : ℂ) (σ : Fin 4 → ℂ) : Fin 3 → ℂ :=
  ![u, z+σ 0, z+σ 1]

def polarRightArguments (v z : ℂ) (σ : Fin 4 → ℂ) : Fin 3 → ℂ :=
  ![v, z+σ 2, z+σ 3]

def ninePolarArgument (u v z : ℂ) (σ : Fin 4 → ℂ) (ij : Fin 3 × Fin 3) : ℂ :=
  polarLeftArguments u z σ ij.1 + polarRightArguments v z σ ij.2

def ninePolarZetaFactor (L : ℝ) (u v z : ℂ) (σ : Fin 4 → ℂ) : ℂ :=
  ∏ ij : Fin 3 × Fin 3, riemannZeta (1+ninePolarArgument u v z σ ij/(L:ℂ))/(L:ℂ)

def ninePolarRationalFactor (u v z : ℂ) (σ : Fin 4 → ℂ) : ℂ :=
  ∏ ij : Fin 3 × Fin 3, 1/ninePolarArgument u v z σ ij

theorem ninePolarZetaFactor_tendsto (u v z : ℂ) (σ : Fin 4 → ℂ)
    (hsep : ∀ ij : Fin 3 × Fin 3, ninePolarArgument u v z σ ij ≠ 0) :
    Tendsto (fun L : ℝ => ninePolarZetaFactor L u v z σ) atTop
      (𝓝 (ninePolarRationalFactor u v z σ)) := by
  apply tendsto_finsetProd
  intro ij _
  exact scaled_riemannZeta_tendsto (hsep ij)

end

end SixthMoment
