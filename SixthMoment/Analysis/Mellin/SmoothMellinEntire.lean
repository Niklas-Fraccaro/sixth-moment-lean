import Mathlib.MeasureTheory.Function.LocallyIntegrable
import SixthMoment.Analysis.Mellin.SmoothMellinInversion


namespace SixthMoment.Source
open Complex Real Set Filter Asymptotics MeasureTheory
open scoped Topology
noncomputable section

theorem compact_dyadic_mellin_entire {w : ℝ → ℂ} (hw : Continuous w)
    (hws : tsupport w ⊆ Icc (1:ℝ) 2) : Differentiable ℂ (mellin w) := by
  intro s
  have htop (a : ℝ) : w =O[atTop] (fun x : ℝ => x^(-a)) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨1,?_⟩
    filter_upwards [eventually_gt_atTop (2:ℝ)] with x hx
    have hz : w x = 0 := by
      apply Function.notMem_support.mp
      intro hm
      have H := hws (subset_tsupport w hm)
      linarith [H.2]
    rw [hz,norm_zero,one_mul]
    exact norm_nonneg _
  have hbot (b : ℝ) : w =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x^(-b)) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨1,?_⟩
    filter_upwards [show Iio (1:ℝ) ∈ 𝓝[>] (0:ℝ) from
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num))] with x hx
    have hz : w x = 0 := by
      apply Function.notMem_support.mp
      intro hm
      have H := hws (subset_tsupport w hm)
      have hx1 : x < 1 := hx
      linarith [H.1]
    rw [hz,norm_zero,one_mul]
    exact norm_nonneg _
  exact mellin_differentiableAt_of_isBigO_rpow
    (hw.locallyIntegrable.locallyIntegrableOn (Ioi 0)) (htop (s.re+1)) (by linarith)
    (hbot (s.re-1)) (by linarith)

end
end SixthMoment.Source
