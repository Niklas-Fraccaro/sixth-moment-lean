import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Sechstmoment.Analysis.Profiles.Classes


namespace Sechstmoment
open Set MeasureTheory Metric
open scoped Topology
noncomputable section

theorem exists_smoothDyadicWeight_mass_gt {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ Φ : ℝ → ℝ, SmoothDyadicWeight Φ ∧ (∀ x, 0 ≤ Φ x) ∧
      (∀ x, Φ x ≤ 1) ∧ q < ∫ x : ℝ, Φ x := by
  let f : ContDiffBump (3/2 : ℝ) :=
    ⟨(q+1)/4, 1/2, by linarith, by linarith⟩
  refine ⟨f, ⟨f.contDiff, ?_⟩, fun _ => f.nonneg, fun _ => f.le_one, ?_⟩
  · intro x hx
    rw [f.tsupport_eq] at hx
    have hb : |x-(3/2 : ℝ)| ≤ 1/2 := by
      simpa only [mem_closedBall, Real.dist_eq, f] using hx
    obtain ⟨hl, hu⟩ := abs_le.mp hb
    constructor <;> linarith
  · have hi : Integrable (f : ℝ → ℝ) :=
      f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
    have hp : (∫ x : ℝ in Icc (3/2-f.rIn) (3/2+f.rIn), f x) = 2*f.rIn := by
      calc
        _ = ∫ _x : ℝ in Icc (3/2-f.rIn) (3/2+f.rIn), (1 : ℝ) := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro x hx
          apply f.one_of_mem_closedBall
          simp only [mem_closedBall, Real.dist_eq]
          exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
        _ = 2*f.rIn := by
          rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith [f.rIn_pos])]
          simp only [smul_eq_mul, mul_one]
          ring
    have hl := setIntegral_le_integral (s := Icc (3/2-f.rIn) (3/2+f.rIn)) hi
      (Filter.Eventually.of_forall (fun _ => f.nonneg))
    rw [hp] at hl
    have hr : f.rIn = (q+1)/4 := rfl
    linarith

end
end Sechstmoment
