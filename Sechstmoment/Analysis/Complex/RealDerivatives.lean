import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.RealDeriv
import Sechstmoment.Analysis.Complex.CauchyBounds

/-! Transfer complex Cauchy estimates to the actual real `t/T` derivatives. -/

namespace Sechstmoment
open Complex Filter Metric
open scoped Topology
noncomputable section

/-- Every complex derivative of a holomorphic function is the corresponding
ordinary real derivative of its restriction to the real axis. -/
theorem iteratedDeriv_comp_ofReal_eq (n : ℕ) {f : ℂ → ℂ} {x : ℝ}
    (hf : AnalyticAt ℂ f (x : ℂ)) :
    iteratedDeriv n (fun y : ℝ => f (y : ℂ)) x = iteratedDeriv n f (x : ℂ) := by
  induction n generalizing f x with
  | zero => simp
  | succ n ih =>
    have hd : deriv (fun y : ℝ => f (y : ℂ)) =ᶠ[𝓝 x]
        (fun y : ℝ => deriv f (y : ℂ)) := by
      filter_upwards [((continuous_ofReal.continuousAt (x := x)).tendsto.eventually
        hf.eventually_analyticAt)] with y hy
      exact hy.differentiableAt.hasDerivAt.comp_ofReal.deriv
    rw [iteratedDeriv_succ', iteratedDeriv_succ', hd.iteratedDeriv_eq n]
    exact ih hf.deriv

/-- Cauchy's disk estimate therefore bounds the genuine real-coordinate
seminorm, without a rescaling loss. -/
theorem cauchy_real_iteratedDeriv_bound (n : ℕ) {R M : ℝ} {x : ℝ} {f : ℂ → ℂ}
    (hR : 0 < R) (hf : DiffContOnCl ℂ f (ball (x : ℂ) R))
    (hM : ∀ z ∈ sphere (x : ℂ) R, ‖f z‖ ≤ M) :
    ‖iteratedDeriv n (fun y : ℝ => f (y : ℂ)) x‖ ≤
      ((Nat.factorial n : ℝ)/R^n)*M := by
  rw [iteratedDeriv_comp_ofReal_eq n
    (hf.differentiableOn.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hR)))]
  exact cauchy_iteratedDeriv_bound n hR hf hM

end
end Sechstmoment
