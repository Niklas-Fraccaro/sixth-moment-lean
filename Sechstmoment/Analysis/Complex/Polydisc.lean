import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Tactic
import Sechstmoment.Analysis.Asymptotics.PowerLog

/-!
Transfer of contour bounds to a closed polydisc by the maximum modulus principle.
Holomorphy of the function being bounded is an explicit input, never inferred from
bounds for its individual meromorphic summands.
-/

namespace Sechstmoment

open Filter Asymptotics Metric Set
open scoped Topology BigOperators

noncomputable def rectangularClosedPolydisc {ι : Type*} (R : ι → ℝ) : Set (ι → ℂ) :=
  {z | ∀ i, ‖z i‖ ≤ R i}

noncomputable def rectangularDistinguishedBoundary {ι : Type*} (R : ι → ℝ) : Set (ι → ℂ) :=
  {z | ∀ i, ‖z i‖ = R i}

/-- Iterating the one-dimensional maximum principle transfers a bound on the
product of circles to the entire closed polydisc. -/
theorem rectangular_polydisc_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ι → ℝ) (hR : ∀ i, 0 < R i) (f : (ι → ℂ) → ℂ)
    (hf : DifferentiableOn ℂ f (rectangularClosedPolydisc R)) {M : ℝ}
    (hboundary : ∀ z ∈ rectangularDistinguishedBoundary R, ‖f z‖ ≤ M) :
    ∀ z ∈ rectangularClosedPolydisc R, ‖f z‖ ≤ M := by
  have aux : ∀ s : Finset ι, ∀ z ∈ rectangularClosedPolydisc R,
      (∀ i ∉ s, ‖z i‖ = R i) → ‖f z‖ ≤ M := by
    intro s
    induction s using Finset.induction with
    | empty =>
      intro z _ hz
      exact hboundary z (fun i => hz i (by simp))
    | @insert i s hi ih =>
      intro z hz hzboundary
      have hupd : ∀ w ∈ closedBall (0:ℂ) (R i),
          Function.update z i w ∈ rectangularClosedPolydisc R := by
        intro w hw j
        by_cases hji : j = i
        · subst j
          simpa only [Function.update_self, mem_closedBall, dist_zero_right] using hw
        · simpa [Function.update_of_ne hji] using hz j
      have hg : Differentiable ℂ (Function.update z i) :=
        fun w => (hasFDerivAt_update z w).differentiableAt
      have hdiff : DifferentiableOn ℂ (fun w => f (Function.update z i w))
          (closedBall (0:ℂ) (R i)) := hf.comp hg.differentiableOn hupd
      have hfront : ∀ w ∈ frontier (ball (0:ℂ) (R i)),
          ‖f (Function.update z i w)‖ ≤ M := by
        intro w hw
        rw [frontier_ball (0:ℂ) (hR i).ne'] at hw
        apply ih _ (hupd w (sphere_subset_closedBall hw))
        intro j hj
        by_cases hji : j = i
        · subst j
          simpa only [Function.update_self, mem_sphere, dist_zero_right] using hw
        · have hjinsert : j ∉ insert i s := by simp [hji, hj]
          simpa [Function.update_of_ne hji] using hzboundary j hjinsert
      have hzball : z i ∈ closure (ball (0:ℂ) (R i)) := by
        rw [closure_ball (0:ℂ) (hR i).ne']
        simpa only [mem_closedBall, dist_zero_right] using hz i
      have hbound := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
        (hdiff.diffContOnCl_ball Subset.rfl) hfront hzball
      simpa only [Function.update_eq_self] using hbound
  intro z hz
  exact aux Finset.univ z hz (by simp)

/-- The contour error is uniform in the shifts because the same majorant is used
on every distinguished-boundary point. -/
theorem rectangular_uniform_polydisc_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ℝ → ι → ℝ) (f : ℝ → (ι → ℂ) → ℂ) (B : ℝ → ℝ)
    (hR : ∀ᶠ T in atTop, ∀ i, 0 < R T i)
    (hf : ∀ᶠ T in atTop, DifferentiableOn ℂ (f T) (rectangularClosedPolydisc (R T)))
    (hboundary : ∀ᶠ T in atTop, ∀ z ∈ rectangularDistinguishedBoundary (R T),
      ‖f T z‖ ≤ B T) :
    ∀ᶠ T in atTop, ∀ z ∈ rectangularClosedPolydisc (R T), ‖f T z‖ ≤ B T := by
  filter_upwards [hR, hf, hboundary] with T hr hd hb
  exact rectangular_polydisc_norm_le (R T) hr (f T) hd hb

/-- A common sublinear boundary majorant gives uniform sublinearity throughout
the polydisc, including the coincident shifts. -/
theorem rectangular_uniform_polydisc_isLittleO {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ℝ → ι → ℝ) (f : ℝ → (ι → ℂ) → ℂ) (B : ℝ → ℝ)
    (hR : ∀ᶠ T in atTop, ∀ i, 0 < R T i)
    (hf : ∀ᶠ T in atTop, DifferentiableOn ℂ (f T) (rectangularClosedPolydisc (R T)))
    (hboundary : ∀ᶠ T in atTop, ∀ z ∈ rectangularDistinguishedBoundary (R T),
      ‖f T z‖ ≤ B T)
    (hB : B =o[atTop] (fun T : ℝ => T)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ T in atTop, ∀ z ∈ rectangularClosedPolydisc (R T),
      ‖f T z‖ ≤ ε * T := by
  intro ε hε
  have hd := rectangular_uniform_polydisc_bound R f B hR hf hboundary
  filter_upwards [hd, hB.def hε, eventually_ge_atTop (0:ℝ)] with T ht hb hT
  intro z hz
  exact (ht z hz).trans ((le_abs_self (B T)).trans (by simpa [Real.norm_eq_abs, abs_of_nonneg hT] using hb))

end Sechstmoment
