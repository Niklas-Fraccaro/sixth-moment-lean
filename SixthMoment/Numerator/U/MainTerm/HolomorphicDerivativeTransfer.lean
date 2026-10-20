import Mathlib.Analysis.Complex.Liouville
import SixthMoment.Numerator.V.DP.DPPolydiscBoundary


namespace SixthMoment
open Complex Metric Set Filter Source
open scoped Topology
noncomputable section

set_option maxHeartbeats 2000000

theorem rectangular_uniform_boundary_zero_to_polydisc_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ι → ℝ) (hR : ∀ i, 0 < R i) (E : ℝ → (ι → ℂ) → ℂ)
    (hhol : ∀ᶠ T : ℝ in atTop,
      DifferentiableOn ℂ (E T) (rectangularClosedPolydisc R))
    (hboundary : TendstoUniformlyOn E (fun _ => (0:ℂ)) atTop
      (rectangularDistinguishedBoundary R)) :
    TendstoUniformlyOn E (fun _ => (0:ℂ)) atTop
      (rectangularClosedPolydisc R) := by
  rw [Metric.tendstoUniformlyOn_iff] at hboundary ⊢
  intro ε hε
  filter_upwards [hhol, hboundary (ε/2) (by positivity)] with T hT hB
  have hbound : ∀ σ ∈ rectangularDistinguishedBoundary R, ‖E T σ‖ ≤ ε/2 := by
    intro σ hσ
    have hh := hB σ hσ
    simpa only [dist_eq_norm, zero_sub, norm_neg] using hh.le
  intro σ hσ
  rw [dist_eq_norm, zero_sub, norm_neg]
  exact (rectangular_polydisc_norm_le R hR (E T) hT hbound σ hσ).trans_lt
    (by linarith)

def rectangularCoordinateLine {ι : Type*} [DecidableEq ι] (i : ι) (z : ℂ) : ι → ℂ :=
  Function.update 0 i z

theorem rectangularCoordinateLine_differentiable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) : Differentiable ℂ (rectangularCoordinateLine i) :=
  fun z => (hasFDerivAt_update (i := i) (0:ι → ℂ) z).differentiableAt

private theorem rectangularCoordinateLine_mem_polydisc {ι : Type*} [DecidableEq ι]
    (R : ι → ℝ) (hR : ∀ j, 0 < R j) (i : ι) {z : ℂ} (hz : ‖z‖ ≤ R i) :
    rectangularCoordinateLine i z ∈ rectangularClosedPolydisc R := by
  intro j
  by_cases hji : j=i
  · subst j
    simpa [rectangularCoordinateLine] using hz
  · simpa [rectangularCoordinateLine, Function.update_of_ne hji] using (hR j).le

private theorem disk_around_disk_norm_le {r : ℝ} {z w : ℂ}
    (hz : z ∈ closedBall (0:ℂ) r) (hw : w ∈ closedBall z r) : ‖w‖ ≤ 2*r := by
  have hz' : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hw' : ‖w-z‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hw
  have hn : ‖w‖ ≤ ‖w-z‖+‖z‖ := by
    convert norm_add_le (w-z) z using 1
    simp
  linarith

theorem rectangular_coordinate_iteratedDeriv_uniform_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ι → ℝ) (hR : ∀ i, 0 < R i) (i : ι)
    (r : ℝ) (hr : 0 < r) (hri : 2*r ≤ R i) (E : ℝ → (ι → ℂ) → ℂ)
    (hhol : ∀ᶠ T : ℝ in atTop,
      DifferentiableOn ℂ (E T) (rectangularClosedPolydisc R))
    (hboundary : TendstoUniformlyOn E (fun _ => (0:ℂ)) atTop
      (rectangularDistinguishedBoundary R)) (n : ℕ) :
    TendstoUniformlyOn
      (fun T => iteratedDeriv n (fun z : ℂ => E T (rectangularCoordinateLine i z)))
      (fun _ => (0:ℂ)) atTop (closedBall (0:ℂ) r) := by
  have hinterior := rectangular_uniform_boundary_zero_to_polydisc_zero
    R hR E hhol hboundary
  rw [Metric.tendstoUniformlyOn_iff] at hinterior ⊢
  intro ε hε
  have hfact : 0 < (n.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos n
  filter_upwards [hhol, hinterior (ε*r^n/(2*(n.factorial:ℝ))) (by positivity)]
    with T hT hB z hz
  have hmap : MapsTo (rectangularCoordinateLine i) (closedBall z r)
      (rectangularClosedPolydisc R) := by
    intro w hw
    exact rectangularCoordinateLine_mem_polydisc R hR i
      ((disk_around_disk_norm_le hz hw).trans hri)
  have hd : DifferentiableOn ℂ (fun w : ℂ => E T (rectangularCoordinateLine i w))
      (closedBall z r) :=
    hT.comp (rectangularCoordinateLine_differentiable i).differentiableOn hmap
  have hc : DiffContOnCl ℂ (fun w : ℂ => E T (rectangularCoordinateLine i w)) (ball z r) :=
    (hd.mono closure_ball_subset_closedBall).diffContOnCl
  have hs : ∀ w ∈ sphere z r,
      ‖E T (rectangularCoordinateLine i w)‖ ≤ ε*r^n/(2*(n.factorial:ℝ)) := by
    intro w hw
    have hh := hB (rectangularCoordinateLine i w) (hmap (sphere_subset_closedBall hw))
    simpa only [dist_eq_norm, zero_sub, norm_neg] using hh.le
  rw [dist_eq_norm, zero_sub, norm_neg]
  calc
    _ ≤ (n.factorial:ℝ)*(ε*r^n/(2*(n.factorial:ℝ)))/r^n :=
      Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hc hs
    _ = ε/2 := by field_simp
    _ < ε := by linarith

private theorem rectangular_coordinate_slice_analyticAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ι → ℝ) (hR : ∀ j, 0 < R j) (i : ι)
    (r : ℝ) (hr : 0 < r) (hri : 2*r ≤ R i)
    (F : (ι → ℂ) → ℂ) (hF : DifferentiableOn ℂ F (rectangularClosedPolydisc R))
    {z : ℂ} (hz : z ∈ closedBall (0:ℂ) r) :
    AnalyticAt ℂ (fun w : ℂ => F (rectangularCoordinateLine i w)) z := by
  have hmap : MapsTo (rectangularCoordinateLine i) (closedBall z r)
      (rectangularClosedPolydisc R) := by
    intro w hw
    exact rectangularCoordinateLine_mem_polydisc R hR i
      ((disk_around_disk_norm_le hz hw).trans hri)
  have hd : DifferentiableOn ℂ (fun w : ℂ => F (rectangularCoordinateLine i w))
      (closedBall z r) :=
    hF.comp (rectangularCoordinateLine_differentiable i).differentiableOn hmap
  exact hd.analyticAt (closedBall_mem_nhds z hr)

theorem rectangular_coordinate_iteratedDeriv_uniform_limit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ι → ℝ) (hR : ∀ i, 0 < R i) (i : ι)
    (r : ℝ) (hr : 0 < r) (hri : 2*r ≤ R i)
    (F : ℝ → (ι → ℂ) → ℂ) (G : (ι → ℂ) → ℂ)
    (hF : ∀ᶠ T : ℝ in atTop, DifferentiableOn ℂ (F T) (rectangularClosedPolydisc R))
    (hG : DifferentiableOn ℂ G (rectangularClosedPolydisc R))
    (hboundary : TendstoUniformlyOn F G atTop (rectangularDistinguishedBoundary R))
    (n : ℕ) :
    TendstoUniformlyOn
      (fun T => iteratedDeriv n (fun z : ℂ => F T (rectangularCoordinateLine i z)))
      (iteratedDeriv n (fun z : ℂ => G (rectangularCoordinateLine i z)))
      atTop (closedBall (0:ℂ) r) := by
  have hhol : ∀ᶠ T : ℝ in atTop,
      DifferentiableOn ℂ (fun σ => F T σ-G σ) (rectangularClosedPolydisc R) := by
    filter_upwards [hF] with T hT
    exact hT.sub hG
  have hb : TendstoUniformlyOn (fun T σ => F T σ-G σ) (fun _ => (0:ℂ)) atTop
      (rectangularDistinguishedBoundary R) := by
    rw [Metric.tendstoUniformlyOn_iff] at hboundary ⊢
    intro ε hε
    filter_upwards [hboundary ε hε] with T hT σ hσ
    rw [dist_eq_norm, zero_sub, norm_neg, norm_sub_rev]
    simpa only [dist_eq_norm] using hT σ hσ
  have herror := rectangular_coordinate_iteratedDeriv_uniform_zero
    R hR i r hr hri (fun T σ => F T σ-G σ) hhol hb n
  rw [Metric.tendstoUniformlyOn_iff] at herror ⊢
  intro ε hε
  filter_upwards [hF, herror ε hε] with T hT hE z hz
  have hsF := rectangular_coordinate_slice_analyticAt R hR i r hr hri (F T) hT hz
  have hsG := rectangular_coordinate_slice_analyticAt R hR i r hr hri G hG hz
  have hsub := iteratedDeriv_fun_sub (n := n) hsF.contDiffAt hsG.contDiffAt
  have hh := hE z hz
  rw [dist_eq_norm, zero_sub, norm_neg, hsub, norm_sub_rev] at hh
  simpa only [dist_eq_norm] using hh

def dpUShiftLine (z : ℂ) : MomentShifts := rectangularCoordinateLine (2:Fin 4) z

theorem dpUShiftLine_eq_vector (z : ℂ) : dpUShiftLine z = ![0,0,z,0] := by
  ext j
  fin_cases j <;> simp [dpUShiftLine, rectangularCoordinateLine]

theorem dpUShiftLine_iteratedDeriv_uniform_zero
    (E : ℝ → MomentShifts → ℂ)
    (hhol : ∀ᶠ T : ℝ in atTop,
      DifferentiableOn ℂ (E T) (rectangularClosedPolydisc dpCauchyRadii))
    (hboundary : TendstoUniformlyOn E (fun _ => (0:ℂ)) atTop
      (rectangularDistinguishedBoundary dpCauchyRadii)) (n : ℕ) :
    TendstoUniformlyOn
      (fun T => iteratedDeriv n (fun z : ℂ => E T (dpUShiftLine z)))
      (fun _ => (0:ℂ)) atTop (closedBall (0:ℂ) 1) :=
  rectangular_coordinate_iteratedDeriv_uniform_zero dpCauchyRadii dpCauchyRadii_positive
    (2:Fin 4) 1 (by norm_num) (by norm_num [dpCauchyRadii]) E hhol hboundary n

theorem dpUShiftLine_iteratedDeriv_zero_through_four
    (E : ℝ → MomentShifts → ℂ)
    (hhol : ∀ᶠ T : ℝ in atTop,
      DifferentiableOn ℂ (E T) (rectangularClosedPolydisc dpCauchyRadii))
    (hboundary : TendstoUniformlyOn E (fun _ => (0:ℂ)) atTop
      (rectangularDistinguishedBoundary dpCauchyRadii)) :
    ∀ n ≤ 4, Tendsto
      (fun T => iteratedDeriv n (fun z : ℂ => E T (dpUShiftLine z)) 0)
      atTop (𝓝 (0:ℂ)) := by
  intro n _
  exact (dpUShiftLine_iteratedDeriv_uniform_zero E hhol hboundary n).tendsto_at
    (by simp)

end
end SixthMoment
