import SixthMoment.Zeta.Centering.Uniform


namespace SixthMoment
open Complex Filter Metric Asymptotics
open scoped Topology
noncomputable section

theorem centeringError_uniform_shift_derivative_bound (n : ℕ) (R : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ x : ℝ, x ∈ Set.Icc (1 : ℝ) 2 →
      ∀ z : ℂ, ‖z‖ ≤ R →
        ‖iteratedDeriv n (centeringError T (T*x)) z‖ ≤
          (Nat.factorial n : ℝ)*(centeringUniformConstant (R+1)/Real.log T) := by
  filter_upwards [centeringFactor_uniform_disk_bound (R+1),
    eventually_centering_disk (R+1)] with T hbound hdomain
  intro x hx z hz
  have ha := centeringError_analyticOnNhd_disk hdomain.1 (T*x) (R+1) hdomain.2
  have hf : DiffContOnCl ℂ (centeringError T (T*x)) (ball 0 (R+1)) :=
    (ha.differentiableOn.mono closure_ball_subset_closedBall).diffContOnCl
  have hM (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) (R+1)) :
      ‖centeringError T (T*x) w‖ ≤ centeringUniformConstant (R+1)/Real.log T := by
    exact hbound x hx w (by simpa using hw)
  have hb := cauchy_iteratedDeriv_innerDisk_bound n (by linarith : R < R+1) hf hM
    z (by simpa using hz)
  simpa only [add_sub_cancel_left, one_pow, div_one] using hb

theorem centeringError_shift_derivative_invLog_isBigO (n : ℕ) (R : ℝ)
    (x : ℝ → ℝ) (z : ℝ → ℂ)
    (hx : ∀ᶠ T in atTop, x T ∈ Set.Icc (1 : ℝ) 2)
    (hz : ∀ᶠ T in atTop, ‖z T‖ ≤ R) :
    (fun T => iteratedDeriv n (centeringError T (T*x T)) (z T))
      =O[atTop] (fun T => (Real.log T)⁻¹) := by
  apply IsBigO.of_bound ((Nat.factorial n : ℝ)*centeringUniformConstant (R+1))
  filter_upwards [centeringError_uniform_shift_derivative_bound n R, hx, hz,
    eventually_gt_atTop (1 : ℝ)] with T hbound hTx hTz hT
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (Real.log_pos hT).le)]
  simpa only [div_eq_mul_inv, mul_assoc] using hbound (x T) hTx (z T) hTz

theorem centeringError_uniform_differentialOperator_bound (N : ℕ)
    (q : Fin (N+1) → ℂ) (R : ℝ) (hR : 0 < R) :
    ∀ᶠ T : ℝ in atTop, ∀ x : ℝ, x ∈ Set.Icc (1 : ℝ) 2 →
      ‖finiteDifferentialOperator N q (centeringError T (T*x)) 0‖ ≤
        (∑ j : Fin (N+1), ‖q j‖*((Nat.factorial j.val : ℝ)/R^j.val))*
          (centeringUniformConstant R/Real.log T) := by
  filter_upwards [centeringFactor_uniform_disk_bound R,
    eventually_centering_disk R] with T hbound hdomain
  intro x hx
  have ha := centeringError_analyticOnNhd_disk hdomain.1 (T*x) R hdomain.2
  have hf : DiffContOnCl ℂ (centeringError T (T*x)) (ball 0 R) :=
    (ha.differentiableOn.mono closure_ball_subset_closedBall).diffContOnCl
  apply cauchy_finiteDifferentialOperator_bound N q hR hf
  intro w hw
  exact hbound x hx w (by simpa using (mem_sphere_iff_norm.mp hw).le)

end
end SixthMoment
