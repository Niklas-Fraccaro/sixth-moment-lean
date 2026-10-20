import Sechstmoment.Denominator.Unbalanced.Expansion.Expansion

namespace Sechstmoment
open Complex Real MeasureTheory Filter Set
open scoped Topology
noncomputable section

theorem d04NormalizedShifts_uniform_eventually_small {R η : ℝ}
    (_hR : 0≤R) (hη : 0<η) :
    ∀ᶠ T : ℝ in atTop, 4≤T ∧ ∀ σ : Fin 2 → ℂ,
      (∀ j, ‖σ j‖≤R) → ∀ j, ‖σ j/(Real.log T : ℂ)‖≤η := by
  filter_upwards [eventually_ge_atTop (4 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (R/η))] with T hT hL
  refine ⟨hT, ?_⟩
  intro σ hσ j
  have hlog : 0<Real.log T := Real.log_pos (by linarith)
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hlog.le]
  apply (div_le_iff₀ hlog).mpr
  have he := (div_le_iff₀ hη).mp hL
  nlinarith [hσ j]

theorem d04NegativeZetaArguments_shift_bounds {T t η : ℝ} (hT : 4≤T)
    (ht : T≤t) (_hη : 0≤η) (hη1 : η≤1) (σ : Fin 2 → ℂ)
    (hσ : ∀ j, ‖σ j/(Real.log T : ℂ)‖≤η) (j : Fin 2) :
    |(d04NegativeZetaArguments T t σ j).re-1/2|≤η ∧
      T/4 < |(d04NegativeZetaArguments T t σ j).im| := by
  have hnorm (j : Fin 2) := hσ j
  have hre (j : Fin 2) := (Complex.abs_re_le_norm (σ j/(Real.log T : ℂ))).trans (hnorm j)
  have him (j : Fin 2) := (Complex.abs_im_le_norm (σ j/(Real.log T : ℂ))).trans (hnorm j)
  have ht0 : 0≤t := by linarith
  have htri (u : ℂ) (hu : |u.im|≤η) :
      T/4 < |-t+u.im| ∧ T/4 < |-t-u.im| := by
    have h1 := abs_add_le (-t+u.im) (-u.im)
    have h2 := abs_add_le (-t-u.im) u.im
    rw [show -t+u.im+-u.im=-t by ring, abs_neg, abs_of_nonneg ht0] at h1
    simp only [abs_neg] at h1
    rw [show -t-u.im+u.im=-t by ring, abs_neg, abs_of_nonneg ht0] at h2
    constructor <;> linarith
  fin_cases j
  · constructor
    · change |(1-criticalLinePoint t-σ 0/(Real.log T : ℂ)).re-1/2|≤η
      have he : (1-criticalLinePoint t-σ 0/(Real.log T : ℂ)).re-1/2=
          -(σ 0/(Real.log T : ℂ)).re := by simp [criticalLinePoint]; ring
      rw [he, abs_neg]
      exact hre 0
    · change T/4 < |(1-criticalLinePoint t-σ 0/(Real.log T : ℂ)).im|
      simpa [criticalLinePoint] using (htri (σ 0/(Real.log T : ℂ)) (him 0)).2
  · constructor
    · change |(1-criticalLinePoint t+σ 1/(Real.log T : ℂ)).re-1/2|≤η
      have he : (1-criticalLinePoint t+σ 1/(Real.log T : ℂ)).re-1/2=
          (σ 1/(Real.log T : ℂ)).re := by simp [criticalLinePoint]; ring
      rw [he]
      exact hre 1
    · change T/4 < |(1-criticalLinePoint t+σ 1/(Real.log T : ℂ)).im|
      simpa [criticalLinePoint] using (htri (σ 1/(Real.log T : ℂ)) (him 1)).1

theorem d04NegativeZetaArguments_im_displacement_bound (T t η : ℝ)
    (σ : Fin 2 → ℂ) (hσ : ∀ j, ‖σ j/(Real.log T : ℂ)‖≤η) (j : Fin 2) :
    |(d04NegativeZetaArguments T t σ j).im+t|≤η := by
  fin_cases j
  · change |(1-criticalLinePoint t-σ 0/(Real.log T : ℂ)).im+t|≤η
    have he : (1-criticalLinePoint t-σ 0/(Real.log T : ℂ)).im+t=
        -(σ 0/(Real.log T : ℂ)).im := by simp [criticalLinePoint]; ring
    rw [he, abs_neg]
    exact (Complex.abs_im_le_norm _).trans (hσ 0)
  · change |(1-criticalLinePoint t+σ 1/(Real.log T : ℂ)).im+t|≤η
    have he : (1-criticalLinePoint t+σ 1/(Real.log T : ℂ)).im+t=
        (σ 1/(Real.log T : ℂ)).im := by simp [criticalLinePoint]
    rw [he]
    exact (Complex.abs_im_le_norm _).trans (hσ 1)

theorem d04NegativeZetaArguments_height_window {T t : ℝ} (hT : 4≤T)
    (ht : t∈Icc T (2*T)) (σ : Fin 2 → ℂ)
    (hσ : ∀ j, ‖σ j/(Real.log T : ℂ)‖≤1/4) (j : Fin 2) :
    (d04NegativeZetaArguments T t σ j).re∈Icc (1/4 : ℝ) (3/4) ∧
      3*T/4≤|(d04NegativeZetaArguments T t σ j).im| ∧
      |(d04NegativeZetaArguments T t σ j).im|≤3*T := by
  have h := d04NegativeZetaArguments_shift_bounds hT ht.1 (by norm_num)
    (by norm_num) σ hσ j
  have hIm := d04NegativeZetaArguments_im_displacement_bound T t (1/4) σ hσ j
  have ht0 : 0≤t := by linarith [ht.1]
  have htri := abs_sub ((d04NegativeZetaArguments T t σ j).im+t)
    (d04NegativeZetaArguments T t σ j).im
  rw [show (d04NegativeZetaArguments T t σ j).im+t-
    (d04NegativeZetaArguments T t σ j).im=t by ring, abs_of_nonneg ht0] at htri
  have hupper := abs_sub ((d04NegativeZetaArguments T t σ j).im+t) t
  rw [add_sub_cancel_right, abs_of_nonneg ht0] at hupper
  refine ⟨?_, ?_, ?_⟩
  · have hRe := abs_le.mp h.1
    constructor <;> linarith
  · linarith [ht.1]
  · linarith [ht.2]

end
end Sechstmoment
