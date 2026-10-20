import Sechstmoment.Analysis.Mellin.SmoothMellin


namespace Sechstmoment.Source
open Complex Real MeasureTheory Set
open scoped Topology ContDiff
noncomputable section

theorem smooth_dyadic_mellin_convergent {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1:ℝ) 2) (s : ℂ) : MellinConvergent w s := by
  let f : ℝ → ℂ := fun x => (x:ℂ)^(s-1)*w x
  have hc : ContinuousOn f (Icc (1:ℝ) 2) := by
    apply ContinuousOn.mul _ hw.continuous.continuousOn
    apply continuousOn_of_forall_continuousAt
    intro x hx
    apply ContinuousAt.cpow (by fun_prop) continuousAt_const
    apply Complex.ofReal_mem_slitPlane.mpr
    linarith [hx.1]
  have hi : Integrable ((Icc (1:ℝ) 2).indicator f) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (hc.integrableOn_Icc)
  change IntegrableOn f (Ioi 0)
  apply hi.integrableOn.congr_fun _ measurableSet_Ioi
  intro x hx
  by_cases hmem : x ∈ Icc (1:ℝ) 2
  · simp only [Set.indicator_of_mem hmem]
  · have hz : w x = 0 := by
      by_contra h
      exact hmem (hws (subset_tsupport w (Function.mem_support.mpr h)))
    simp [Set.indicator_of_notMem hmem,f,hz]

theorem smooth_dyadic_mellin_vertical_integrable {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2) (κ : ℝ) :
    VerticalIntegrable (mellin w) κ := by
  have h := smooth_mellin_weighted_integrable hw hws κ 0
  simp only [pow_zero,one_mul] at h
  exact (integrable_norm_iff
    (smooth_mellin_line_continuous hw hws κ).aestronglyMeasurable).mp h

theorem smooth_dyadic_mellin_inversion {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1:ℝ) 2) (κ : ℝ) {x : ℝ} (hx : 0 < x) :
    mellinInv κ (mellin w) x = w x :=
  mellinInv_mellin_eq κ w hx (smooth_dyadic_mellin_convergent hw hws _)
    (smooth_dyadic_mellin_vertical_integrable hw hws κ) hw.continuous.continuousAt

theorem smooth_dyadic_mellin_inversion_integral {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    (κ : ℝ) {x : ℝ} (hx : 0 < x) :
    (1/(2*Real.pi):ℂ)*
      (∫ v : ℝ, mellin w ((κ:ℂ)+(v:ℂ)*I)*(x:ℂ)^(-((κ:ℂ)+(v:ℂ)*I))) = w x := by
  simpa only [mellinInv,Complex.real_smul,Complex.ofReal_div,Complex.ofReal_one,
    Complex.ofReal_mul,Complex.ofReal_ofNat,smul_eq_mul,mul_comm] using
      smooth_dyadic_mellin_inversion hw hws κ hx

end
end Sechstmoment.Source
