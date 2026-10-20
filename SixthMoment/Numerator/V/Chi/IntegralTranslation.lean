import SixthMoment.Numerator.V.Chi.ShiftedKernel
import SixthMoment.Numerator.V.Chi.TranslatedWeight


namespace SixthMoment.Source
open Complex Real Set MeasureTheory
open scoped ContDiff
noncomputable section

def noDPChiBaseIntegrand (r c t : ℝ) : ℂ :=
  (r:ℂ)^(-((c:ℂ)+(t:ℂ)*I))*zetaChi (1-((c:ℂ)+(t:ℂ)*I))

theorem noDPChiBaseIntegrand_aestronglyMeasurable {r c : ℝ}
    (hr : 0 < r) (hc : 0 < c) :
    AEStronglyMeasurable (noDPChiBaseIntegrand r c) volume := by
  have hp : Continuous (fun t : ℝ => (r:ℂ)^(-((c:ℂ)+(t:ℂ)*I))) := by
    have he : (fun t : ℝ => (r:ℂ)^(-((c:ℂ)+(t:ℂ)*I))) =
        fun t : ℝ => Complex.exp (Complex.log (r:ℂ)*(-((c:ℂ)+(t:ℂ)*I))) := by
      funext t
      exact Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') _
    rw [he]
    fun_prop
  exact hp.aestronglyMeasurable.mul (chi_vertical_aestronglyMeasurable hc)

theorem noDPChiBaseIntegrand_norm {r : ℝ} (hr : 0 < r) (c t : ℝ) :
    ‖noDPChiBaseIntegrand r c t‖ =
      r^(-c)*‖zetaChi (1-((c:ℂ)+(t:ℂ)*I))‖ := by
  rw [noDPChiBaseIntegrand,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp

theorem noDPChiTimeTransform_translation_error {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 64 ≤ T → ∀ c : ℝ, ∀ u : ℂ,
      c-u.re ∈ Icc (1/2:ℝ) 2 → c-u.re ≤ 1+A/Real.log T → |u.im| ≤ T/2 →
      ∀ r : ℝ, 0 < r →
      ‖noDPChiTimeTransform w T c u r-
        (r:ℂ)^(-u)*noDPChiTimeTransform w T (c-u.re) 0 r‖ ≤
        C*r^(-c)*T^(1/2:ℝ)*|u.im| := by
  obtain ⟨D,hD,htranslate⟩ := smooth_compact_weight_integrated_translation hw hws
  let C := D*131*Real.exp A
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro T hT c u hc hcline hu r hr
  have hT1 : 1 ≤ T := by linarith
  have hc0 : 0 < c-u.re := by linarith [hc.1]
  let M := r^(-(c-u.re))*(131*Real.exp A*T^(1/2:ℝ))
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hbound (v : ℝ) (hv : v ∈ Icc (T/2) (3*T)) :
      ‖noDPChiBaseIntegrand r (c-u.re) v‖ ≤ M := by
    rw [noDPChiBaseIntegrand_norm hr]
    exact mul_le_mul_of_nonneg_left (chi_transform_wide_log_line_bound hT hc hcline hv)
      (Real.rpow_nonneg hr.le _)
  have H := htranslate T hT1 u.im hu (noDPChiBaseIntegrand r (c-u.re))
    (noDPChiBaseIntegrand_aestronglyMeasurable hr hc0) M hM hbound
  have he : noDPChiTimeTransform w T c u r-
      (r:ℂ)^(-u)*noDPChiTimeTransform w T (c-u.re) 0 r =
      (r:ℂ)^(-u)*(1/(2*Real.pi):ℂ)*
        ((∫ v : ℝ, noDPChiBaseIntegrand r (c-u.re) v*w ((v+u.im)/T))-
          (∫ v : ℝ, noDPChiBaseIntegrand r (c-u.re) v*w (v/T))) := by
    rw [noDPChiTimeTransform_shift w T c u hr]
    unfold noDPChiTimeTransform noDPChiBaseIntegrand
    simp only [add_zero]
    ring
  have hprefix : ‖(r:ℂ)^(-u)‖ = r^(-u.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr,neg_re]
  have hscale : ‖(1/(2*Real.pi):ℂ)‖ ≤ 1 := by
    have hp : 0 < 2*Real.pi := by positivity
    have he : ‖(1/(2*Real.pi):ℂ)‖ = 1/(2*Real.pi) := by simp
    rw [he]
    exact (div_le_one hp).mpr (by linarith [Real.two_le_pi])
  rw [he,norm_mul,norm_mul,hprefix]
  calc
    _ ≤ (r^(-u.re)*1)*(D*M*|u.im|) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hscale (Real.rpow_nonneg hr.le _)) H
        (norm_nonneg _) (by positivity)
    _ = C*r^(-c)*T^(1/2:ℝ)*|u.im| := by
      dsimp only [C,M]
      rw [show -c = -u.re+(-(c-u.re)) by ring,Real.rpow_add hr]
      ring

end
end SixthMoment.Source
