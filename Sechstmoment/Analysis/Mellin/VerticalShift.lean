import Sechstmoment.Analysis.Complex.SimplePole
import Sechstmoment.Analysis.Gaussian.Decay


namespace Sechstmoment.Source
open Complex Real MeasureTheory Filter Set
open scoped Topology
noncomputable section

theorem vertical_integrable_of_gaussian_bound (F : ℂ → ℂ) (c C : ℝ)
    (hcont : Continuous (fun v : ℝ => F ((c : ℂ)+(v : ℂ)*I)))
    (hbound : ∀ v : ℝ, ‖F ((c : ℂ)+(v : ℂ)*I)‖ ≤ C*Real.exp (-v^2)) :
    Integrable (fun v : ℝ => F ((c : ℂ)+(v : ℂ)*I)) := by
  have hgauss : Integrable (fun v : ℝ => Real.exp (-v^2)) := by
    simpa using gaussianPolynomialExponential_integrable 0 0
  exact (hgauss.const_mul C).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall hbound)

theorem horizontal_tendsto_zero_of_gaussian_strip_bound (F : ℂ → ℂ)
    {a b C : ℝ} (hab : a ≤ b)
    (hbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖F z‖ ≤ C*Real.exp (-z.im^2)) :
    Tendsto (fun v : ℝ => ∫ c in a..b, F ((c : ℂ)+(v : ℂ)*I))
      (cocompact ℝ) (𝓝 0) := by
  have hlim : Tendsto (fun v : ℝ => (b-a)*C*Real.exp (-v^2)) (cocompact ℝ) (𝓝 0) := by
    simpa using (gaussianPolynomialExponential_tendsto_zero 0 0).const_mul ((b-a)*C)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  apply Eventually.of_forall
  intro v
  have hpoint (c : ℝ) (hc : c ∈ uIoc a b) :
      ‖F ((c : ℂ)+(v : ℂ)*I)‖ ≤ C*Real.exp (-v^2) := by
    rw [uIoc_of_le hab] at hc
    simpa using hbound ((c : ℂ)+(v : ℂ)*I) (by simpa using hc.1.le) (by simpa using hc.2)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at h
  convert h using 1
  ring

theorem vertical_integrals_eq_of_holomorphic (F : ℂ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ F z)
    (hLeft : Integrable (fun v : ℝ => F ((a : ℂ)+(v : ℂ)*I)))
    (hRight : Integrable (fun v : ℝ => F ((b : ℂ)+(v : ℂ)*I)))
    (hEdge : Tendsto (fun v : ℝ => ∫ c in a..b, F ((c : ℂ)+(v : ℂ)*I))
      (cocompact ℝ) (𝓝 0)) :
    (∫ v : ℝ, F ((b : ℂ)+(v : ℂ)*I)) = ∫ v : ℝ, F ((a : ℂ)+(v : ℂ)*I) := by
  have hrect (R : ℝ) :
      (∫ c in a..b, F ((c : ℂ)+((-R : ℝ) : ℂ)*I))-
      (∫ c in a..b, F ((c : ℂ)+(R : ℂ)*I))+
      I*(∫ v in (-R)..R, F ((b : ℂ)+(v : ℂ)*I))-
      I*(∫ v in (-R)..R, F ((a : ℂ)+(v : ℂ)*I)) = 0 := by
    have hd : DifferentiableOn ℂ F (uIcc a b ×ℂ uIcc (-R) R) := by
      intro z hz
      have hzre : z.re ∈ uIcc a b := hz.1
      rw [uIcc_of_le hab] at hzre
      exact (hF z hzre.1 hzre.2).differentiableWithinAt
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
      ((a : ℂ)+((-R : ℝ) : ℂ)*I) ((b : ℂ)+(R : ℂ)*I) (by simpa using hd)
    simpa [smul_eq_mul] using h
  have hneg : Tendsto (fun R : ℝ => -R) atTop atBot := tendsto_neg_atTop_atBot
  have hL := MeasureTheory.intervalIntegral_tendsto_integral hLeft hneg tendsto_id
  have hR := MeasureTheory.intervalIntegral_tendsto_integral hRight hneg tendsto_id
  have hTop := hEdge.mono_left atTop_le_cocompact
  have hBot := (hEdge.mono_left atBot_le_cocompact).comp hneg
  have hlim := ((hBot.sub hTop).add (hR.const_mul I)).sub (hL.const_mul I)
  have hzero : Tendsto (fun R : ℝ =>
      (∫ c in a..b, F ((c : ℂ)+((-R : ℝ) : ℂ)*I))-
      (∫ c in a..b, F ((c : ℂ)+(R : ℂ)*I))+
      I*(∫ v in (-R)..R, F ((b : ℂ)+(v : ℂ)*I))-
      I*(∫ v in (-R)..R, F ((a : ℂ)+(v : ℂ)*I))) atTop (𝓝 0) := by
    exact tendsto_const_nhds.congr' (Eventually.of_forall fun R => (hrect R).symm)
  simp only [Function.comp_apply, sub_self, zero_add] at hlim
  have he := tendsto_nhds_unique hlim hzero
  exact mul_left_cancel₀ I_ne_zero (sub_eq_zero.mp he)

end
end Sechstmoment.Source
