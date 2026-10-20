import SixthMoment.Analysis.Complex.SimplePole


namespace SixthMoment
open Complex MeasureTheory Filter Set
open scoped Topology
noncomputable section

theorem bblrRectangle_integral_shift
    (F : ℂ → ℂ) {U : Set ℂ} (hF : DifferentiableOn ℂ F U)
    {a b : ℝ} (hab : a ≤ b)
    (hstrip : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → z ∈ U)
    (hLeft : Integrable (fun y : ℝ => F ((a:ℂ)+(y:ℂ)*I)))
    (hRight : Integrable (fun y : ℝ => F ((b:ℂ)+(y:ℂ)*I)))
    (hedge : Tendsto (fun y : ℝ => ∫ c in a..b, F ((c:ℂ)+(y:ℂ)*I))
      (cocompact ℝ) (𝓝 0)) :
    (∫ y : ℝ, F ((b:ℂ)+(y:ℂ)*I)) =
      (∫ y : ℝ, F ((a:ℂ)+(y:ℂ)*I)) := by
  have hrect (R : ℝ) :
      (∫ c in a..b, F ((c:ℂ)+((-R:ℝ):ℂ)*I))-
      (∫ c in a..b, F ((c:ℂ)+(R:ℂ)*I))+
      I*(∫ y in (-R)..R, F ((b:ℂ)+(y:ℂ)*I))-
      I*(∫ y in (-R)..R, F ((a:ℂ)+(y:ℂ)*I)) = 0 := by
    have hd : DifferentiableOn ℂ F (uIcc a b ×ℂ uIcc (-R) R) := by
      apply hF.mono
      intro z hz
      have hre : z.re ∈ uIcc a b := hz.1
      rw [uIcc_of_le hab] at hre
      exact hstrip z hre.1 hre.2
    have hh := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
      ((a:ℂ)+((-R:ℝ):ℂ)*I) ((b:ℂ)+(R:ℂ)*I) (by simpa using hd)
    simpa [smul_eq_mul] using hh
  have hneg : Tendsto (fun R : ℝ => -R) atTop atBot := tendsto_neg_atTop_atBot
  have hl := MeasureTheory.intervalIntegral_tendsto_integral hLeft hneg tendsto_id
  have hr := MeasureTheory.intervalIntegral_tendsto_integral hRight hneg tendsto_id
  have htop := hedge.mono_left atTop_le_cocompact
  have hbot := (hedge.mono_left atBot_le_cocompact).comp hneg
  have hlim := ((hbot.sub htop).add (hr.const_mul I)).sub (hl.const_mul I)
  have hzero : Tendsto (fun R : ℝ =>
      (∫ c in a..b, F ((c:ℂ)+((-R:ℝ):ℂ)*I))-
      (∫ c in a..b, F ((c:ℂ)+(R:ℂ)*I))+
      I*(∫ y in (-R)..R, F ((b:ℂ)+(y:ℂ)*I))-
      I*(∫ y in (-R)..R, F ((a:ℂ)+(y:ℂ)*I))) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall (fun R => (hrect R).symm)
  simp only [Function.comp_apply,Complex.ofReal_neg,id_eq] at hlim hzero
  have he := tendsto_nhds_unique hlim hzero
  simp only [sub_self,zero_add] at he
  apply mul_left_cancel₀ I_ne_zero
  exact sub_eq_zero.mp he

theorem bblrRectangle_verticalIntegral_shift
    (F : ℂ → ℂ) {U : Set ℂ} (hF : DifferentiableOn ℂ F U)
    {a b : ℝ} (hab : a ≤ b)
    (hstrip : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → z ∈ U)
    (hLeft : Integrable (fun y : ℝ => F ((a:ℂ)+(y:ℂ)*I)))
    (hRight : Integrable (fun y : ℝ => F ((b:ℂ)+(y:ℂ)*I)))
    (hedge : Tendsto (fun y : ℝ => ∫ c in a..b, F ((c:ℂ)+(y:ℂ)*I))
      (cocompact ℝ) (𝓝 0)) :
    Source.verticalIntegral b F = Source.verticalIntegral a F := by
  unfold Source.verticalIntegral
  rw [bblrRectangle_integral_shift F hF hab hstrip hLeft hRight hedge]

end
end SixthMoment
