import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import SixthMoment.Analysis.Complex.SimplePole


namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem vertical_line_translate (c : ℝ) (p : ℂ) (t : ℝ) :
    ((c-p.re:ℝ):ℂ)+(t:ℂ)*I+p = (c:ℂ)+((t+p.im:ℝ):ℂ)*I := by
  apply Complex.ext <;> simp

theorem translated_simple_pole_pointwise (H : ℂ → ℂ) (c : ℝ) (p : ℂ) (t : ℝ) :
    H (((c-p.re:ℝ):ℂ)+(t:ℂ)*I+p)/(((c-p.re:ℝ):ℂ)+(t:ℂ)*I) =
      H ((c:ℂ)+((t+p.im:ℝ):ℂ)*I)/((c:ℂ)+((t+p.im:ℝ):ℂ)*I-p) := by
  simp only [← vertical_line_translate c p t,add_sub_cancel_right]

theorem mellinRectangle_complex_simplePole_shift (H : ℂ → ℂ)
    (hH : Differentiable ℂ H) {p : ℂ} {a b : ℝ}
    (ha : a < p.re) (hb : p.re < b)
    (hLeft : Integrable (fun y : ℝ => H ((a:ℂ)+(y:ℂ)*I)/((a:ℂ)+(y:ℂ)*I-p)))
    (hRight : Integrable (fun y : ℝ => H ((b:ℂ)+(y:ℂ)*I)/((b:ℂ)+(y:ℂ)*I-p)))
    (hEdge : Tendsto (fun y : ℝ => ∫ c in a..b,
      H ((c:ℂ)+(y:ℂ)*I)/((c:ℂ)+(y:ℂ)*I-p)) (cocompact ℝ) (𝓝 0)) :
    (∫ y : ℝ, H ((b:ℂ)+(y:ℂ)*I)/((b:ℂ)+(y:ℂ)*I-p)) =
      (∫ y : ℝ, H ((a:ℂ)+(y:ℂ)*I)/((a:ℂ)+(y:ℂ)*I-p))+(2*Real.pi:ℂ)*H p := by
  let G : ℂ → ℂ := fun z => H (z+p)
  have hG : Differentiable ℂ G := hH.comp (by fun_prop)
  have hIL : Integrable (fun y : ℝ =>
      G (((a-p.re:ℝ):ℂ)+(y:ℂ)*I)/(((a-p.re:ℝ):ℂ)+(y:ℂ)*I)) := by
    apply ((measurePreserving_add_right volume p.im).integrable_comp_of_integrable hLeft).congr
    exact Eventually.of_forall (fun y => (translated_simple_pole_pointwise H a p y).symm)
  have hIR : Integrable (fun y : ℝ =>
      G (((b-p.re:ℝ):ℂ)+(y:ℂ)*I)/(((b-p.re:ℝ):ℂ)+(y:ℂ)*I)) := by
    apply ((measurePreserving_add_right volume p.im).integrable_comp_of_integrable hRight).congr
    exact Eventually.of_forall (fun y => (translated_simple_pole_pointwise H b p y).symm)
  have heq (c : ℝ) :
      (∫ y : ℝ, G (((c-p.re:ℝ):ℂ)+(y:ℂ)*I)/(((c-p.re:ℝ):ℂ)+(y:ℂ)*I)) =
        ∫ y : ℝ, H ((c:ℂ)+(y:ℂ)*I)/((c:ℂ)+(y:ℂ)*I-p) := by
    calc
      _ = ∫ y : ℝ, H ((c:ℂ)+((y+p.im:ℝ):ℂ)*I)/((c:ℂ)+((y+p.im:ℝ):ℂ)*I-p) :=
        integral_congr_ae (Eventually.of_forall (translated_simple_pole_pointwise H c p))
      _ = _ := by
        simpa only using! integral_add_right_eq_self (μ := volume)
          (fun y : ℝ => H ((c:ℂ)+(y:ℂ)*I)/((c:ℂ)+(y:ℂ)*I-p)) p.im
  have hedgeeq (y : ℝ) :
      (∫ c in (a-p.re)..(b-p.re), G ((c:ℂ)+(y:ℂ)*I)/((c:ℂ)+(y:ℂ)*I)) =
        ∫ c in a..b, H ((c:ℂ)+((y+p.im:ℝ):ℂ)*I)/((c:ℂ)+((y+p.im:ℝ):ℂ)*I-p) := by
    calc
      _ = ∫ c in (a-p.re)..(b-p.re),
          H (((c+p.re:ℝ):ℂ)+((y+p.im:ℝ):ℂ)*I)/
            (((c+p.re:ℝ):ℂ)+((y+p.im:ℝ):ℂ)*I-p) := by
        apply intervalIntegral.integral_congr
        intro c _
        simpa only [add_sub_cancel_right] using translated_simple_pole_pointwise H (c+p.re) p y
      _ = _ := by
        simpa only [sub_add_cancel] using! intervalIntegral.integral_comp_add_right
          (a := a-p.re) (b := b-p.re)
          (fun c : ℝ => H ((c:ℂ)+((y+p.im:ℝ):ℂ)*I)/
            ((c:ℂ)+((y+p.im:ℝ):ℂ)*I-p)) p.re
  have htrans : Tendsto (fun y : ℝ => y+p.im) (cocompact ℝ) (cocompact ℝ) :=
    (Homeomorph.addRight p.im).isClosedEmbedding.tendsto_cocompact
  have hGE : Tendsto (fun y : ℝ => ∫ c in (a-p.re)..(b-p.re),
      G ((c:ℂ)+(y:ℂ)*I)/((c:ℂ)+(y:ℂ)*I)) (cocompact ℝ) (𝓝 0) :=
    (hEdge.comp htrans).congr' (Eventually.of_forall (fun y => (hedgeeq y).symm))
  have Hshift := mellinRectangle_simplePole_shift G isOpen_univ hG.differentiableOn
    (by linarith : a-p.re < 0) (by linarith : 0 < b-p.re)
    (fun _ _ _ => mem_univ _) hIL hIR hGE
  rw [heq b,heq a] at Hshift
  simpa only [G,zero_add] using Hshift

end
end SixthMoment.Source
