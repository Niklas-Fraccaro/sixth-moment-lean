import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Sechstmoment.Analysis.Mellin.ProfileInversion


namespace Sechstmoment
open Complex Real MeasureTheory Set
noncomputable section
set_option maxHeartbeats 1000000

def a04VerticalPoint (c y : ℝ) : ℂ := (c:ℂ)+(y:ℂ)*I

theorem a04VerticalPoint_re (c y : ℝ) : (a04VerticalPoint c y).re = c := by
  simp [a04VerticalPoint]

theorem a04VerticalCoupling_integrable {c : ℝ} (hc : 0 < c)
    (F G : ℝ → ℂ) (hFc : Continuous F) (hGc : Continuous G)
    (hF : Integrable F) (hG : Integrable G) :
    Integrable (fun p : (ℝ × ℝ) × ℝ =>
      F p.1.1*G p.1.2 *
        Complex.exp (-(a04VerticalPoint c p.1.1+a04VerticalPoint c p.1.2)*p.2))
      ((volume.prod volume).prod (volume.restrict (Ioi 0))) := by
  have he : Integrable (fun t : ℝ => Real.exp ((-2*c)*t))
      (volume.restrict (Ioi 0)) :=
    integrableOn_exp_mul_Ioi (by linarith : -2*c < 0) 0
  have hm := (hF.norm.mul_prod hG.norm).mul_prod he
  apply hm.mono' (by apply Continuous.aestronglyMeasurable; unfold a04VerticalPoint; fun_prop)
  apply Filter.Eventually.of_forall
  intro p
  simp only [norm_mul, Complex.norm_exp]
  have hr : (-(a04VerticalPoint c p.1.1+a04VerticalPoint c p.1.2)*(p.2:ℂ)).re =
      (-2*c)*p.2 := by simp [a04VerticalPoint]; ring
  rw [hr]

theorem a04DoubleVerticalCoupling {c : ℝ} (hc : 0 < c)
    (F G : ℝ → ℂ) (hFc : Continuous F) (hGc : Continuous G)
    (hF : Integrable F) (hG : Integrable G) :
    (∫ y : ℝ × ℝ, F y.1*G y.2/
      (a04VerticalPoint c y.1+a04VerticalPoint c y.2) ∂(volume.prod volume)) =
    ∫ t in Ioi (0:ℝ),
      (∫ y : ℝ, F y*Complex.exp (-a04VerticalPoint c y*t))*
      (∫ y : ℝ, G y*Complex.exp (-a04VerticalPoint c y*t)) := by
  let H : (ℝ × ℝ) → ℝ → ℂ := fun y t => F y.1*G y.2*
    Complex.exp (-(a04VerticalPoint c y.1+a04VerticalPoint c y.2)*t)
  have hH : Integrable (Function.uncurry H)
      ((volume.prod volume).prod (volume.restrict (Ioi 0))) :=
    a04VerticalCoupling_integrable hc F G hFc hGc hF hG
  have hp (y : ℝ × ℝ) :
      (∫ t in Ioi (0:ℝ), H y t) =
        F y.1*G y.2/(a04VerticalPoint c y.1+a04VerticalPoint c y.2) := by
    dsimp [H]
    rw [integral_const_mul, integral_exp_mul_complex_Ioi]
    · simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq]
      ring
    · simp [a04VerticalPoint]
      linarith
  calc
    _ = ∫ y : ℝ × ℝ, (∫ t in Ioi (0:ℝ), H y t) ∂(volume.prod volume) := by
      simp_rw [hp]
    _ = ∫ t in Ioi (0:ℝ), ∫ y : ℝ × ℝ, H y t ∂(volume.prod volume) :=
      integral_integral_swap hH
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      have he : H = fun (y : ℝ × ℝ) (t : ℝ) =>
          (F y.1*Complex.exp (-a04VerticalPoint c y.1*t))*
          (G y.2*Complex.exp (-a04VerticalPoint c y.2*t)) := by
        funext y t
        dsimp [H]
        rw [show -(a04VerticalPoint c y.1+a04VerticalPoint c y.2)*(t:ℂ) =
          -a04VerticalPoint c y.1*t + -a04VerticalPoint c y.2*t by ring,
          Complex.exp_add]
        ring
      rw [he]
      dsimp only
      exact integral_prod_mul
        (fun y : ℝ => F y*Complex.exp (-a04VerticalPoint c y*t))
        (fun y : ℝ => G y*Complex.exp (-a04VerticalPoint c y*t))

end
end Sechstmoment
