import SixthMoment.Analysis.Simplex.RadialIntegral
import SixthMoment.Numerator.V.DP.DPNormalization


namespace SixthMoment
open MeasureTheory Set
open scoped Topology

set_option maxHeartbeats 0

theorem complex_interval_scale (η H : ℝ) (f : ℝ → ℂ) :
    (∫ x in (0:ℝ)..η*H, f x) =
      (η:ℂ)*(∫ x in (0:ℝ)..H, f (η*x)) := by
  have h := intervalIntegral.smul_integral_comp_mul_left
    (a := (0:ℝ)) (b := H) f η
  simpa only [mul_zero, Complex.real_smul] using h.symm

theorem complex_simplex_scale (η : ℝ) (f : ℝ → ℝ → ℝ → ℂ) :
    (∫ x in (0:ℝ)..η, ∫ y in (0:ℝ)..η-x,
      ∫ w in (0:ℝ)..η-x-y, f x y w) =
      (η:ℂ)^3*(∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1-x,
        ∫ w in (0:ℝ)..1-x-y, f (η*x) (η*y) (η*w)) := by
  have hy (x : ℝ) : η-η*x = η*(1-x) := by ring
  have hz (x y : ℝ) : η*(1-x)-η*y = η*(1-x-y) := by ring
  have hin (x y : ℝ) :
      (∫ w in (0:ℝ)..η*(1-x)-η*y, f (η*x) (η*y) w) =
        (η:ℂ)*(∫ w in (0:ℝ)..1-x-y, f (η*x) (η*y) (η*w)) := by
    rw [hz, complex_interval_scale]
  have him (x : ℝ) :
      (∫ y in (0:ℝ)..η-η*x, ∫ w in (0:ℝ)..η-η*x-y, f (η*x) y w) =
        (η:ℂ)^2*(∫ y in (0:ℝ)..1-x,
          ∫ w in (0:ℝ)..1-x-y, f (η*x) (η*y) (η*w)) := by
    rw [hy, complex_interval_scale]
    simp_rw [hin, intervalIntegral.integral_const_mul]
    ring
  rw [show η = η*1 by ring, complex_interval_scale]
  simp only [mul_one]
  simp_rw [him, intervalIntegral.integral_const_mul]
  ring

theorem weighted_triangle_eq_dpNormalizedTriple {η : ℝ} (hη : 0 < η)
    (P : Polynomial ℝ) (β γ δ : ℂ) :
    (∫ a in (0:ℝ)..η,
      ((Polynomial.eval (1-a/η : ℝ) P : ℝ):ℂ)*
        simplexTriangleExpIntegral (-β) γ δ 1 0 a) =
      (η:ℂ)^3*Source.dpNormalizedTriple η P β γ δ := by
  have hi (a : ℝ) :
      ((Polynomial.eval (1-a/η : ℝ) P : ℝ):ℂ)*
        simplexTriangleExpIntegral (-β) γ δ 1 0 a =
      ∫ x in (0:ℝ)..a, ∫ y in (0:ℝ)..a-x,
        ((Polynomial.eval (1-a/η : ℝ) P : ℝ):ℂ)*
          Complex.exp (-β*x+γ*y+δ*(a-x-y : ℝ)) := by
    unfold simplexTriangleExpIntegral
    simp only [one_mul, add_zero]
    rw [← intervalIntegral.integral_const_mul]
    simp_rw [← intervalIntegral.integral_const_mul]
  simp_rw [hi]
  rw [radial_simplex_integral η hη.le]
  · have he (x y w : ℝ) : (x+y+w)-x-y = w := by ring
    simp_rw [he]
    rw [complex_simplex_scale]
    unfold Source.dpNormalizedTriple
    congr 1
    apply intervalIntegral.integral_congr
    intro x _
    apply intervalIntegral.integral_congr
    intro y _
    apply intervalIntegral.integral_congr
    intro w _
    dsimp only
    have hp : 1-(η*x+η*y+η*w)/η = 1-x-y-w := by field_simp; ring
    rw [hp]
    congr 2
    push_cast
    ring
  · fun_prop

theorem dpNormalizedTriple_add (η : ℝ) (P Q : Polynomial ℝ) (β γ δ : ℂ) :
    Source.dpNormalizedTriple η (P+Q) β γ δ =
      Source.dpNormalizedTriple η P β γ δ + Source.dpNormalizedTriple η Q β γ δ := by
  unfold Source.dpNormalizedTriple
  simp only [Polynomial.eval_add, Complex.ofReal_add, add_mul]
  have hinner (R : Polynomial ℝ) (x y : ℝ) : Continuous (fun w : ℝ =>
      ((Polynomial.eval (1-x-y-w : ℝ) R : ℝ):ℂ)*
        Complex.exp ((η:ℂ)*(-β*x+γ*y+δ*w))) := by fun_prop
  have hmiddle (R : Polynomial ℝ) (x : ℝ) : Continuous (fun y : ℝ =>
      ∫ w in (0:ℝ)..1-x-y,
        ((Polynomial.eval (1-x-y-w : ℝ) R : ℝ):ℂ)*
          Complex.exp ((η:ℂ)*(-β*x+γ*y+δ*w))) := by fun_prop
  have houter (R : Polynomial ℝ) : Continuous (fun x : ℝ =>
      ∫ y in (0:ℝ)..1-x, ∫ w in (0:ℝ)..1-x-y,
        ((Polynomial.eval (1-x-y-w : ℝ) R : ℝ):ℂ)*
          Complex.exp ((η:ℂ)*(-β*x+γ*y+δ*w))) := by fun_prop
  have hw (x y : ℝ) := intervalIntegral.integral_add (μ := volume)
    ((hinner P x y).intervalIntegrable 0 (1-x-y))
    ((hinner Q x y).intervalIntegrable 0 (1-x-y))
  simp_rw [hw]
  have hy (x : ℝ) := intervalIntegral.integral_add (μ := volume)
    ((hmiddle P x).intervalIntegrable 0 (1-x))
    ((hmiddle Q x).intervalIntegrable 0 (1-x))
  simp_rw [hy]
  exact intervalIntegral.integral_add ((houter P).intervalIntegrable 0 1)
    ((houter Q).intervalIntegrable 0 1)

theorem dpNormalizedTriple_neg (η : ℝ) (P : Polynomial ℝ) (β γ δ : ℂ) :
    Source.dpNormalizedTriple η (-P) β γ δ = -Source.dpNormalizedTriple η P β γ δ := by
  unfold Source.dpNormalizedTriple
  simp only [Polynomial.eval_neg, Complex.ofReal_neg, neg_mul,
    intervalIntegral.integral_neg]

theorem dpNormalizedTriple_sub (η : ℝ) (P Q : Polynomial ℝ) (β γ δ : ℂ) :
    Source.dpNormalizedTriple η (P-Q) β γ δ =
      Source.dpNormalizedTriple η P β γ δ - Source.dpNormalizedTriple η Q β γ δ := by
  rw [sub_eq_add_neg, dpNormalizedTriple_add, dpNormalizedTriple_neg, sub_eq_add_neg]

end SixthMoment
