import Sechstmoment.Analysis.Mellin.ComplexPoleShift
import Sechstmoment.Analysis.Mellin.PolePartialFractions


namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped Topology BigOperators
noncomputable section
set_option autoImplicit false

theorem mellinRectangle_separated_poles_shift
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (H : ℂ → ℂ) (hH : Differentiable ℂ H)
    (p : ι → ℂ) (hp : Function.Injective p) {a b : ℝ}
    (ha : ∀ i, a < (p i).re) (hb : ∀ i, (p i).re < b)
    (hLeft : ∀ i, Integrable (fun y : ℝ => H ((a:ℂ)+(y:ℂ)*I)/((a:ℂ)+(y:ℂ)*I-p i)))
    (hRight : ∀ i, Integrable (fun y : ℝ => H ((b:ℂ)+(y:ℂ)*I)/((b:ℂ)+(y:ℂ)*I-p i)))
    (hEdge : ∀ i, Tendsto (fun y : ℝ => ∫ c in a..b,
      H ((c:ℂ)+(y:ℂ)*I)/((c:ℂ)+(y:ℂ)*I-p i)) (cocompact ℝ) (𝓝 0)) :
    (∫ y : ℝ, H ((b:ℂ)+(y:ℂ)*I)/(∏ i : ι, (((b:ℂ)+(y:ℂ)*I)-p i))) =
      (∫ y : ℝ, H ((a:ℂ)+(y:ℂ)*I)/(∏ i : ι, (((a:ℂ)+(y:ℂ)*I)-p i)))+
      (2*Real.pi:ℂ)*(∑ i : ι,
        (((Finset.univ : Finset ι).erase i).prod (fun j : ι => p i-p j))⁻¹*H (p i)) := by
  classical
  let d : ι → ℂ := fun i =>
    (((Finset.univ : Finset ι).erase i).prod (fun j : ι => p i-p j))⁻¹
  let F : ℝ → ℝ → ℂ := fun c y => H ((c:ℂ)+(y:ℂ)*I)/
    (∏ i : ι, (((c:ℂ)+(y:ℂ)*I)-p i))
  let G : ι → ℝ → ℝ → ℂ := fun i c y =>
    H ((c:ℂ)+(y:ℂ)*I)/((c:ℂ)+(y:ℂ)*I-p i)
  have hpoint {c : ℝ} (hc : ∀ i, c ≠ (p i).re) (y : ℝ) :
      F c y = ∑ i, d i*G i c y := by
    have hz (i : ι) : (c:ℂ)+(y:ℂ)*I ≠ p i := by
      intro he
      have hre := congrArg Complex.re he
      simp only [add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero] at hre
      exact hc i hre
    dsimp only [F,G,d]
    rw [div_eq_mul_inv,separated_pole_partial_fractions p hp _ hz,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hint {c : ℝ} (hc : ∀ i, c ≠ (p i).re)
      (hi : ∀ i, Integrable (G i c)) :
      (∫ y : ℝ, F c y) = ∑ i, d i*(∫ y : ℝ, G i c y) := by
    calc
      _ = ∫ y : ℝ, ∑ i, d i*G i c y :=
        integral_congr_ae (Eventually.of_forall (hpoint hc))
      _ = ∑ i, ∫ y : ℝ, d i*G i c y :=
        integral_finsetSum _ (fun i _ => (hi i).const_mul (d i))
      _ = _ := by simp_rw [integral_const_mul]
  have hIa := hint (fun i => (ha i).ne) hLeft
  have hIb := hint (fun i => (hb i).ne') hRight
  have hshift (i : ι) :
      (∫ y : ℝ, G i b y) = (∫ y : ℝ, G i a y)+(2*Real.pi:ℂ)*H (p i) :=
    mellinRectangle_complex_simplePole_shift H hH (ha i) (hb i)
      (hLeft i) (hRight i) (hEdge i)
  change (∫ y : ℝ, F b y) = (∫ y : ℝ, F a y)+(2*Real.pi:ℂ)*(∑ i, d i*H (p i))
  rw [hIb,hIa]
  simp_rw [hshift,mul_add]
  rw [Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end Sechstmoment.Source
