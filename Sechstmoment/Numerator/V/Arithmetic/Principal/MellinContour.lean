import Sechstmoment.Analysis.Mellin.MultiPoleShift
import Sechstmoment.Analysis.Mellin.SimplePoleDecay
import Sechstmoment.Numerator.V.Arithmetic.Principal.MellinBounds


namespace Sechstmoment.Source.NoDPGlobalLFactorization
open Complex Real Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology
noncomputable section
set_option autoImplicit false

theorem principalMellin_contour_shift {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    (q : ℕ) [NeZero q] (d : ℕ) (hd : d ≠ 0)
    (β : Fin 4 → ℂ) (hβ : ∀ j, ‖β j‖ ≤ 1/8) (hsep : Function.Injective β)
    {x : ℝ} (hx : 0 < x) {a b : ℝ} (ha : 1/4 ≤ a) (hb : b ≤ 5/4)
    (hpa : ∀ i, a < (1-β i).re) (hpb : ∀ i, (1-β i).re < b) :
    (∫ t : ℝ, mellin w ((b:ℂ)+(t:ℂ)*I)*(x:ℂ)^((b:ℂ)+(t:ℂ)*I)*
      shiftedContinuation (1 : DirichletCharacter ℂ q) d β ((b:ℂ)+(t:ℂ)*I)) =
      (∫ t : ℝ, mellin w ((a:ℂ)+(t:ℂ)*I)*(x:ℂ)^((a:ℂ)+(t:ℂ)*I)*
        shiftedContinuation (1 : DirichletCharacter ℂ q) d β ((a:ℂ)+(t:ℂ)*I))+
      (2*Real.pi:ℂ)*(∑ i : Fin 4,
        (((Finset.univ : Finset (Fin 4)).erase i).prod
          (fun j : Fin 4 => (1-β i)-(1-β j)))⁻¹*
            principalMellinNumerator q d w β x (1-β i)) := by
  let H := principalMellinNumerator q d w β x
  let p : Fin 4 → ℂ := fun i => 1-β i
  have hH : Differentiable ℂ H := principalMellinNumerator_entire hw.continuous hws q d β hx
  have hp : Function.Injective p := by
    intro i j hij
    apply hsep
    dsimp only [p] at hij
    linear_combination -hij
  have hab : a ≤ b := (hpa 0).le.trans (hpb 0).le
  obtain ⟨C,_hC,Hdecay⟩ := principalMellinNumerator_strip_decay hw hws q d hd hx 2
  have hbound (s : ℂ) (hs : s.re ∈ Icc a b) : (1+|s.im|)^2*‖H s‖ ≤ C :=
    Hdecay β hβ s ⟨ha.trans hs.1,hs.2.trans hb⟩
  have hleft (i : Fin 4) : Integrable (fun t : ℝ =>
      H ((a:ℂ)+(t:ℂ)*I)/((a:ℂ)+(t:ℂ)*I-p i)) :=
    simple_pole_line_integrable_of_square_decay H hH.continuous ⟨le_rfl,hab⟩
      (p i) (hpa i).ne hbound
  have hright (i : Fin 4) : Integrable (fun t : ℝ =>
      H ((b:ℂ)+(t:ℂ)*I)/((b:ℂ)+(t:ℂ)*I-p i)) :=
    simple_pole_line_integrable_of_square_decay H hH.continuous ⟨hab,le_rfl⟩
      (p i) (hpb i).ne' hbound
  have hedge (i : Fin 4) : Tendsto (fun t : ℝ => ∫ c in a..b,
      H ((c:ℂ)+(t:ℂ)*I)/((c:ℂ)+(t:ℂ)*I-p i)) (cocompact ℝ) (𝓝 0) :=
    simple_pole_horizontal_tendsto_zero_of_square_decay H hab (p i) hbound
  have hpoint {c : ℝ} (hc : ∀ i, c ≠ (p i).re) (t : ℝ) :
      H ((c:ℂ)+(t:ℂ)*I)/(∏ i : Fin 4, ((c:ℂ)+(t:ℂ)*I-p i)) =
        mellin w ((c:ℂ)+(t:ℂ)*I)*(x:ℂ)^((c:ℂ)+(t:ℂ)*I)*
          shiftedContinuation (1 : DirichletCharacter ℂ q) d β ((c:ℂ)+(t:ℂ)*I) := by
    apply principalMellinNumerator_div_poles
    intro i he
    have hre := congrArg Complex.re he
    exact hc i (by simpa only [add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero] using hre)
  have HS := mellinRectangle_separated_poles_shift H hH p hp hpa hpb hleft hright hedge
  simpa only [hpoint (fun i => (hpa i).ne),hpoint (fun i => (hpb i).ne'),H,p] using HS

end
end Sechstmoment.Source.NoDPGlobalLFactorization
