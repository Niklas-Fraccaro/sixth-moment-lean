import SixthMoment.Numerator.V.Arithmetic.NonprincipalMellinContour
import SixthMoment.Numerator.V.Arithmetic.Principal.Gauss
import SixthMoment.Numerator.V.Arithmetic.Principal.MellinContour
import SixthMoment.Numerator.V.EulerTransfer.CorrectedMellin


namespace SixthMoment.Source.NoDPGlobalLFactorization
open Complex Real Set MeasureTheory Filter ZMod
open scoped BigOperators ContDiff Topology
noncomputable section
set_option autoImplicit false

def principalMellinResidueSum (q : ℕ) [NeZero q] (d : ℕ) (w : ℝ → ℂ)
    (β : Fin 4 → ℂ) (x : ℝ) : ℂ :=
  ∑ i : Fin 4, (((Finset.univ : Finset (Fin 4)).erase i).prod
    (fun j : Fin 4 => (1-β i)-(1-β j)))⁻¹*
      principalMellinNumerator q d w β x (1-β i)

theorem principalMellin_line_integrable {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    (q : ℕ) [NeZero q] (d : ℕ) (hd : d ≠ 0)
    (β : Fin 4 → ℂ) (hβ : ∀ j, ‖β j‖ ≤ 1/8)
    {x c : ℝ} (hx : 0 < x) (hc : c ∈ Icc (1/4:ℝ) (5/4))
    (hcp : ∀ j, c ≠ (1-β j).re) :
    Integrable (fun t : ℝ =>
      characterMellinIntegrand (1 : DirichletCharacter ℂ q) d w β x ((c:ℂ)+(t:ℂ)*I)) := by
  let H := principalMellinNumerator q d w β x
  let p : Fin 4 → ℂ := fun i => 1-β i
  have hH : Continuous H := (principalMellinNumerator_entire hw.continuous hws q d β hx).continuous
  obtain ⟨C,_hC,Hdecay⟩ := principalMellinNumerator_strip_decay hw hws q d hd hx 2
  have hi := finite_poles_line_integrable_of_square_decay H hH hc p hcp (Hdecay β hβ)
  apply hi.congr
  apply Eventually.of_forall
  intro t
  apply principalMellinNumerator_div_poles
  intro j he
  have hre := congrArg Complex.re he
  exact hcp j (by simpa using hre)

theorem characterMellin_boundary_integrable {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (d : ℕ) (hd : d ≠ 0)
    (β : Fin 4 → ℂ) {x a c : ℝ} (hx : 0 < x) (ha : 1/2 < a)
    (hc : c ∈ Icc a (5/4)) (hβ : ∀ j, ‖β j‖ ≤ min (1/8) (a-1/2))
    (hcp : ∀ j, c ≠ (1-β j).re) :
    Integrable (fun t : ℝ => characterMellinIntegrand χ d w β x ((c:ℂ)+(t:ℂ)*I)) := by
  by_cases hχ : χ = 1
  · subst χ
    exact principalMellin_line_integrable hw hws q d hd β
      (fun j => (hβ j).trans (min_le_left _ _)) hx ⟨by linarith [hc.1],hc.2⟩ hcp
  · have hF := nonprincipalMellinIntegrand_entire hw.continuous hws χ hχ d β hx
    obtain ⟨C,_hC,H⟩ := nonprincipalMellinIntegrand_strip_decay hw hws χ hχ d hd hx ha 2
    exact vertical_integrable_of_square_strip_decay _ hF.continuous hc (H β hβ)

theorem correctedMellin_contour_shift {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    (q : ℕ) [NeZero q] (d : ℕ) (hd : d ≠ 0)
    (β : Fin 4 → ℂ) (hsep : Function.Injective β) {x a b : ℝ}
    (hx : 0 < x) (ha : 1/2 < a) (hb : b ≤ 5/4)
    (hβ : ∀ j, ‖β j‖ ≤ min (1/8) (a-1/2))
    (hpa : ∀ j, a < (1-β j).re) (hpb : ∀ j, (1-β j).re < b) :
    (∫ t : ℝ, correctedMellinIntegrand q d w b β x t) =
      (∫ t : ℝ, correctedMellinIntegrand q d w a β x t)+
      (2*Real.pi:ℂ)*(q.totient:ℂ)⁻¹*(ArithmeticFunction.moebius q:ℂ)*
        principalMellinResidueSum q d w β x := by
  classical
  have hab : a ≤ b := (hpa 0).le.trans (hpb 0).le
  let F := fun (χ : DirichletCharacter ℂ q) (c t : ℝ) =>
    characterMellinIntegrand χ d w β x ((c:ℂ)+(t:ℂ)*I)
  let g := fun χ : DirichletCharacter ℂ q => gaussSum χ⁻¹ stdAddChar*χ (-1)
  let S := principalMellinResidueSum q d w β x
  have hi (χ : DirichletCharacter ℂ q) (c : ℝ) (hc : c ∈ Icc a (5/4))
      (hcp : ∀ j, c ≠ (1-β j).re) : Integrable (F χ c) :=
    characterMellin_boundary_integrable hw hws χ d hd β hx ha hc hβ hcp
  have hpoint (c t : ℝ) : correctedMellinIntegrand q d w c β x t =
      (q.totient:ℂ)⁻¹*∑ χ : DirichletCharacter ℂ q, g χ*F χ c t := by
    dsimp only [correctedMellinIntegrand,correctedGaussTransform,F,g,characterMellinIntegrand]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ _
    ring
  have hint (c : ℝ) (hc : c ∈ Icc a (5/4)) (hcp : ∀ j, c ≠ (1-β j).re) :
      (∫ t : ℝ, correctedMellinIntegrand q d w c β x t) =
        (q.totient:ℂ)⁻¹*∑ χ : DirichletCharacter ℂ q, g χ*(∫ t : ℝ, F χ c t) := by
    simp_rw [hpoint]
    rw [integral_const_mul,integral_finsetSum _ (fun χ _ => (hi χ c hc hcp).const_mul (g χ))]
    simp_rw [integral_const_mul]
  have hshift (χ : DirichletCharacter ℂ q) :
      (∫ t : ℝ, F χ b t) = (∫ t : ℝ, F χ a t)+
        (if χ = 1 then (2*Real.pi:ℂ)*S else 0) := by
    by_cases hχ : χ = 1
    · subst χ
      rw [ite_eq_left rfl]
      exact principalMellin_contour_shift hw hws q d hd β
        (fun j => (hβ j).trans (min_le_left _ _)) hsep hx (by linarith) hb hpa hpb
    · rw [ite_eq_right hχ,add_zero]
      exact nonprincipalMellin_contour_shift hw hws χ hχ d hd β hx ha hab hb hβ
  have hsum : (∑ χ : DirichletCharacter ℂ q,
      g χ*(if χ = 1 then (2*Real.pi:ℂ)*S else 0)) =
      g 1*((2*Real.pi:ℂ)*S) := by
    rw [← show g 1*(if (1 : DirichletCharacter ℂ q) = 1 then (2*Real.pi:ℂ)*S else 0) =
      g 1*((2*Real.pi:ℂ)*S) by rw [ite_eq_left rfl]]
    apply Finset.sum_eq_single (1 : DirichletCharacter ℂ q)
    · intro χ _ hχ
      rw [ite_eq_right hχ,mul_zero]
    · simp
  have hg : g 1 = (ArithmeticFunction.moebius q:ℂ) := by
    have hone : (1 : DirichletCharacter ℂ q) (-1) = 1 := by
      simpa using (MulChar.one_apply_coe (-1:(ZMod q)ˣ) :
        (1 : DirichletCharacter ℂ q) ((-1:(ZMod q)ˣ):ZMod q) = 1)
    dsimp only [g]
    rw [inv_one,hone,mul_one,principal_gaussSum_eq_moebius]
  rw [hint b ⟨hab,hb⟩ (fun j => (hpb j).ne'),
    hint a ⟨le_rfl,hab.trans hb⟩ (fun j => (hpa j).ne)]
  simp_rw [hshift,mul_add]
  rw [Finset.sum_add_distrib,mul_add,hsum,hg]
  ring

end
end SixthMoment.Source.NoDPGlobalLFactorization
