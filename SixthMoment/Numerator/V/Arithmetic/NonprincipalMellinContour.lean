import SixthMoment.Analysis.Mellin.MellinSquareDecay
import SixthMoment.Analysis.Mellin.SmoothMellinEntire
import SixthMoment.Arithmetic.Euler.FourL.Continuation
import SixthMoment.Numerator.U.ZeroModes.Transforms.PositiveTimeMellinStripDecay
import SixthMoment.Zeta.DirichletL.NonprincipalStrip


namespace SixthMoment.Source.NoDPGlobalLFactorization
open Complex Real Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology
noncomputable section
set_option autoImplicit false

def characterMellinIntegrand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (d : ℕ) (w : ℝ → ℂ) (β : Fin 4 → ℂ) (x : ℝ) (s : ℂ) : ℂ :=
  mellin w s*(x:ℂ)^s*shiftedContinuation χ d β s

theorem nonprincipalMellinIntegrand_entire {w : ℝ → ℂ}
    (hw : Continuous w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (d : ℕ) (β : Fin 4 → ℂ) {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (characterMellinIntegrand χ d w β x) := by
  have hxC : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hp : Differentiable ℂ (fun s : ℂ => (x:ℂ)^s) := by
    have he : (fun s : ℂ => (x:ℂ)^s) =
        fun s : ℂ => Complex.exp (Complex.log (x:ℂ)*s) :=
      funext (Complex.cpow_def_of_ne_zero hxC)
    rw [he]
    fun_prop
  exact ((compact_dyadic_mellin_entire hw hws).mul hp).mul
    (nonprincipal_continuation_entire χ hχ d β)

theorem nonprincipalMellinIntegrand_strip_decay {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (d : ℕ) (hd : d ≠ 0) {x a : ℝ} (hx : 0 < x) (ha : 1/2 < a) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : Fin 4 → ℂ,
      (∀ j, ‖β j‖ ≤ min (1/8) (a-1/2)) → ∀ s : ℂ, s.re ∈ Icc a (5/4) →
      (1+|s.im|)^n*‖characterMellinIntegrand χ d w β x s‖ ≤ C := by
  obtain ⟨A,hA,Hcorr⟩ := eulerCorrection_subpower (1/4) 1 (by norm_num) (by norm_num)
  obtain ⟨B,hB,HL⟩ := nonprincipalDirichlet_polynomial_strip χ hχ
  obtain ⟨D,hD,HM⟩ := a03PositiveTimeMellin_strip_full_height_decay hw hws a (5/4) (n+80)
  have hxcont : Continuous (fun c : ℝ => x^c) := by
    simpa only [Real.rpow_def_of_pos hx] using
      (show Continuous (fun c : ℝ => Real.exp (Real.log x*c)) by fun_prop)
  obtain ⟨X,hX⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc a (5/4:ℝ)) hxcont.continuousOn
  let Y := max 1 X
  have hY : 0 < Y := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let K := A*(d:ℝ)*Y*((2:ℝ)^20*B)^4
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K*(D+1)+1,by positivity,?_⟩
  intro β hβ s hs
  have hsmall (j : Fin 4) : ‖β j‖ ≤ 1/8 := (hβ j).trans (min_le_left _ _)
  have hp : ‖(x:ℂ)^s‖ ≤ Y := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    have hxp : x^s.re ≤ X := by
      simpa only [Real.norm_of_nonneg (Real.rpow_nonneg hx.le s.re)] using hX s.re hs
    exact hxp.trans (le_max_right _ _)
  have hc : ‖eulerCorrection χ d β s‖ ≤ A*(d:ℝ) := by
    simpa only [Real.rpow_one] using Hcorr q inferInstance χ d hd β
      (fun j => (hsmall j).trans (by norm_num)) s (by linarith [hs.1])
  have hLs : (∏ j : Fin 4, ‖χ.LFunction (s+β j)‖) ≤
      ((2:ℝ)^20*B)^4*(1+|s.im|)^80 := by
    calc
      _ ≤ ∏ _j : Fin 4, (2:ℝ)^20*B*(1+|s.im|)^20 := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro j _
        have hr := abs_le.mp ((Complex.abs_re_le_norm (β j)).trans (hsmall j))
        have hr' := abs_le.mp ((Complex.abs_re_le_norm (β j)).trans
          ((hβ j).trans (min_le_right _ _)))
        have hi := (Complex.abs_im_le_norm (β j)).trans (hsmall j)
        have hsr : (s+β j).re ∈ Icc (1/2:ℝ) (3/2) := by
          simp only [add_re]
          constructor <;> linarith [hs.1,hs.2,hr.2,hr'.1]
        have ht : 1+|(s+β j).im| ≤ 2*(1+|s.im|) := by
          rw [add_im]
          linarith [abs_add_le s.im (β j).im,abs_nonneg s.im]
        calc
          _ ≤ B*(1+|(s+β j).im|)^20 := HL _ hsr
          _ ≤ B*(2*(1+|s.im|))^20 := by gcongr
          _ = _ := by rw [mul_pow]; ring
      _ = _ := by simp; ring
  have hbound : ‖characterMellinIntegrand χ d w β x s‖ ≤
      K*((1+|s.im|)^80*‖mellin w s‖) := by
    rw [characterMellinIntegrand,shiftedContinuation,norm_mul,norm_mul,norm_mul,norm_prod]
    calc
      _ ≤ ‖mellin w s‖*Y*((A*(d:ℝ))*(((2:ℝ)^20*B)^4*(1+|s.im|)^80)) := by gcongr
      _ = _ := by dsimp only [K]; ring
  have hm : (1+|s.im|)^(n+80)*‖mellin w s‖ ≤ D := by
    simpa only [s.re_add_im] using HM s.re hs s.im
  calc
    _ ≤ (1+|s.im|)^n*(K*((1+|s.im|)^80*‖mellin w s‖)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = K*((1+|s.im|)^(n+80)*‖mellin w s‖) := by rw [pow_add]; ring
    _ ≤ K*D := mul_le_mul_of_nonneg_left hm hK
    _ ≤ K*(D+1)+1 := by nlinarith

theorem nonprincipalMellin_contour_shift {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (d : ℕ) (hd : d ≠ 0) (β : Fin 4 → ℂ) {x a b : ℝ}
    (hx : 0 < x) (ha : 1/2 < a) (hab : a ≤ b) (hb : b ≤ 5/4)
    (hβ : ∀ j, ‖β j‖ ≤ min (1/8) (a-1/2)) :
    (∫ t : ℝ, characterMellinIntegrand χ d w β x ((b:ℂ)+(t:ℂ)*I)) =
      ∫ t : ℝ, characterMellinIntegrand χ d w β x ((a:ℂ)+(t:ℂ)*I) := by
  let F := characterMellinIntegrand χ d w β x
  have hF : Differentiable ℂ F := nonprincipalMellinIntegrand_entire hw.continuous hws χ hχ d β hx
  obtain ⟨C,_hC,H⟩ := nonprincipalMellinIntegrand_strip_decay hw hws χ hχ d hd hx ha 2
  have hbound (s : ℂ) (hs : s.re ∈ Icc a b) : (1+|s.im|)^2*‖F s‖ ≤ C :=
    H β hβ s ⟨hs.1,hs.2.trans hb⟩
  exact vertical_integrals_eq_of_holomorphic F hab (fun s _ _ => hF s)
    (vertical_integrable_of_square_strip_decay F hF.continuous ⟨le_rfl,hab⟩ hbound)
    (vertical_integrable_of_square_strip_decay F hF.continuous ⟨hab,le_rfl⟩ hbound)
    (horizontal_tendsto_zero_of_square_strip_decay F hab hbound)

end
end SixthMoment.Source.NoDPGlobalLFactorization
