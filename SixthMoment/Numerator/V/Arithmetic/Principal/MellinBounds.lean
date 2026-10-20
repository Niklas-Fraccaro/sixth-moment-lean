import SixthMoment.Numerator.U.ZeroModes.Transforms.PositiveTimeMellinStripDecay
import SixthMoment.Numerator.V.Arithmetic.Principal.MellinNumerator
import SixthMoment.Zeta.Bounds.ZetaPolynomialBound


namespace SixthMoment.Source.NoDPGlobalLFactorization
open Complex Real Set MeasureTheory
open scoped BigOperators ContDiff
noncomputable section

theorem principal_regularizedL_eq_euler_zeta (q : ℕ) [NeZero q] (s : ℂ) :
    DirichletCharacter.LFunctionTrivChar₁ q s =
      (∏ p ∈ q.primeFactors, (1-(p:ℂ)^(-s)))*polarRegularizedZeta s := by
  by_cases hs : s = 1
  · subst s
    rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_self,
      polarRegularizedZeta_one,mul_one]
    apply Finset.prod_congr rfl
    intro p _
    rw [Complex.cpow_neg,Complex.cpow_one]
  · rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hs,
      polarRegularizedZeta_of_ne_one hs]
    rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) hs]
    ring

theorem principal_regularizedL_polynomial_bound (q : ℕ) [NeZero q] :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Icc (0:ℝ) (3/2) →
      ‖DirichletCharacter.LFunctionTrivChar₁ q s‖ ≤ C*(1+|s.im|)^2 := by
  obtain ⟨A,hA,H⟩ := polarRegularizedZeta_polynomial_crossing_strip
  refine ⟨(2:ℝ)^q.primeFactors.card*A,by positivity,?_⟩
  intro s hs
  have heuler : ‖∏ p ∈ q.primeFactors, (1-(p:ℂ)^(-s))‖ ≤ (2:ℝ)^q.primeFactors.card := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _p ∈ q.primeFactors, (2:ℝ) := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro p hp
        have hprime := Nat.prime_of_mem_primeFactors hp
        have hpow : ‖(p:ℂ)^(-s)‖ ≤ 1 := by
          rw [Complex.norm_natCast_cpow_of_pos hprime.pos,neg_re]
          exact Real.rpow_le_one_of_one_le_of_nonpos
            (by exact_mod_cast hprime.one_le) (by linarith [hs.1])
        calc
          _ ≤ ‖(1:ℂ)‖+‖(p:ℂ)^(-s)‖ := norm_sub_le _ _
          _ = 1+‖(p:ℂ)^(-s)‖ := by rw [norm_one]
          _ ≤ 2 := by linarith
      _ = _ := by simp
  rw [principal_regularizedL_eq_euler_zeta,norm_mul]
  exact (mul_le_mul heuler (H s ⟨by linarith [hs.1],hs.2⟩)
    (norm_nonneg _) (by positivity)).trans_eq (by ring)

theorem principalMellinNumerator_strip_decay {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    (q : ℕ) [NeZero q] (d : ℕ) (hd : d ≠ 0)
    {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : Fin 4 → ℂ, (∀ j, ‖β j‖ ≤ 1/8) →
      ∀ s : ℂ, s.re ∈ Icc (1/4:ℝ) (5/4) →
      (1+|s.im|)^n*‖principalMellinNumerator q d w β x s‖ ≤ C := by
  obtain ⟨A,hA,Hcorr⟩ := eulerCorrection_subpower (1/4) 1 (by norm_num) (by norm_num)
  obtain ⟨B,hB,HL⟩ := principal_regularizedL_polynomial_bound q
  obtain ⟨D,hD,HM⟩ := a03PositiveTimeMellin_strip_full_height_decay hw hws (1/4) (5/4) (n+8)
  have hxcont : Continuous (fun a : ℝ => x^a) := by
    simpa only [Real.rpow_def_of_pos hx] using
      (show Continuous (fun a : ℝ => Real.exp (Real.log x*a)) by fun_prop)
  obtain ⟨X,hX⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (1/4:ℝ) (5/4)) hxcont.continuousOn
  let Y := max 1 X
  have hY : 0 < Y := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let K := A*(d:ℝ)*Y*(4*B)^4
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K*(D+1)+1,by positivity,?_⟩
  intro β hβ s hs
  have hp : ‖(x:ℂ)^s‖ ≤ Y := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    have hxp : x^s.re ≤ X := by
      simpa only [Real.norm_of_nonneg (Real.rpow_nonneg hx.le s.re)] using hX s.re hs
    exact hxp.trans (le_max_right _ _)
  have hc : ‖eulerCorrection (1 : DirichletCharacter ℂ q) d β s‖ ≤ A*(d:ℝ) := by
    simpa only [Real.rpow_one] using
      Hcorr q inferInstance (1 : DirichletCharacter ℂ q) d hd β
        (fun j => (hβ j).trans (by norm_num)) s hs.1
  have hLs : (∏ j : Fin 4, ‖DirichletCharacter.LFunctionTrivChar₁ q (s+β j)‖) ≤
      (4*B)^4*(1+|s.im|)^8 := by
    calc
      _ ≤ ∏ _j : Fin 4, 4*B*(1+|s.im|)^2 := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro j _
        have hr := abs_le.mp ((Complex.abs_re_le_norm (β j)).trans (hβ j))
        have hi := (Complex.abs_im_le_norm (β j)).trans (hβ j)
        have hsr : (s+β j).re ∈ Icc (0:ℝ) (3/2) := by
          simp only [add_re]
          constructor <;> linarith [hs.1,hs.2,hr.1,hr.2]
        have ht : 1+|(s+β j).im| ≤ 2*(1+|s.im|) := by
          rw [add_im]
          linarith [abs_add_le s.im (β j).im,abs_nonneg s.im]
        calc
          _ ≤ B*(1+|(s+β j).im|)^2 := HL _ hsr
          _ ≤ B*(2*(1+|s.im|))^2 := by gcongr
          _ = _ := by ring
      _ = _ := by simp; ring
  have hbound : ‖principalMellinNumerator q d w β x s‖ ≤
      K*((1+|s.im|)^8*‖mellin w s‖) := by
    rw [principalMellinNumerator,norm_mul,norm_mul,norm_mul,norm_prod]
    calc
      _ ≤ ‖mellin w s‖*Y*(A*(d:ℝ))*((4*B)^4*(1+|s.im|)^8) := by gcongr
      _ = _ := by dsimp only [K]; ring
  have hm : (1+|s.im|)^(n+8)*‖mellin w s‖ ≤ D := by
    simpa only [s.re_add_im] using HM s.re hs s.im
  calc
    _ ≤ (1+|s.im|)^n*(K*((1+|s.im|)^8*‖mellin w s‖)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = K*((1+|s.im|)^(n+8)*‖mellin w s‖) := by rw [pow_add]; ring
    _ ≤ K*D := mul_le_mul_of_nonneg_left hm hK
    _ ≤ K*(D+1)+1 := by nlinarith

end
end SixthMoment.Source.NoDPGlobalLFactorization
