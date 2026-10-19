import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Sechstmoment.Analysis.Mellin.SmoothMellinSeries
import Sechstmoment.Arithmetic.Euler.FourL.Continuation

/-! Actual character-dependent Mellin insertion on the absolute starting
line, including convergence of the resulting Mellin integral. -/

namespace Sechstmoment.Source.NoDPGlobalLFactorization
open Complex Real Set MeasureTheory
open scoped BigOperators ContDiff
noncomputable section

theorem shifted_positive_dirichlet_hasSum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (d : ℕ) (hd : d ≠ 0) (β : Fin 4 → ℂ)
    (s : ℂ) (hs : ∀ j, 1 < (s+β j).re) :
    HasSum (fun n : ℕ+ => fourAF β (d*n)*χ n*(n:ℂ)^(-s))
      (shiftedContinuation χ d β s) := by
  have H := shiftedTerm_hasSum χ d hd β s hs
  change HasSum (shiftedTerm χ d β s) (shiftedContinuation χ d β s) at H
  have h0 : shiftedTerm χ d β s 0 = 0 := by simp [shiftedTerm]
  have Hp : HasSum (fun n : ℕ+ => shiftedTerm χ d β s n) (shiftedContinuation χ d β s) :=
    hasSum_pnat_iff.mpr (by simpa only [h0,add_zero] using H)
  simpa only [shiftedTerm] using Hp

theorem shifted_positive_dirichlet_absolute {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (d : ℕ) (hd : d ≠ 0) (β : Fin 4 → ℂ)
    (c : ℝ) (hc : ∀ j, 1 < c+(β j).re) :
    Summable (fun n : ℕ+ => ‖fourAF β (d*n)*χ n‖*(n:ℝ)^(-c)) := by
  have H := (shifted_positive_dirichlet_hasSum χ d hd β (c:ℂ) (by
    simpa only [add_re,ofReal_re] using hc)).summable.norm
  apply H.congr
  intro n
  have hn : 0 < (n:ℝ) := by exact_mod_cast n.pos
  rw [norm_mul,show (n:ℂ) = ((n:ℝ):ℂ) by simp,
    Complex.norm_cpow_eq_rpow_re_of_pos hn]
  simp

theorem shiftedContinuation_starting_line_integrable {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (d : ℕ) (hd : d ≠ 0)
    (β : Fin 4 → ℂ) (c : ℝ) (hc : ∀ j, 1 < c+(β j).re) {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => mellin w ((c:ℂ)+(t:ℂ)*I)*(x:ℂ)^((c:ℂ)+(t:ℂ)*I)*
      shiftedContinuation χ d β ((c:ℂ)+(t:ℂ)*I)) := by
  let B := ∑' n : ℕ+, ‖fourAF β (d*n)*χ n‖*(n:ℝ)^(-c)
  have hB : 0 ≤ B := tsum_nonneg (fun n => by positivity)
  have hmass := shifted_positive_dirichlet_absolute χ d hd β c hc
  have hline (t : ℝ) : ∀ j, 1 < ((c:ℂ)+(t:ℂ)*I+β j).re := by
    intro j
    simpa only [add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero] using hc j
  have hbound (t : ℝ) : ‖shiftedContinuation χ d β ((c:ℂ)+(t:ℂ)*I)‖ ≤ B := by
    have H := shifted_positive_dirichlet_hasSum χ d hd β _ (hline t)
    have he (n : ℕ+) :
        ‖fourAF β (d*n)*χ n*(n:ℂ)^(-((c:ℂ)+(t:ℂ)*I))‖ =
          ‖fourAF β (d*n)*χ n‖*(n:ℝ)^(-c) := by
      have hn : 0 < (n:ℝ) := by exact_mod_cast n.pos
      rw [norm_mul,show (n:ℂ) = ((n:ℝ):ℂ) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos hn]
      simp
    rw [← H.tsum_eq]
    exact (norm_tsum_le_tsum_norm (hmass.congr (fun n => (he n).symm))).trans_eq (by
      dsimp only [B]
      simp_rw [he])
  have hpath : Continuous (fun t : ℝ => (c:ℂ)+(t:ℂ)*I) := by fun_prop
  have hL : Continuous (fun t : ℝ => shiftedContinuation χ d β ((c:ℂ)+(t:ℂ)*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (continuation_differentiableAt χ d β _ _).continuousAt.comp hpath.continuousAt
    intro j
    left
    intro he
    have H := hline t j
    rw [he,one_re] at H
    exact (lt_irrefl _ H)
  have hpow : Continuous (fun t : ℝ => (x:ℂ)^((c:ℂ)+(t:ℂ)*I)) :=
    hpath.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have hcont := ((smooth_mellin_line_continuous hw hws c).mul hpow).mul hL
  apply ((smooth_dyadic_mellin_vertical_integrable hw hws c).norm.const_mul (x^c*B)).mono'
    hcont.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  simp only [Pi.mul_apply]
  rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero]
  calc
    _ ≤ ‖mellin w ((c:ℂ)+(t:ℂ)*I)‖*x^c*B := by gcongr; exact hbound t
    _ = _ := by ring

theorem shifted_character_mellin_inversion {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (d : ℕ) (hd : d ≠ 0)
    (β : Fin 4 → ℂ) (c : ℝ) (hc : ∀ j, 1 < c+(β j).re) {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ+, (fourAF β (d*n)*χ n)*w ((n:ℝ)/x)) =
      (1/(2*Real.pi):ℂ)*(∫ t : ℝ,
        mellin w ((c:ℂ)+(t:ℂ)*I)*(x:ℂ)^((c:ℂ)+(t:ℂ)*I)*
          shiftedContinuation χ d β ((c:ℂ)+(t:ℂ)*I)) := by
  have hp (t : ℝ) :
      (∑' n : ℕ+, fourAF β (d*n)*χ n*(n:ℂ)^(-((c:ℂ)+(t:ℂ)*I))) =
        shiftedContinuation χ d β ((c:ℂ)+(t:ℂ)*I) := by
    apply (shifted_positive_dirichlet_hasSum χ d hd β _ _).tsum_eq
    intro j
    simpa only [add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero] using hc j
  have H := smooth_mellin_dirichlet_inversion hw hws c
    (fun n : ℕ+ => fourAF β (d*n)*χ n) hx
    (shifted_positive_dirichlet_absolute χ d hd β c hc)
  simpa only [hp] using H

end
end Sechstmoment.Source.NoDPGlobalLFactorization
