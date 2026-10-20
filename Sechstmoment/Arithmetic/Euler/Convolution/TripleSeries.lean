import Sechstmoment.Arithmetic.Euler.Convolution.DirichletCoefficients

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Sechstmoment.Source.NoDPGlobalConvolution
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest
open scoped BigOperators
noncomputable section

theorem powerAF_term (z u : ℂ) (h : 1 < (u+z).re) (n : ℕ) :
    LSeries.term (powerAF z) u n =
      riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re h) n := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [LSeries.term_def₀ ArithmeticFunction.map_zero, powerAF_apply z n hn]
    change (n:ℂ)^(-z) * (n:ℂ)^(-u) = (n:ℂ)^(-(u+z))
    rw [← Complex.cpow_add _ _ (by exact_mod_cast hn)]
    congr 1
    ring

theorem powerAF_hasSum (z u : ℂ) (h : 1 < (u+z).re) :
    LSeriesHasSum (powerAF z) u (riemannZeta (u+z)) := by
  have H := (summable_riemannZetaSummand h).of_norm.hasSum
  rw [tsum_riemannZetaSummand h] at H
  change HasSum (LSeries.term (powerAF z) u) (riemannZeta (u+z))
  convert H using 1
  funext n
  exact powerAF_term z u h n

def tripleZeta (s : Fin 4 → ℂ) (u : ℂ) : ℂ :=
  riemannZeta (1+u+s 1) * (riemannZeta (1+u+s 2) * riemannZeta (1+u+s 3))

def tripleTerm (s : Fin 4 → ℂ) (u : ℂ) (n : ℕ) : ℂ := tripleCoeff s n * (n:ℂ)^(-u)

theorem tripleTerm_eq_LSeries (s : Fin 4 → ℂ) (u : ℂ) (n : ℕ) :
    tripleTerm s u n = LSeries.term (tripleAF s) u n :=
  (LSeries.term_def₀ ArithmeticFunction.map_zero u n).symm

theorem tripleTerm_hasSum (s : Fin 4 → ℂ) (u : ℂ)
    (H : ∀ j : Fin 3, 1 < (1+u+s j.succ).re) :
    HasSum (tripleTerm s u) (tripleZeta s u) := by
  have H1' := H (0 : Fin 3)
  have H2' := H (1 : Fin 3)
  have H3' := H (2 : Fin 3)
  change 1 < (1+u+s 1).re at H1'
  change 1 < (1+u+s 2).re at H2'
  change 1 < (1+u+s 3).re at H3'
  have H1 : 1 < (u+(1+s 1)).re := by simpa only [add_assoc,add_left_comm u 1] using H1'
  have H2 : 1 < (u+(1+s 2)).re := by simpa only [add_assoc,add_left_comm u 1] using H2'
  have H3 : 1 < (u+(1+s 3)).re := by simpa only [add_assoc,add_left_comm u 1] using H3'
  have h := ArithmeticFunction.LSeriesHasSum_mul (powerAF_hasSum (1+s 1) u H1)
    (ArithmeticFunction.LSeriesHasSum_mul (powerAF_hasSum (1+s 2) u H2)
      (powerAF_hasSum (1+s 3) u H3))
  rw [show tripleTerm s u = LSeries.term (tripleAF s) u from funext (tripleTerm_eq_LSeries s u)]
  simpa only [LSeriesHasSum, tripleAF, tripleZeta, add_assoc,add_left_comm u 1] using h

theorem shifted_zeta_region (s : Fin 4 → ℂ) (ρ : ℝ) (hs : ∀ j, ‖s j‖ ≤ ρ)
    (u : ℂ) (hu : ρ < u.re) (j : Fin 3) : 1 < (1+u+s j.succ).re := by
  have H := (Complex.re_le_norm (-(s j.succ))).trans (by simpa using hs j.succ)
  simp only [Complex.add_re,Complex.one_re]
  simp only [Complex.neg_re] at H
  linarith

theorem tripleTerm_uniform_hasSum (s : Fin 4 → ℂ) (ρ : ℝ) (hs : ∀ j, ‖s j‖ ≤ ρ)
    (u : ℂ) (hu : ρ < u.re) : HasSum (tripleTerm s u) (tripleZeta s u) :=
  tripleTerm_hasSum s u (shifted_zeta_region s ρ hs u hu)

theorem tripleTerm_absolute (s : Fin 4 → ℂ) (ρ : ℝ) (hs : ∀ j, ‖s j‖ ≤ ρ)
    (u : ℂ) (hu : ρ < u.re) : Summable (fun n => ‖tripleTerm s u n‖) :=
  (tripleTerm_uniform_hasSum s ρ hs u hu).summable.norm

@[simp] theorem tripleTerm_zero (s : Fin 4 → ℂ) (u : ℂ) : tripleTerm s u 0 = 0 := by
  simp [tripleTerm]

end
end Sechstmoment.Source.NoDPGlobalConvolution
