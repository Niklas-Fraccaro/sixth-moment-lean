import Mathlib.NumberTheory.LSeries.DirichletContinuation
import SixthMoment.Arithmetic.Euler.FourL.CoefficientFactorization

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace SixthMoment.Source.NoDPGlobalLFactorization
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest NoDPGlobalConvolution
open scoped BigOperators
noncomputable section

def characterHom {q : ℕ} (χ : DirichletCharacter ℂ q) : ℕ →* ℂ where
  toFun n := χ n
  map_one' := by simp
  map_mul' m n := by simp [Nat.cast_mul,map_mul]

theorem twistedAF_mul (u : ℕ →* ℂ) (f g : ArithmeticFunction ℂ) :
    twistedAF u (f*g) = twistedAF u f * twistedAF u g := by
  ext n
  change (f*g) n * u n = _
  rw [ArithmeticFunction.mul_apply,ArithmeticFunction.mul_apply,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have H : u n = u p.1 * u p.2 := by
    rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1,map_mul]
  change f p.1 * g p.2 * u n = (f p.1*u p.1) * (g p.2*u p.2)
  rw [H]
  ring

theorem twisted_power_term {q : ℕ} (χ : DirichletCharacter ℂ q) (a z : ℂ) (n : ℕ) :
    LSeries.term (twistedAF (characterHom χ) (powerAF a)) z n =
      LSeries.term (fun n => χ n) (z+a) n := by
  by_cases hn : n = 0
  · simp [hn]
  rw [LSeries.term_def₀ ArithmeticFunction.map_zero,LSeries.term_of_ne_zero hn]
  change (powerAF a n * χ n) * (n:ℂ)^(-z) = χ n / (n:ℂ)^(z+a)
  rw [powerAF_apply a n hn,div_eq_mul_inv,← Complex.cpow_neg]
  rw [show -(z+a) = -a + -z by ring,Complex.cpow_add _ _ (by exact_mod_cast hn)]
  ring

theorem twisted_power_hasSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a z : ℂ) (h : 1 < (z+a).re) :
    LSeriesHasSum (twistedAF (characterHom χ) (powerAF a)) z (DirichletCharacter.LFunction χ (z+a)) := by
  have H : LSeriesHasSum (fun n => χ n) (z+a) (DirichletCharacter.LFunction χ (z+a)) := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ h]
    exact (DirichletCharacter.LSeriesSummable_of_one_lt_re χ h).LSeriesHasSum
  change HasSum _ _ at H ⊢
  convert H using 1
  funext n
  exact twisted_power_term χ a z n

def fourL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : Fin 4 → ℂ) (z : ℂ) : ℂ :=
  DirichletCharacter.LFunction χ (z+s 0) * (DirichletCharacter.LFunction χ (z+s 1) *
    (DirichletCharacter.LFunction χ (z+s 2) * DirichletCharacter.LFunction χ (z+s 3)))

theorem fourL_eq_product {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : Fin 4 → ℂ) (z : ℂ) :
    fourL χ s z = ∏ j : Fin 4, DirichletCharacter.LFunction χ (z+s j) := by
  simp [fourL,Fin.prod_univ_succ]

theorem twisted_four_hasSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : Fin 4 → ℂ) (z : ℂ) (H : ∀ j, 1 < (z+s j).re) :
    LSeriesHasSum (twistedAF (characterHom χ) (fourAF s)) z (fourL χ s z) := by
  have h := ArithmeticFunction.LSeriesHasSum_mul (twisted_power_hasSum χ (s 0) z (H 0))
    (ArithmeticFunction.LSeriesHasSum_mul (twisted_power_hasSum χ (s 1) z (H 1))
      (ArithmeticFunction.LSeriesHasSum_mul (twisted_power_hasSum χ (s 2) z (H 2))
        (twisted_power_hasSum χ (s 3) z (H 3))))
  simpa only [fourAF,twistedAF_mul,fourL] using h

end
end SixthMoment.Source.NoDPGlobalLFactorization
