import Sechstmoment.Zeta.AFE.Four.Definitions


namespace Sechstmoment.Source
open Complex
open scoped BigOperators

noncomputable section

private theorem fourNat_cpow (a b c d : ℕ) (q : ℂ) :
    (((a*b*c*d : ℕ) : ℂ)^q) =
      (a : ℂ)^q*(b : ℂ)^q*(c : ℂ)^q*(d : ℂ)^q := by
  rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow,
    Nat.cast_mul, Complex.natCast_mul_natCast_cpow,
    Nat.cast_mul, Complex.natCast_mul_natCast_cpow]

theorem fixedAFEFourDirichlet_factorization
    (n : Fin 4 → ℕ) (t : ℝ) (α : MomentShifts) (z : ℂ) :
    (∏ j : Fin 4, 1/(n j+1 : ℂ)^(sourceZetaPoints t j+α j+z)) =
      ((((n 0+1)*(n 1+1) : ℕ) : ℂ) /
        (((n 2+1)*(n 3+1) : ℕ) : ℂ))^(-(t : ℂ)*I) *
      ((positiveQuadProduct n : ℂ)^(-z)) /
        ∏ j : Fin 4, (n j+1 : ℂ)^(1/2+α j) := by
  have hn (j : Fin 4) : (n j+1 : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (n j)
  have hexp (j : Fin 4) :
      sourceZetaPoints t j+α j+z =
        (1/2+α j)+z+
          (if j.val < 2 then (t : ℂ)*I else -((t : ℂ)*I)) := by
    fin_cases j <;> simp [sourceZetaPoints, criticalLinePoint] <;> ring
  have hp (j : Fin 4) :
      (n j+1 : ℂ)^(sourceZetaPoints t j+α j+z) =
        (n j+1 : ℂ)^(1/2+α j)*(n j+1 : ℂ)^z *
          (n j+1 : ℂ)^(if j.val < 2 then (t : ℂ)*I else -((t : ℂ)*I)) := by
    rw [hexp, Complex.cpow_add _ _ (hn j), Complex.cpow_add _ _ (hn j)]
  have hratio := Complex.div_cpow_ofReal_nonneg
    (a := (((n 0+1)*(n 1+1) : ℕ) : ℝ))
    (b := (((n 2+1)*(n 3+1) : ℕ) : ℝ))
    (by positivity) (by positivity) (-(t : ℂ)*I)
  simp only [Complex.ofReal_natCast] at hratio
  simp only [Nat.cast_mul] at hratio
  rw [Complex.natCast_mul_natCast_cpow,
    Complex.natCast_mul_natCast_cpow] at hratio
  simp only [Nat.cast_add, Nat.cast_one] at hratio
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [hratio]
  rw [show (positiveQuadProduct n : ℂ)^(-z) =
      (n 0+1 : ℂ)^(-z)*(n 1+1 : ℂ)^(-z)*
        (n 2+1 : ℂ)^(-z)*(n 3+1 : ℂ)^(-z) by
    simpa only [positiveQuadProduct, Nat.cast_add, Nat.cast_one] using
      fourNat_cpow (n 0+1) (n 1+1) (n 2+1) (n 3+1) (-z)]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.reduceSucc, mul_one, hp,
    Fin.isValue, Fin.reduceSucc, Fin.val_zero, Fin.val_succ,
    Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false, neg_mul, Complex.cpow_neg]
  field_simp [Complex.natCast_add_one_cpow_ne_zero]

end
end Sechstmoment.Source
