import Mathlib.Tactic
import Sechstmoment.Numerator.U.Reconstruction.RectangularAFEGrouping
import Sechstmoment.Numerator.U.Reconstruction.RectangularAFEReconstruction

/-!
The finite genuine dyadic boxes are inserted into the actual Gamma-based
Mellin integral. Integrability is proved from the original BBLR weight class.
All original and dual boxes remain present in the exact moment identity.
-/

namespace Sechstmoment

open Complex Source MeasureTheory Set
open scoped BigOperators Topology
open Classical

noncomputable section

def rectangularAFEOscillation (t : ℝ) (n : Fin 4 → ℕ) : ℂ :=
  ((((n 0+1)*(n 1+1) : ℕ) : ℂ)/
    (((n 2+1)*(n 3+1) : ℕ) : ℂ))^(-(t : ℂ)*I)

def rectangularAFEMellinKernel (G : ℂ → ℂ) (α : MomentShifts)
    (t : ℝ) (n : Fin 4 → ℕ) (z : ℂ) : ℂ :=
  G z/z*bblrGammaQuotient t α z*(Real.pi : ℂ)^(-2*z)*
    rectangularAFEOscillation t n/
      ∏ j : Fin 4, (n j+1 : ℂ)^(1/2+α j+z)

/-- The actual Mellin factor separates over the four positive integer
variables, using the principal power only on positive real bases. -/
theorem rectangular_AFE_Mellin_powers (α : MomentShifts) (n : Fin 4 → ℕ) (z : ℂ) :
    ((positiveQuadProduct n : ℂ)^(-z))/
      (∏ j : Fin 4, (n j+1 : ℂ)^(1/2+α j)) =
        1/(∏ j : Fin 4, (n j+1 : ℂ)^(1/2+α j+z)) := by
  have hp : (positiveQuadProduct n : ℂ)^(-z) = ∏ j : Fin 4, (n j+1 : ℂ)^(-z) := by
    have h₁ := Complex.natCast_mul_natCast_cpow (n 0+1) (n 1+1) (-z)
    have h₂ := Complex.natCast_mul_natCast_cpow ((n 0+1)*(n 1+1)) (n 2+1) (-z)
    have h₃ := Complex.natCast_mul_natCast_cpow ((n 0+1)*(n 1+1)*(n 2+1)) (n 3+1) (-z)
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h₁ h₂ h₃
    simp only [positiveQuadProduct, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Fin.prod_univ_four]
    rw [h₃, h₂, h₁]
  rw [hp, ← Finset.prod_div_distrib]
  simp only [one_div]
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have hb : (n j+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n j)
  rw [Complex.cpow_neg]
  simp only [Complex.cpow_add _ _ hb, div_eq_mul_inv, mul_inv_rev]

theorem rectangular_AFE_Mellin_kernel_line (G : ℂ → ℂ) (α : MomentShifts)
    (t : ℝ) (n : Fin 4 → ℕ) (v : ℝ) :
    rectangularAFEMellinKernel G α t n (1+(v : ℂ)*I) =
      (rectangularAFEOscillation t n/
        ∏ j : Fin 4, (n j+1 : ℂ)^(1/2+α j))*
          bblrVerticalIntegrand G α (positiveQuadProduct n) t v := by
  have hpow := rectangular_AFE_Mellin_powers α n (1+(v : ℂ)*I)
  dsimp [rectangularAFEMellinKernel, bblrVerticalIntegrand]
  have hpow' := congrArg (fun w : ℂ =>
    (G (1+(v : ℂ)*I)/(1+(v : ℂ)*I)*bblrGammaQuotient t α (1+(v : ℂ)*I)*
      (Real.pi : ℂ)^(-2*(1+(v : ℂ)*I))*rectangularAFEOscillation t n)*w) hpow
  convert hpow'.symm using 1 <;> ring

/-- Each actual separated dyadic Mellin summand is integrable. -/
theorem rectangular_AFE_Mellin_kernel_integrable (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (t : ℝ) (hα : ∀ j, -1/2 < (α j).re)
    (n : Fin 4 → ℕ) : Integrable (fun v : ℝ =>
      rectangularAFEMellinKernel G α t n (1+(v : ℂ)*I)) := by
  have hi := bblrVerticalIntegrand_integrable G (continuousOn_univ.mp hG.1.continuousOn)
    (rectangular_BBLR_weight_vertical_integrable G α hG) α (positiveQuadProduct n) t
    (by simp [positiveQuadProduct]; positivity) hα
  simpa only [rectangular_AFE_Mellin_kernel_line] using hi.const_mul
    (rectangularAFEOscillation t n/∏ j : Fin 4, (n j+1 : ℂ)^(1/2+α j))

theorem rectangular_actual_AFE_summand_Mellin (G : ℂ → ℂ) (α : MomentShifts)
    (t : ℝ) (n : Fin 4 → ℕ) :
    bblrAFESummand G α t n = verticalIntegral 1 (rectangularAFEMellinKernel G α t n) := by
  change rectangularAFEOscillation t n*
      ((1/(2*Real.pi) : ℂ)*∫ v : ℝ, bblrVerticalIntegrand G α (positiveQuadProduct n) t v)/
      (∏ j : Fin 4, (n j+1 : ℂ)^(1/2+α j)) =
    (1/(2*Real.pi) : ℂ)*∫ v : ℝ, rectangularAFEMellinKernel G α t n (1+(v : ℂ)*I)
  simp_rw [rectangular_AFE_Mellin_kernel_line]
  rw [integral_const_mul]
  ring

/-- The actual finite dyadic box is moved through its defining vertical
integral, including an arbitrary exact diagonal or signed-gap selection. -/
theorem rectangular_actual_AFE_box_Mellin (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (t : ℝ) (hα : ∀ j, -1/2 < (α j).re)
    (k : Fin 4 → ℕ) (P : (Fin 4 → ℕ) → Prop) :
    (∑ n ∈ rectangularAFEDyadicBox k, if P n then bblrAFESummand G α t n else 0) =
      verticalIntegral 1 (fun z => ∑ n ∈ rectangularAFEDyadicBox k,
        if P n then rectangularAFEMellinKernel G α t n z else 0) := by
  have hi : ∀ n ∈ rectangularAFEDyadicBox k, Integrable (fun v : ℝ =>
      if P n then rectangularAFEMellinKernel G α t n (1+(v : ℂ)*I) else 0) := by
    intro n hn
    by_cases h : P n
    · simpa only [h, ite_true] using rectangular_AFE_Mellin_kernel_integrable G α hG t hα n
    · simp only [h, ite_false]; exact integrable_zero _ _ _
  unfold verticalIntegral
  dsimp only
  simp only [Complex.ofReal_one]
  rw [integral_finsetSum _ hi, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h : P n
  · simp only [h, ite_true]
    exact rectangular_actual_AFE_summand_Mellin G α t n
  · simp [h]

end
end Sechstmoment
