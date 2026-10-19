import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Sechstmoment.Zeta.AFE.Four.Specification
import Sechstmoment.Zeta.Gamma.MellinBounds

/-! Actual Gamma bounds on the original AFE line. -/

namespace Sechstmoment.Source
open Complex MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section

@[simp] theorem sourceZetaPoints_re (t : ℝ) (j : Fin 4) :
    (sourceZetaPoints t j).re = 1/2 := by
  fin_cases j <;> norm_num [sourceZetaPoints, criticalLinePoint]

def bblrGammaLineMajorant (α : MomentShifts) (t : ℝ) : ℝ :=
  ∏ j : Fin 4, Real.Gamma ((3/2+ (α j).re)/2) /
    ‖Gamma ((sourceZetaPoints t j+α j)/2)‖

theorem bblrGammaLineMajorant_nonneg (α : MomentShifts) (t : ℝ)
    (hα : ∀ j, -1/2 < (α j).re) : 0 ≤ bblrGammaLineMajorant α t := by
  unfold bblrGammaLineMajorant
  apply Finset.prod_nonneg
  intro j hj
  apply div_nonneg _ (norm_nonneg _)
  exact (Real.Gamma_pos_of_pos (by have := hα j; linarith)).le

theorem bblrGammaQuotient_norm_line_le (α : MomentShifts) (t v : ℝ)
    (hα : ∀ j, -1/2 < (α j).re) :
    ‖bblrGammaQuotient t α (1+(v : ℂ)*I)‖ ≤ bblrGammaLineMajorant α t := by
  unfold bblrGammaQuotient bblrGammaLineMajorant
  rw [norm_prod]
  apply Finset.prod_le_prod₀
  · intro j hj
    exact norm_nonneg _
  · intro j hj
    rw [norm_div]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    have hr : ((sourceZetaPoints t j+α j+(1+(v : ℂ)*I))/2).re =
        (3/2+(α j).re)/2 := by
      simp
      ring
    have hpos : 0 < ((sourceZetaPoints t j+α j+(1+(v : ℂ)*I))/2).re := by
      rw [hr]
      have := hα j
      linarith
    simpa only [hr] using gamma_norm_le_realGamma_re hpos

theorem bblrGammaQuotient_continuous_line (α : MomentShifts) (t : ℝ)
    (hα : ∀ j, -1/2 < (α j).re) :
    Continuous (fun v : ℝ => bblrGammaQuotient t α (1+(v : ℂ)*I)) := by
  unfold bblrGammaQuotient
  apply continuous_finsetProd
  intro j hj
  apply Continuous.div_const
  apply continuous_iff_continuousAt.mpr
  intro v
  apply (Complex.continuousAt_Gamma _ ?_).comp
  · fun_prop
  · intro n hn
    have hr := congrArg Complex.re hn
    have ha := hα j
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp at hr
    linarith

theorem bblrVerticalIntegrand_norm_le (G : ℂ → ℂ) (α : MomentShifts)
    (x t v : ℝ) (hx : 0 < x) (hα : ∀ j, -1/2 < (α j).re) :
    ‖bblrVerticalIntegrand G α x t v‖ ≤
      (bblrGammaLineMajorant α t*Real.pi^(-2 : ℝ)/x)*‖G (1+(v : ℂ)*I)‖ := by
  have hz : 1 ≤ ‖(1 : ℂ)+(v : ℂ)*I‖ := by
    simpa using Complex.abs_re_le_norm ((1 : ℂ)+(v : ℂ)*I)
  have hg : ‖G (1+(v : ℂ)*I)/(1+(v : ℂ)*I)‖ ≤ ‖G (1+(v : ℂ)*I)‖ := by
    rw [norm_div]
    exact div_le_self (norm_nonneg _) hz
  have hπ : ‖(Real.pi : ℂ)^(-2*(1+(v : ℂ)*I))‖ = Real.pi^(-2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    simp
  have hxp : ‖(x : ℂ)^(-(1+(v : ℂ)*I))‖ = 1/x := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp [Real.rpow_neg_one]
  unfold bblrVerticalIntegrand
  dsimp only
  rw [norm_mul, norm_mul, norm_mul, hπ, hxp]
  calc
    _ ≤ ‖G (1+(v : ℂ)*I)‖*bblrGammaLineMajorant α t*
        Real.pi^(-2 : ℝ)*(1/x) := by
      gcongr
      exact bblrGammaQuotient_norm_line_le α t v hα
    _ = _ := by ring

/-- Actual vertical integrability follows from integrability of the fixed
auxiliary function on the AFE line. No asymptotic input is needed. -/
theorem bblrVerticalIntegrand_integrable (G : ℂ → ℂ) (hG : Continuous G)
    (hGI : Integrable (fun v : ℝ => ‖G (1+(v : ℂ)*I)‖))
    (α : MomentShifts) (x t : ℝ) (hx : 0 < x)
    (hα : ∀ j, -1/2 < (α j).re) :
    Integrable (bblrVerticalIntegrand G α x t) := by
  have hc : Continuous (bblrVerticalIntegrand G α x t) := by
    unfold bblrVerticalIntegrand
    dsimp only
    apply Continuous.mul
    · apply Continuous.mul
      · apply Continuous.mul
        · apply Continuous.div
          · exact hG.comp (by fun_prop)
          · fun_prop
          · intro v hv
            have hr := congrArg Complex.re hv
            simp at hr
        · exact bblrGammaQuotient_continuous_line α t hα
      · apply Continuous.const_cpow
        · fun_prop
        · exact Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    · apply Continuous.const_cpow
      · fun_prop
      · exact Or.inl (Complex.ofReal_ne_zero.mpr hx.ne')
  refine (hGI.const_mul (bblrGammaLineMajorant α t*Real.pi^(-2 : ℝ)/x)).mono'
    hc.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun v => bblrVerticalIntegrand_norm_le G α x t v hx hα)

/-- The actual original-line integral decays at least as x^{-1}; the constant
depends on the fixed auxiliary function, shifts and height, not on x. -/
theorem bblrV_norm_le_inv (G : ℂ → ℂ) (hG : Continuous G)
    (hGI : Integrable (fun v : ℝ => ‖G (1+(v : ℂ)*I)‖))
    (α : MomentShifts) (t : ℝ) (hα : ∀ j, -1/2 < (α j).re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → ‖bblrV G α x t‖ ≤ C/x := by
  let J : ℝ := ∫ v : ℝ, ‖G (1+(v : ℂ)*I)‖
  let D : ℝ := bblrGammaLineMajorant α t*Real.pi^(-2 : ℝ)
  have hJ : 0 ≤ J := integral_nonneg (fun _ => norm_nonneg _)
  have hD : 0 ≤ D := mul_nonneg (bblrGammaLineMajorant_nonneg α t hα)
    (Real.rpow_pos_of_pos Real.pi_pos _).le
  refine ⟨D*J/(2*Real.pi), by positivity, ?_⟩
  intro x hx
  have hI := bblrVerticalIntegrand_integrable G hG hGI α x t hx hα
  have hb : ‖∫ v : ℝ, bblrVerticalIntegrand G α x t v‖ ≤ (D/x)*J := by
    calc
      _ ≤ ∫ v : ℝ, ‖bblrVerticalIntegrand G α x t v‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ v : ℝ, (D/x)*‖G (1+(v : ℂ)*I)‖ := by
        apply integral_mono hI.norm (hGI.const_mul (D/x))
        intro v
        exact bblrVerticalIntegrand_norm_le G α x t v hx hα
      _ = _ := integral_const_mul _ _
  change ‖(1/(2*Real.pi) : ℂ)*(∫ v : ℝ, bblrVerticalIntegrand G α x t v)‖ ≤ _
  rw [norm_mul]
  have hc : ‖(1/(2*Real.pi) : ℂ)‖ = 1/(2*Real.pi) := by
    simp [Complex.norm_real, abs_of_pos Real.pi_pos]
  rw [hc]
  calc
    _ ≤ (1/(2*Real.pi))*((D/x)*J) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- A finite product of genuine summable nonnegative one-variable sequences
is summable on the actual function-type index of the fourfold AFE. -/
theorem summable_finitePi_prod_nonneg (n : ℕ) (f : Fin n → ℕ → ℝ)
    (hf0 : ∀ j k, 0 ≤ f j k) (hf : ∀ j, Summable (f j)) :
    Summable (fun k : Fin n → ℕ => ∏ j, f j (k j)) := by
  induction n with
  | zero => exact summable_of_hasFiniteSupport (Set.toFinite _)
  | succ n ih =>
    let e := Fin.insertNthEquiv (fun _ : Fin (n+1) => ℕ) 0
    have ht : Summable (fun k : Fin n → ℕ => ∏ j, f j.succ (k j)) :=
      ih (fun j => f j.succ) (fun j k => hf0 j.succ k) (fun j => hf j.succ)
    have hp := (hf 0).mul_of_nonneg ht (hf0 0)
      (fun k => Finset.prod_nonneg (fun j _ => hf0 j.succ (k j)))
    apply e.summable_iff.mp
    simpa [Function.comp_def, e, Fin.insertNthEquiv, Fin.prod_univ_succ] using hp

theorem positiveQuadProduct_eq_prod (n : Fin 4 → ℕ) :
    positiveQuadProduct n = ∏ j : Fin 4, (n j+1) := by
  simp [positiveQuadProduct, Fin.prod_univ_succ]
  ring

theorem bblrAFE_oscillation_norm_one (n : Fin 4 → ℕ) (t : ℝ) :
    ‖((((n 0+1)*(n 1+1) : ℕ) : ℂ) /
      (((n 2+1)*(n 3+1) : ℕ) : ℂ))^(-(t : ℂ)*I)‖ = 1 := by
  have hr : (0 : ℝ) < (((n 0+1)*(n 1+1) : ℕ) : ℝ) /
      (((n 2+1)*(n 3+1) : ℕ) : ℝ) := by positivity
  have he : ((((n 0+1)*(n 1+1) : ℕ) : ℂ) /
      (((n 2+1)*(n 3+1) : ℕ) : ℂ)) =
    (((((n 0+1)*(n 1+1) : ℕ) : ℝ) /
      (((n 2+1)*(n 3+1) : ℕ) : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [he, Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp

theorem bblrAFESummand_norm_majorant (G : ℂ → ℂ) (α : MomentShifts)
    (t : ℝ) (C : ℝ) (hV : ∀ x : ℝ, 0 < x → ‖bblrV G α x t‖ ≤ C/x)
    (n : Fin 4 → ℕ) :
    ‖bblrAFESummand G α t n‖ ≤
      C*∏ j : Fin 4, 1/(n j+1 : ℝ)^(3/2+(α j).re) := by
  have hn (j : Fin 4) : 0 < (n j+1 : ℝ) := by positivity
  have hx : 0 < (positiveQuadProduct n : ℝ) := by
    unfold positiveQuadProduct
    positivity
  have hden : 0 < ∏ j : Fin 4, (n j+1 : ℝ)^(1/2+(α j).re) :=
    Finset.prod_pos (fun j _ => Real.rpow_pos_of_pos (hn j) _)
  have he : ∏ j : Fin 4, (n j+1 : ℝ)^(3/2+(α j).re) =
      (positiveQuadProduct n : ℝ)*∏ j : Fin 4, (n j+1 : ℝ)^(1/2+(α j).re) := by
    have he' (j : Fin 4) : (n j+1 : ℝ)^(3/2+(α j).re) =
        (n j+1 : ℝ)*(n j+1 : ℝ)^(1/2+(α j).re) := by
      rw [show (3/2 : ℝ)+(α j).re = 1+(1/2+(α j).re) by ring,
        Real.rpow_add (hn j), Real.rpow_one]
    simp_rw [he']
    rw [Finset.prod_mul_distrib, positiveQuadProduct_eq_prod]
    push_cast
    rfl
  unfold bblrAFESummand
  rw [norm_div, norm_mul, bblrAFE_oscillation_norm_one, one_mul, norm_prod]
  have hncp (j : Fin 4) : ‖(n j+1 : ℂ)^(1/2+α j)‖ =
      (n j+1 : ℝ)^(1/2+(α j).re) := by
    rw [show (n j+1 : ℂ) = ((n j+1 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (hn j)]
    congr 1
    simp
  simp_rw [hncp]
  calc
    _ ≤ (C/(positiveQuadProduct n : ℝ))/
        ∏ j : Fin 4, (n j+1 : ℝ)^(1/2+(α j).re) :=
      div_le_div_of_nonneg_right (hV _ hx) hden.le
    _ = C*∏ j : Fin 4, 1/(n j+1 : ℝ)^(3/2+(α j).re) := by
      rw [Finset.prod_div_distrib, Finset.prod_const_one, he]
      ring

/-- Actual fourfold AFE summability, proved using the original vertical line
and four genuine convergent p-series. -/
theorem bblrAFESummand_summable (G : ℂ → ℂ) (hG : Continuous G)
    (hGI : Integrable (fun v : ℝ => ‖G (1+(v : ℂ)*I)‖))
    (α : MomentShifts) (t : ℝ) (hα : ∀ j, -1/2 < (α j).re) :
    Summable (bblrAFESummand G α t) := by
  obtain ⟨C, hC, hV⟩ := bblrV_norm_le_inv G hG hGI α t hα
  have hs : ∀ j : Fin 4, Summable (fun k : ℕ => 1/(k+1 : ℝ)^(3/2+(α j).re)) := by
    intro j
    have hsum := (Real.summable_one_div_nat_add_rpow 1 (3/2+(α j).re)).mpr
      (by have := hα j; linarith)
    have ha (k : ℕ) : |(k : ℝ)+1| = (k : ℝ)+1 := abs_of_pos (by positivity)
    simpa only [ha] using hsum
  have hp := summable_finitePi_prod_nonneg 4
    (fun j k => 1/(k+1 : ℝ)^(3/2+(α j).re))
    (fun j k => by positivity) hs
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => bblrAFESummand_norm_majorant G α t C hV n)
    (hp.mul_left C)

end
end Sechstmoment.Source
