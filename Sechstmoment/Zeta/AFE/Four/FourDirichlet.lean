import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic
import Sechstmoment.Zeta.AFE.Four.Factorization
import Sechstmoment.Zeta.AFE.Four.Integrability
import Sechstmoment.Zeta.AFE.Four.Kernel


namespace Sechstmoment.Source

open Complex Real MeasureTheory Filter
open scoped BigOperators
noncomputable section

theorem fixedAFE_finitePi_norm_summable (m : ℕ) (f : Fin m → ℕ → ℂ)
    (hf : ∀ j, Summable (fun k => ‖f j k‖)) :
    Summable (fun n : Fin m → ℕ => ‖∏ j, f j (n j)‖) := by
  induction m with
  | zero => exact summable_of_hasFiniteSupport (Set.toFinite _)
  | succ m ih =>
    let e := Fin.insertNthEquiv (fun _ : Fin (m+1) => ℕ) 0
    have ht := ih (fun j k => f j.succ k) (fun j => hf j.succ)
    have hp := (hf 0).mul_norm ht
    apply e.summable_iff.mp
    simpa [Function.comp_def, e, Fin.insertNthEquiv, Fin.prod_univ_succ] using hp

theorem fixedAFE_finitePi_tsum_prod (m : ℕ) (f : Fin m → ℕ → ℂ)
    (hf : ∀ j, Summable (fun k => ‖f j k‖)) :
    (∑' n : Fin m → ℕ, ∏ j, f j (n j)) = ∏ j, ∑' k, f j k := by
  induction m with
  | zero => simp
  | succ m ih =>
    let e := Fin.insertNthEquiv (fun _ : Fin (m+1) => ℕ) 0
    rw [← e.tsum_eq (fun n : Fin (m+1) → ℕ => ∏ j, f j (n j))]
    simp only [e, Fin.insertNthEquiv_apply, Fin.insertNth_zero',
      Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [← tsum_mul_tsum_of_summable_norm (hf 0)
      (fixedAFE_finitePi_norm_summable m (fun j k => f j.succ k)
        (fun j => hf j.succ)), ih (fun j k => f j.succ k) (fun j => hf j.succ)]

def fixedAFEFourDirichletKernel (s : Fin 4 → ℂ) (n : Fin 4 → ℕ) (v : ℝ) : ℂ :=
  ∏ j, 1/(n j+1 : ℂ)^(s j+(v : ℂ)*I)

def fixedAFEFourDirichletMass (s : Fin 4 → ℂ) (n : Fin 4 → ℕ) : ℝ :=
  ∏ j, (n j+1 : ℝ)^(-(s j).re)

theorem fixedAFEFourDirichletKernel_norm (s : Fin 4 → ℂ)
    (n : Fin 4 → ℕ) (v : ℝ) :
    ‖fixedAFEFourDirichletKernel s n v‖ = fixedAFEFourDirichletMass s n := by
  unfold fixedAFEFourDirichletKernel fixedAFEFourDirichletMass
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro j hj
  rw [norm_div, norm_one,
    show (n j+1 : ℂ) = ((n j+1 : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im,
    I_im, zero_mul, sub_self, add_zero]
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ n j+1)]
  simp only [one_div]

theorem fixedAFE_oneDirichlet_norm_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ‖1/(n+1 : ℂ)^s‖) := by
  have hp := (Real.summable_one_div_nat_add_rpow 1 s.re).mpr hs
  convert hp using 1
  funext n
  rw [norm_div, norm_one,
    show (n+1 : ℂ) = ((n+1 : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
    abs_of_pos (by positivity : (0 : ℝ) < n+1)]

theorem fixedAFEFourDirichletMass_summable {s : Fin 4 → ℂ}
    (hs : ∀ j, 1 < (s j).re) : Summable (fixedAFEFourDirichletMass s) := by
  have hp := fixedAFE_finitePi_norm_summable 4
    (fun j n => 1/(n+1 : ℂ)^(s j))
    (fun j => fixedAFE_oneDirichlet_norm_summable (hs j))
  convert hp using 1
  funext n
  symm
  simpa only [fixedAFEFourDirichletKernel, ofReal_zero, zero_mul, add_zero] using
    fixedAFEFourDirichletKernel_norm s n 0

theorem fixedAFEFourDirichletKernel_tsum {s : Fin 4 → ℂ}
    (hs : ∀ j, 1 < (s j).re) (v : ℝ) :
    (∑' n : Fin 4 → ℕ, fixedAFEFourDirichletKernel s n v) =
      ∏ j, riemannZeta (s j+(v : ℂ)*I) := by
  have hsr (j : Fin 4) : 1 < (s j+(v : ℂ)*I).re := by simpa using hs j
  unfold fixedAFEFourDirichletKernel
  rw [fixedAFE_finitePi_tsum_prod 4 _
    (fun j => fixedAFE_oneDirichlet_norm_summable (hsr j))]
  apply Finset.prod_congr rfl
  intro j hj
  exact (zeta_eq_tsum_one_div_nat_add_one_cpow (hsr j)).symm

theorem fixedAFEFourDirichletKernel_continuous (s : Fin 4 → ℂ)
    (n : Fin 4 → ℕ) : Continuous (fixedAFEFourDirichletKernel s n) := by
  unfold fixedAFEFourDirichletKernel
  apply continuous_finsetProd
  intro j hj
  have hn : (n j+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n j)
  exact continuous_const.div
    (Continuous.const_cpow (by fun_prop) (Or.inl hn))
    (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl hn))

theorem fixedAFEFourDirichlet_integral_interchange {s : Fin 4 → ℂ}
    (hs : ∀ j, 1 < (s j).re) (F : ℝ → ℂ) (hF : Integrable F) :
    (∑' n : Fin 4 → ℕ, ∫ v : ℝ, F v*fixedAFEFourDirichletKernel s n v) =
      ∫ v : ℝ, F v*∏ j, riemannZeta (s j+(v : ℂ)*I) := by
  have hFI (n : Fin 4 → ℕ) :
      Integrable (fun v => F v*fixedAFEFourDirichletKernel s n v) := by
    apply (hF.norm.mul_const (fixedAFEFourDirichletMass s n)).mono'
      (hF.aestronglyMeasurable.mul
        (fixedAFEFourDirichletKernel_continuous s n).aestronglyMeasurable)
    exact Eventually.of_forall fun v => by
      change ‖F v*fixedAFEFourDirichletKernel s n v‖ ≤
        ‖F v‖*fixedAFEFourDirichletMass s n
      rw [norm_mul, fixedAFEFourDirichletKernel_norm]
  have he (n : Fin 4 → ℕ) :
      (∫ v : ℝ, ‖F v*fixedAFEFourDirichletKernel s n v‖) =
        (∫ v : ℝ, ‖F v‖)*fixedAFEFourDirichletMass s n := by
    simp_rw [norm_mul, fixedAFEFourDirichletKernel_norm]
    exact integral_mul_const _ _
  rw [integral_tsum_of_summable_integral_norm hFI (by
    simp_rw [he]
    exact (fixedAFEFourDirichletMass_summable hs).mul_left _)]
  apply integral_congr_ae
  exact Eventually.of_forall fun v => by
    change (∑' n : Fin 4 → ℕ, F v*fixedAFEFourDirichletKernel s n v) =
      F v*∏ j, riemannZeta (s j+(v : ℂ)*I)
    rw [tsum_mul_left, fixedAFEFourDirichletKernel_tsum hs]

def fixedAFEWeightOnLine (G : ℂ → ℂ) (α : MomentShifts) (t v : ℝ) : ℂ :=
  let z : ℂ := 1+(v : ℂ)*I
  G z/z*bblrGammaQuotient t α z*(Real.pi : ℂ)^(-2*z)

theorem fixedAFE_entireWeight_line_norm_integrable (G : ℂ → ℂ)
    (hG : BBLREntireWeight G (fun _ => 0)) :
    Integrable (fun v : ℝ => ‖G (1+(v : ℂ)*I)‖) := by
  obtain ⟨C, hC, hbound⟩ := hG.2.2.2 1 (by norm_num) 2
  have hc : Continuous (fun v : ℝ => G (1+(v : ℂ)*I)) :=
    hG.1.continuous.comp (by fun_prop)
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.norm.aestronglyMeasurable
  exact Eventually.of_forall fun v => by
    rw [norm_norm]
    have hb : ‖G (1+(v : ℂ)*I)‖*(1+|v|)^2 ≤ C := by
      simpa using hbound (1+(v : ℂ)*I) (by simp)
    have hquad : 1+v^2 ≤ (1+|v|)^2 := by
      nlinarith [abs_nonneg v, sq_abs v]
    have hm := (mul_le_mul_of_nonneg_left hquad
      (norm_nonneg (G (1+(v : ℂ)*I)))).trans hb
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < 1+v^2)).mpr hm

theorem fixedAFEWeightOnLine_integrable (G : ℂ → ℂ)
    (hG : BBLREntireWeight G (fun _ => 0))
    (α : MomentShifts) (t : ℝ) (hα : ∀ j, -1/2 < (α j).re) :
    Integrable (fixedAFEWeightOnLine G α t) := by
  have hI := bblrVerticalIntegrand_integrable G hG.1.continuous
    (fixedAFE_entireWeight_line_norm_integrable G hG) α 1 t (by norm_num) hα
  have he : fixedAFEWeightOnLine G α t = bblrVerticalIntegrand G α 1 t := by
    funext v
    simp [fixedAFEWeightOnLine, bblrVerticalIntegrand]
  rw [he]
  exact hI

theorem fixedAFE_AFESummand_summable_of_entireWeight
    (G : ℂ → ℂ) (hG : BBLREntireWeight G (fun _ => 0))
    (α : MomentShifts) (t : ℝ) (hα : ∀ j, -1/2 < (α j).re) :
    Summable (bblrAFESummand G α t) :=
  bblrAFESummand_summable G hG.1.continuous
    (fixedAFE_entireWeight_line_norm_integrable G hG) α t hα

theorem fixedAFE_AFESummand_eq_integral (G : ℂ → ℂ) (α : MomentShifts)
    (t : ℝ) (n : Fin 4 → ℕ) :
    bblrAFESummand G α t n = (1/(2*Real.pi) : ℂ)*
      ∫ v : ℝ, fixedAFEWeightOnLine G α t v*
        fixedAFEFourDirichletKernel (fun j => sourceZetaPoints t j+α j+1) n v := by
  have hpoint (v : ℝ) : fixedAFEWeightOnLine G α t v*
      fixedAFEFourDirichletKernel (fun j => sourceZetaPoints t j+α j+1) n v =
      (((((n 0+1)*(n 1+1) : ℕ) : ℂ) /
        (((n 2+1)*(n 3+1) : ℕ) : ℂ))^(-(t : ℂ)*I) /
        ∏ j : Fin 4, (n j+1 : ℂ)^(1/2+α j)) *
        bblrVerticalIntegrand G α (positiveQuadProduct n) t v := by
    unfold fixedAFEFourDirichletKernel
    have hp := fixedAFEFourDirichlet_factorization n t α (1+(v : ℂ)*I)
    simp only [add_assoc] at hp ⊢
    rw [hp]
    unfold fixedAFEWeightOnLine bblrVerticalIntegrand
    dsimp only
    push_cast
    ring
  simp_rw [hpoint]
  rw [integral_const_mul]
  unfold bblrAFESummand bblrV verticalIntegral
  simp only [bblrVerticalIntegrand, Complex.ofReal_one]
  ring

theorem fixedAFE_AFESum_eq_right_integral (G : ℂ → ℂ) (α : MomentShifts)
    (t : ℝ) (hα : ∀ j, -1/2 < (α j).re)
    (hF : Integrable (fixedAFEWeightOnLine G α t)) :
    bblrAFESum G α t = verticalIntegral 1 (fun z =>
      G z/z*bblrGammaQuotient t α z*(Real.pi : ℂ)^(-2*z)*
        ∏ j : Fin 4, riemannZeta (sourceZetaPoints t j+α j+z)) := by
  have hs (j : Fin 4) : 1 < (sourceZetaPoints t j+α j+1).re := by
    have hj : (sourceZetaPoints t j).re = 1/2 := by
      fin_cases j <;> norm_num [sourceZetaPoints, criticalLinePoint]
    simp only [add_re, one_re, hj]
    have := hα j
    linarith
  unfold bblrAFESum
  simp_rw [fixedAFE_AFESummand_eq_integral]
  rw [tsum_mul_left, fixedAFEFourDirichlet_integral_interchange hs _ hF]
  unfold verticalIntegral fixedAFEWeightOnLine
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun v => by
    simp only [add_assoc, Complex.ofReal_one]

theorem fixedAFE_AFESum_eq_right_integral_of_entireWeight
    (G : ℂ → ℂ) (hG : BBLREntireWeight G (fun _ => 0))
    (α : MomentShifts) (t : ℝ) (hα : ∀ j, -1/2 < (α j).re) :
    bblrAFESum G α t = verticalIntegral 1 (fun z =>
      G z/z*bblrGammaQuotient t α z*(Real.pi : ℂ)^(-2*z)*
        ∏ j : Fin 4, riemannZeta (sourceZetaPoints t j+α j+z)) :=
  fixedAFE_AFESum_eq_right_integral G α t hα
    (fixedAFEWeightOnLine_integrable G hG α t hα)

theorem fixedAFE_AFESum_eq_completed_right_integral
    (G : ℂ → ℂ) (hG : BBLREntireWeight G (fun _ => 0))
    (α : MomentShifts) (t : ℝ) (hα : ∀ j, -1/2 < (α j).re) :
    bblrAFESum G α t = verticalIntegral 1
      (fun z => fixedAFECompletedKernel G α t z/z) := by
  rw [fixedAFE_AFESum_eq_right_integral_of_entireWeight G hG α t hα]
  unfold verticalIntegral
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun v => by
    symm
    apply fixedAFECompletedKernel_div_eq_gamma_zeta
    intro j
    have hj := sourceZetaPoints_re t j
    have ha := hα j
    simp only [fixedAFEShiftedPoint, Complex.add_re,
      Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, zero_mul, sub_self, add_zero, hj]
    linarith

end
end Sechstmoment.Source
