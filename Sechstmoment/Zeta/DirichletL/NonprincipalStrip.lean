import Mathlib.Analysis.Complex.PhragmenLindelof
import Sechstmoment.Zeta.DirichletL.CharacterFourthMoment
import Sechstmoment.Zeta.DirichletL.NonprincipalStripGrowth


namespace Sechstmoment.Source
open Complex Real Filter Set
open scoped Topology BigOperators
noncomputable section

def nonprincipalPolynomialAux {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  (χ.LFunction s)^4/(s+2)^20

private theorem nonprincipal_shift_norm_geometry {s : ℂ} (hs : 1/2 ≤ s.re) :
    1 ≤ ‖s+2‖ ∧ 1+|s.im| ≤ 2*‖s+2‖ := by
  have hre := Complex.re_le_norm (s+2)
  have him := Complex.abs_im_le_norm (s+2)
  simp only [add_re,re_ofNat] at hre
  simp only [add_im,im_ofNat,add_zero] at him
  constructor <;> linarith

private theorem real_exp_fourth (y : ℝ) : (Real.exp y)^4 = Real.exp (4*y) := by
  calc
    _ = (Real.exp y*Real.exp y)*(Real.exp y*Real.exp y) := by ring
    _ = Real.exp (y+y)*Real.exp (y+y) :=
      congrArg₂ (fun a b : ℝ => a*b) (Real.exp_add y y).symm (Real.exp_add y y).symm
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem nonprincipalDirichlet_polynomial_strip {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Icc (1/2:ℝ) (3/2) →
      ‖χ.LFunction s‖ ≤ C*(1+|s.im|)^20 := by
  classical
  obtain ⟨A,hA,HA⟩ := allDirichlet_fourthMoment (ε := 1) (by norm_num)
  let Z := zetaDirichletMajorant (3/2)
  let K := (2:ℝ)^20*A*(q:ℝ)^2+Z^4+1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hnorm (s : ℂ) :
      ‖nonprincipalPolynomialAux χ s‖ = ‖χ.LFunction s‖^4/‖s+2‖^20 := by
    rw [nonprincipalPolynomialAux,norm_div,norm_pow,norm_pow]
  have hleft {s : ℂ} (hs : s.re = 1/2) : ‖nonprincipalPolynomialAux χ s‖ ≤ K := by
    have hden := (nonprincipal_shift_norm_geometry hs.ge).1
    have hheight := (nonprincipal_shift_norm_geometry hs.ge).2
    have hsingle : ‖χ.LFunction s‖^4 ≤ A*(q:ℝ)^2*(1+|s.im|)^20 := by
      have H := HA q inferInstance s (by rw [hs]; norm_num)
      norm_num only [show (1:ℝ)+1 = 2 by norm_num,Real.rpow_two] at H
      exact (Finset.single_le_sum (fun ψ _ => by positivity) (Finset.mem_univ χ)).trans H
    rw [hnorm,div_le_iff₀ (by positivity : 0 < ‖s+2‖^20)]
    calc
      _ ≤ A*(q:ℝ)^2*(1+|s.im|)^20 := hsingle
      _ ≤ A*(q:ℝ)^2*(2*‖s+2‖)^20 := by gcongr
      _ = ((2:ℝ)^20*A*(q:ℝ)^2)*‖s+2‖^20 := by rw [mul_pow]; ring
      _ ≤ K*‖s+2‖^20 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp only [K]
        have hz : 0 ≤ Z^4 := by positivity
        linarith
  have hright {s : ℂ} (hs : s.re = 3/2) : ‖nonprincipalPolynomialAux χ s‖ ≤ K := by
    have hden := (nonprincipal_shift_norm_geometry (by linarith : 1/2 ≤ s.re)).1
    rw [hnorm,div_le_iff₀ (by positivity : 0 < ‖s+2‖^20)]
    have hL : ‖χ.LFunction s‖ ≤ Z := dirichletL_norm_le_dirichlet χ (by norm_num) hs.ge
    have hp : 1 ≤ ‖s+2‖^20 := one_le_pow₀ hden
    calc
      _ ≤ Z^4 := by gcongr
      _ ≤ K := by
        dsimp only [K]
        have hz : 0 ≤ (2:ℝ)^20*A*(q:ℝ)^2 := by positivity
        linarith
      _ ≤ _ := le_mul_of_one_le_right hK.le hp
  have hdiff : DiffContOnCl ℂ (nonprincipalPolynomialAux χ)
      (Complex.re ⁻¹' Ioo (1/2:ℝ) (3/2)) := by
    have hcl : closure (Complex.re ⁻¹' Ioo (1/2:ℝ) (3/2)) ⊆
        Complex.re ⁻¹' Icc (1/2:ℝ) (3/2) :=
      closure_minimal (fun _ h => ⟨h.1.le,h.2.le⟩)
        (isClosed_Icc.preimage Complex.continuous_re)
    apply DifferentiableOn.diffContOnCl
    intro s hs
    have hn : s+2 ≠ 0 := by
      intro he
      have H := (nonprincipal_shift_norm_geometry (hcl hs).1).1
      rw [he,norm_zero] at H
      norm_num at H
    exact (((DirichletCharacter.differentiable_LFunction hχ s).pow 4).div
      ((differentiableAt_id.add_const 2).pow 20) (pow_ne_zero 20 hn)).differentiableWithinAt
  obtain ⟨B,hB,HB⟩ := nonprincipalDirichlet_exponential_strip χ hχ
  have hO : nonprincipalPolynomialAux χ =O[comap (abs ∘ Complex.im) atTop ⊓
      𝓟 (Complex.re ⁻¹' Ioo (1/2:ℝ) (3/2))]
      (fun s : ℂ => Real.exp (4*Real.pi*Real.exp ((1/2)*|s.im|))) := by
    apply Asymptotics.IsBigO.of_bound (B^4)
    simp only [eventually_inf_principal,eventually_comap,Function.comp_apply]
    filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy s hsy hs
    have ht : 1 ≤ |s.im| := hsy ▸ hy
    have hd : 1 ≤ ‖s+2‖^20 := one_le_pow₀ (nonprincipal_shift_norm_geometry hs.1.le).1
    have he : Real.exp (2*Real.pi*|s.im|) ≤
        Real.exp (4*Real.pi*Real.exp ((1/2)*|s.im|)) := by
      apply Real.exp_le_exp.mpr
      have H : (1/2)*|s.im| ≤ Real.exp ((1/2)*|s.im|) := by
        linarith [Real.add_one_le_exp ((1/2)*|s.im|)]
      nlinarith [mul_le_mul_of_nonneg_left H (show 0 ≤ 4*Real.pi by positivity)]
    calc
      _ ≤ ‖χ.LFunction s‖^4 := by
        rw [hnorm]
        exact div_le_self (by positivity) hd
      _ ≤ (B*Real.exp (Real.pi*|s.im|/2))^4 := by
        gcongr
        exact HB s ⟨hs.1.le,hs.2.le⟩ ht
      _ = B^4*Real.exp (2*Real.pi*|s.im|) := by
        rw [mul_pow,real_exp_fourth,
          show 4*(Real.pi*|s.im|/2) = 2*Real.pi*|s.im| by ring]
      _ ≤ _ := by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        exact mul_le_mul_of_nonneg_left he (by positivity)
  have haux (s : ℂ) (hs : s.re ∈ Icc (1/2:ℝ) (3/2)) :
      ‖nonprincipalPolynomialAux χ s‖ ≤ K :=
    PhragmenLindelof.vertical_strip hdiff
      ⟨1/2,by norm_num; linarith [Real.two_le_pi],4*Real.pi,hO⟩
      (fun _ h => hleft h) (fun _ h => hright h) hs.1 hs.2
  refine ⟨1+K*4^20,by positivity,?_⟩
  intro s hs
  have H := haux s hs
  have hden := (nonprincipal_shift_norm_geometry hs.1).1
  rw [hnorm,div_le_iff₀ (by positivity : 0 < ‖s+2‖^20)] at H
  have hheight : ‖s+2‖ ≤ 4*(1+|s.im|) := by
    have Hb := Complex.norm_le_abs_re_add_abs_im (s+2)
    simp only [add_re,re_ofNat,add_im,im_ofNat,add_zero] at Hb
    rw [abs_of_nonneg (by linarith [hs.1])] at Hb
    linarith [hs.2,abs_nonneg s.im]
  have hcoarse : ‖χ.LFunction s‖ ≤ 1+‖χ.LFunction s‖^4 := by
    by_cases hh : ‖χ.LFunction s‖ ≤ 1
    · exact hh.trans (by linarith [pow_nonneg (norm_nonneg (χ.LFunction s)) 4])
    · have Hp := pow_le_pow_right₀ (le_of_not_ge hh) (show (1:ℕ) ≤ 4 by decide)
      simp only [pow_one] at Hp
      linarith
  have hone : 1 ≤ (1+|s.im|)^20 := one_le_pow₀ (by linarith [abs_nonneg s.im])
  calc
    _ ≤ 1+‖χ.LFunction s‖^4 := hcoarse
    _ ≤ 1+K*(4*(1+|s.im|))^20 :=
      add_le_add le_rfl (H.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hheight 20) hK.le))
    _ ≤ _ := by rw [mul_pow]; nlinarith

end
end Sechstmoment.Source
