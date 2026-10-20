import SixthMoment.Numerator.Polar.PureHorizontal
import SixthMoment.Numerator.U.ZeroModes.Contour.PoleRemoval


namespace SixthMoment
open Complex Real Source Set
open scoped BigOperators
open Classical
noncomputable section
set_option maxHeartbeats 0

def a03ZeroModeMainRootArgument (T : ℝ) (σ : MomentShifts) (j : Fin 2) (z : ℂ) : ℂ :=
  if j=0 then 1+2*(z-a03ZeroModeMainPoleRoot T σ j)
    else 1-2*(z-a03ZeroModeMainPoleRoot T σ j)

def a03ZeroModeMainRootZetaProduct (T : ℝ) (σ : MomentShifts) (z : ℂ) : ℂ :=
  ∏ j : Fin 2, riemannZeta (a03ZeroModeMainRootArgument T σ j z)

theorem a03ZeroModeMainRootZetaProduct_eq (T : ℝ) (σ : MomentShifts) (z : ℂ) :
    a03ZeroModeMainRootZetaProduct T σ z =
      riemannZeta (1+rawMomentShifts T σ 0+rawMomentShifts T σ 2+2*z)*
        riemannZeta (1-rawMomentShifts T σ 1-rawMomentShifts T σ 3-2*z) := by
  simp only [a03ZeroModeMainRootZetaProduct,Fin.prod_univ_two]
  change riemannZeta (1+2*(z-a03ZeroModeMainPoleRoot T σ 0))*
    riemannZeta (1-2*(z-a03ZeroModeMainPoleRoot T σ 1)) = _
  rw [a03ZeroModeMainPoleRoot_zero,a03ZeroModeMainPoleRoot_one]
  congr 2 <;> ring

theorem a03ZeroModeMainRootArgument_norm_distance (T : ℝ) (σ : MomentShifts)
    (j : Fin 2) (z : ℂ) :
    ‖1-a03ZeroModeMainRootArgument T σ j z‖=2*‖z-a03ZeroModeMainPoleRoot T σ j‖ := by
  fin_cases j
  · change ‖1-(1+2*(z-a03ZeroModeMainPoleRoot T σ 0))‖ = _
    rw [show 1-(1+2*(z-a03ZeroModeMainPoleRoot T σ 0))=
      -(2*(z-a03ZeroModeMainPoleRoot T σ 0)) by ring,norm_neg,norm_mul]
    norm_num
  · change ‖1-(1-2*(z-a03ZeroModeMainPoleRoot T σ 1))‖ = _
    rw [show 1-(1-2*(z-a03ZeroModeMainPoleRoot T σ 1))=
      2*(z-a03ZeroModeMainPoleRoot T σ 1) by ring,norm_mul]
    norm_num

theorem a03ZeroModeMainRootArgument_im_abs (T : ℝ) (σ : MomentShifts)
    (j : Fin 2) (z : ℂ) :
    |(a03ZeroModeMainRootArgument T σ j z).im|=
      2*|z.im-(a03ZeroModeMainPoleRoot T σ j).im| := by
  fin_cases j <;> simp [a03ZeroModeMainRootArgument,abs_mul]

theorem a03ZeroModeMainRootArgument_re_lower {T δ : ℝ} (σ : MomentShifts)
    (hδ : 0<δ) (hδ1 : δ<1/4)
    (hρ : ∀ j : Fin 2, ‖a03ZeroModeMainPoleRoot T σ j‖≤δ/4)
    {z : ℂ} (hz : |z.re|≤δ) (j : Fin 2) :
    (1/4:ℝ)≤(a03ZeroModeMainRootArgument T σ j z).re := by
  have hr (j : Fin 2) : |(a03ZeroModeMainPoleRoot T σ j).re|≤δ/4 :=
    (Complex.abs_re_le_norm (a03ZeroModeMainPoleRoot T σ j)).trans (hρ j)
  fin_cases j <;> simp [a03ZeroModeMainRootArgument] <;>
    linarith [(abs_le.mp hz).1,(abs_le.mp hz).2,(abs_le.mp (hr 0)).1,
      (abs_le.mp (hr 0)).2,(abs_le.mp (hr 1)).1,(abs_le.mp (hr 1)).2]

theorem a03ZeroModeMainRootArgument_line_separation {T δ c : ℝ}
    (σ : MomentShifts) (hδ : 0<δ)
    (hρ : ∀ j : Fin 2, ‖a03ZeroModeMainPoleRoot T σ j‖≤δ/4)
    (hc : |c|=δ) (v : ℝ) (j : Fin 2) :
    δ≤‖1-a03ZeroModeMainRootArgument T σ j ((c:ℂ)+(v:ℂ)*I)‖ := by
  rw [a03ZeroModeMainRootArgument_norm_distance]
  have hr := (Complex.abs_re_le_norm (a03ZeroModeMainPoleRoot T σ j)).trans (hρ j)
  have ht : |c|≤|c-(a03ZeroModeMainPoleRoot T σ j).re|+
      |(a03ZeroModeMainPoleRoot T σ j).re| := by
    simpa using abs_add_le (c-(a03ZeroModeMainPoleRoot T σ j).re)
      (a03ZeroModeMainPoleRoot T σ j).re
  have hn := Complex.abs_re_le_norm
    (((c:ℂ)+(v:ℂ)*I)-a03ZeroModeMainPoleRoot T σ j)
  simp only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,
    zero_mul,sub_zero,add_zero] at hn
  rw [hc] at ht
  linarith

theorem a03ZeroModeMainRootArgument_horizontal_separation {T δ c : ℝ}
    (σ : MomentShifts) (hδ : 0<δ) (hδ1 : δ<1/4)
    (hρ : ∀ j : Fin 2, ‖a03ZeroModeMainPoleRoot T σ j‖≤δ/4)
    {v : ℝ} (hv : 1≤|v|) (j : Fin 2) :
    δ≤‖1-a03ZeroModeMainRootArgument T σ j ((c:ℂ)+(v:ℂ)*I)‖ := by
  rw [a03ZeroModeMainRootArgument_norm_distance]
  have hr := (Complex.abs_im_le_norm (a03ZeroModeMainPoleRoot T σ j)).trans (hρ j)
  have ht : |v|≤|v-(a03ZeroModeMainPoleRoot T σ j).im|+
      |(a03ZeroModeMainPoleRoot T σ j).im| := by
    simpa using abs_add_le (v-(a03ZeroModeMainPoleRoot T σ j).im)
      (a03ZeroModeMainPoleRoot T σ j).im
  have hn := Complex.abs_im_le_norm
    (((c:ℂ)+(v:ℂ)*I)-a03ZeroModeMainPoleRoot T σ j)
  simp only [sub_im,add_im,ofReal_im,mul_im,ofReal_re,I_re,I_im,mul_zero,
    mul_one,add_zero,zero_add] at hn
  linarith

theorem a03ZeroModeMainRootZetaProduct_strip_bound {T δ : ℝ}
    (σ : MomentShifts) (hδ : 0<δ) (hδ1 : δ<1/4)
    (hρ : ∀ j : Fin 2, ‖a03ZeroModeMainPoleRoot T σ j‖≤δ/4) :
    ∃ D : ℝ, 0≤D ∧ ∀ z : ℂ, |z.re|≤δ →
      (∀ j : Fin 2, δ≤‖1-a03ZeroModeMainRootArgument T σ j z‖) →
      ‖a03ZeroModeMainRootZetaProduct T σ z‖≤D*Real.exp (2*Real.pi*|z.im|) := by
  obtain ⟨C,hC,hZ⟩ := riemannZeta_norm_le_exp_halfPlane
    (by norm_num : (0:ℝ)<1/4) hδ
  refine ⟨C^2*Real.exp (2*Real.pi*(δ/4)),by positivity,?_⟩
  intro z hz hsep
  have hf (j : Fin 2) : ‖riemannZeta (a03ZeroModeMainRootArgument T σ j z)‖≤
      C*Real.exp (Real.pi*(|z.im|+δ/4)) := by
    have him : |(a03ZeroModeMainRootArgument T σ j z).im|≤2*(|z.im|+δ/4) := by
      rw [a03ZeroModeMainRootArgument_im_abs]
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
      exact (abs_sub _ _).trans (add_le_add le_rfl
        ((Complex.abs_im_le_norm _).trans (hρ j)))
    exact (hZ _ (a03ZeroModeMainRootArgument_re_lower σ hδ hδ1 hρ hz j) (hsep j)).trans
      (by gcongr; nlinarith [Real.pi_pos])
  unfold a03ZeroModeMainRootZetaProduct
  calc
    _ ≤ ∏ j : Fin 2, ‖riemannZeta (a03ZeroModeMainRootArgument T σ j z)‖ :=
      Finset.norm_prod_le _ _
    _ ≤ ∏ _j : Fin 2, C*Real.exp (Real.pi*(|z.im|+δ/4)) :=
      Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => hf j)
    _ = _ := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
      rw [mul_pow,←Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [mul_assoc,←Real.exp_add]
      congr 2
      ring

end
end SixthMoment
