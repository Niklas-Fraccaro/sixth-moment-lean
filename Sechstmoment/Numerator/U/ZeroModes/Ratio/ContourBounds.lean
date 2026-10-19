import Sechstmoment.Numerator.U.Replacement.GaussianCoefficientGrowth
import Sechstmoment.Numerator.U.Replacement.GaussianTail
import Sechstmoment.Numerator.U.ZeroModes.Ratio.ContourGeometry
import Sechstmoment.Zeta.Bounds.MellinZetaHalfPlaneGrowth

/-! Actual Gaussian and arithmetic majorants for the ratio-u/v contours.
The eta cost is a genuine subpower bound and every zeta denominator is
controlled by its actual Möbius series. -/

namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 0

def a03ZeroModeRatioGaussianConstant (α : MomentShifts) (R : ℝ) : ℝ :=
  Real.exp (R^2)*(R+1)^4*
    (1+‖((a03ZeroModeRatioRoot α 0)^2)⁻¹‖)*
      (1+‖((a03ZeroModeRatioRoot α 1)^2)⁻¹‖)

theorem a03ZeroModeRatioGaussianConstant_nonneg (α : MomentShifts) (R : ℝ) :
    0≤a03ZeroModeRatioGaussianConstant α R := by
  unfold a03ZeroModeRatioGaussianConstant
  positivity

theorem a03ZeroModeRatioWeight_gaussian_bound (α : MomentShifts)
    {R : ℝ} (hR : 0≤R) {z : ℂ} (hz : |z.re|≤R) :
    ‖a03ZeroModeRatioWeight α z‖≤a03ZeroModeRatioGaussianConstant α R*
      (1+|z.im|)^4*Real.exp (-z.im^2) := by
  have hn : ‖z‖≤(R+1)*(1+|z.im|) := by
    have h := Complex.norm_le_abs_re_add_abs_im z
    nlinarith [abs_nonneg z.im]
  have hf (j : Fin 2) : ‖1-z^2/(a03ZeroModeRatioRoot α j)^2‖≤
      (1+‖((a03ZeroModeRatioRoot α j)^2)⁻¹‖)*(R+1)^2*(1+|z.im|)^2 := by
    have hs : 1≤(R+1)^2*(1+|z.im|)^2 := by
      have hr := one_le_pow₀ (show (1:ℝ)≤R+1 by linarith) (n := 2)
      have hi := one_le_pow₀ (show (1:ℝ)≤1+|z.im| by linarith [abs_nonneg z.im]) (n := 2)
      nlinarith
    calc
      _ ≤ 1+‖z‖^2*‖((a03ZeroModeRatioRoot α j)^2)⁻¹‖ := by
        apply (norm_sub_le (1:ℂ) (z^2/(a03ZeroModeRatioRoot α j)^2)).trans_eq
        rw [norm_one,norm_div,norm_pow,norm_inv,norm_pow,div_eq_mul_inv]
      _ ≤ 1+((R+1)*(1+|z.im|))^2*‖((a03ZeroModeRatioRoot α j)^2)⁻¹‖ := by gcongr
      _ ≤ _ := by rw [mul_pow]; nlinarith [norm_nonneg (((a03ZeroModeRatioRoot α j)^2)⁻¹)]
  have he : ‖exp (z^2)‖≤Real.exp (R^2)*Real.exp (-z.im^2) := by
    rw [Complex.norm_exp,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [pow_two,mul_re]
    nlinarith [sq_abs z.re,abs_nonneg z.re,sq_nonneg (R-|z.re|)]
  unfold a03ZeroModeRatioWeight
  rw [norm_mul,norm_mul]
  calc
    _ ≤ (Real.exp (R^2)*Real.exp (-z.im^2))*
        ((1+‖((a03ZeroModeRatioRoot α 0)^2)⁻¹‖)*(R+1)^2*(1+|z.im|)^2)*
          ((1+‖((a03ZeroModeRatioRoot α 1)^2)⁻¹‖)*(R+1)^2*(1+|z.im|)^2) := by
            gcongr
            · exact hf 0
            · exact hf 1
    _ = _ := by unfold a03ZeroModeRatioGaussianConstant; ring

theorem a03ZeroModeRatioRoot_norm_le {ε : ℝ} {α : MomentShifts}
    (hα : ∀ j : Fin 4,‖α j‖≤ε/8) (j : Fin 2) :
    ‖a03ZeroModeRatioRoot α j‖≤ε/8 := by
  fin_cases j
  · change ‖-(α 0-α 1)/2‖≤ε/8
    rw [norm_div,norm_neg]
    norm_num only [Complex.norm_ofNat]
    have h := (norm_sub_le (α 0) (α 1)).trans (add_le_add (hα 0) (hα 1))
    linarith
  · change ‖-(α 2-α 3)/2‖≤ε/8
    rw [norm_div,norm_neg]
    norm_num only [Complex.norm_ofNat]
    have h := (norm_sub_le (α 2) (α 3)).trans (add_le_add (hα 2) (hα 3))
    linarith

theorem a03ZeroModeRatioDifferenceArgument_norm_distance (α : MomentShifts)
    (j : Fin 2) (z : ℂ) :
    ‖1-a03ZeroModeRatioDifferenceArgument α j z‖=2*‖z-a03ZeroModeRatioRoot α j‖ := by
  unfold a03ZeroModeRatioDifferenceArgument
  rw [show 1-(1+2*(z-a03ZeroModeRatioRoot α j))=
    -(2*(z-a03ZeroModeRatioRoot α j)) by ring,norm_neg,norm_mul]
  norm_num

theorem a03ZeroModeRatioDifferenceArgument_im_abs (α : MomentShifts)
    (j : Fin 2) (z : ℂ) :
    |(a03ZeroModeRatioDifferenceArgument α j z).im|=
      2*|z.im-(a03ZeroModeRatioRoot α j).im| := by
  simp [a03ZeroModeRatioDifferenceArgument,abs_mul]

theorem a03ZeroModeRatioDifferenceArgument_line_separation {ε c : ℝ}
    (hε : 0<ε) {α : MomentShifts} (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hc : ε≤|c|) (y : ℝ) (j : Fin 2) :
    ε≤‖1-a03ZeroModeRatioDifferenceArgument α j ((c:ℂ)+(y:ℂ)*I)‖ := by
  rw [a03ZeroModeRatioDifferenceArgument_norm_distance]
  have hr := (Complex.abs_re_le_norm _).trans (a03ZeroModeRatioRoot_norm_le hα j)
  have ht : |c|≤|c-(a03ZeroModeRatioRoot α j).re|+|(a03ZeroModeRatioRoot α j).re| := by
    simpa using abs_add_le (c-(a03ZeroModeRatioRoot α j).re) (a03ZeroModeRatioRoot α j).re
  have hn := Complex.abs_re_le_norm (((c:ℂ)+(y:ℂ)*I)-a03ZeroModeRatioRoot α j)
  simp only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,
    zero_mul,sub_zero,add_zero] at hn
  linarith

theorem a03ZeroModeRatioDifferenceArgument_horizontal_separation {ε y : ℝ}
    (hε : 0<ε) (hε1 : ε<1/8) {α : MomentShifts}
    (hα : ∀ j : Fin 4,‖α j‖≤ε/8) (hy : 1≤|y|) (c : ℝ) (j : Fin 2) :
    ε≤‖1-a03ZeroModeRatioDifferenceArgument α j ((c:ℂ)+(y:ℂ)*I)‖ := by
  rw [a03ZeroModeRatioDifferenceArgument_norm_distance]
  have hr := (Complex.abs_im_le_norm _).trans (a03ZeroModeRatioRoot_norm_le hα j)
  have ht : |y|≤|y-(a03ZeroModeRatioRoot α j).im|+|(a03ZeroModeRatioRoot α j).im| := by
    simpa using abs_add_le (y-(a03ZeroModeRatioRoot α j).im) (a03ZeroModeRatioRoot α j).im
  have hn := Complex.abs_im_le_norm (((c:ℂ)+(y:ℂ)*I)-a03ZeroModeRatioRoot α j)
  simp only [sub_im,add_im,ofReal_im,mul_im,ofReal_re,I_re,I_im,mul_zero,
    mul_one,add_zero,zero_add] at hn
  linarith

theorem a03ZeroModeRatioGaussianConstant_log_growth {T κ : ℝ}
    (hT : 1<T) (hL : 1≤Real.log T) (hκ : 0<κ) (σ : MomentShifts)
    (hρ : ∀ k : Sechstmoment.PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) :
    a03ZeroModeRatioGaussianConstant (Sechstmoment.rawMomentShifts T σ) 1≤
      (Real.exp 1*16*(1+1/κ^2)^2)*(Real.log T)^4 := by
  have hroot (j : Fin 2) :
      ‖((a03ZeroModeRatioRoot (Sechstmoment.rawMomentShifts T σ) j)^2)⁻¹‖≤
        (Real.log T)^2/κ^2 := by
    fin_cases j
    · change ‖((a03ZeroModeRatioRoot (Sechstmoment.rawMomentShifts T σ) 0)^2)⁻¹‖≤_
      rw [a03ZeroModeRatioRoot_zero_eq_pure]
      simpa using purePolarRoot_inverse_sq_norm hT hκ σ (2,(1,0)) (hρ (2,(1,0)))
    · change ‖((a03ZeroModeRatioRoot (Sechstmoment.rawMomentShifts T σ) 1)^2)⁻¹‖≤_
      rw [a03ZeroModeRatioRoot_one_eq_pure]
      simpa using purePolarRoot_inverse_sq_norm hT hκ σ (2,(0,1)) (hρ (2,(0,1)))
  have hcost (j : Fin 2) :
      1+‖((a03ZeroModeRatioRoot (Sechstmoment.rawMomentShifts T σ) j)^2)⁻¹‖≤
        (1+1/κ^2)*(Real.log T)^2 := by
    have h := hroot j
    rw [show (Real.log T)^2/κ^2=(1/κ^2)*(Real.log T)^2 by ring] at h
    have hs : 1≤(Real.log T)^2 := by nlinarith
    nlinarith
  unfold a03ZeroModeRatioGaussianConstant
  norm_num only [one_pow,one_add_one_eq_two,show (2:ℝ)^4=16 by norm_num]
  calc
    _ ≤ (Real.exp 1*16)*((1+1/κ^2)*(Real.log T)^2)*
        ((1+1/κ^2)*(Real.log T)^2) := by gcongr; exact hcost 0; exact hcost 1
    _ = _ := by ring

def a03ZeroModeRatioArithmeticKernel (α : MomentShifts) (a b : ℕ)
    (u v s : ℂ) : ℂ := a03ZeroModeRatioArithmeticNumerator α a b u v s/(u*v)

theorem a03ZeroModeRatioArithmeticKernel_gaussian_majorant
    {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ) :
    ∃ C : ℝ,0≤C ∧ ∀ α : MomentShifts,
      (∀ j : Fin 4,‖α j‖≤ε/8) →
      (∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0) →
      ∀ a b : ℕ,a≠0 → b≠0 → ∀ u v s : ℂ,
      1+ε≤s.re → |u.re|≤1 → |v.re|≤1 →
      A03ZeroModeRatioContourRegion ε u v →
      ε≤‖1-a03ZeroModeRatioDifferenceArgument α 0 u‖ →
      ε≤‖1-a03ZeroModeRatioDifferenceArgument α 1 v‖ →
      ‖a03ZeroModeRatioArithmeticKernel α a b u v s‖≤
        C*(a03ZeroModeRatioGaussianConstant α 1)^2*
          (a:ℝ)^δ*(b:ℝ)^δ*‖u‖⁻¹*‖v‖⁻¹*
          (1+|u.im|)^4*(1+|v.im|)^4*
            Real.exp (Real.pi*(|u.im|+|v.im|)-u.im^2-v.im^2) := by
  obtain ⟨D,hD,hEta⟩ := a03ZeroModeRatioEtaPair_subpower_bound hδ
  obtain ⟨E,hE,hZeta⟩ := Sechstmoment.riemannZeta_norm_le_exp_halfPlane hε hε
  let Z : ℝ := Sechstmoment.zetaDirichletMajorant (1+ε)
  have hZ : 0≤Z := Sechstmoment.zetaDirichletMajorant_nonneg _
  let C : ℝ := E^2*Real.exp (Real.pi*(ε/4))*Z^3*D
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro α hα hρ a b ha hb u v s hs hu hv huv hsepU hsepV
  let B : ℝ := a03ZeroModeRatioGaussianConstant α 1
  have hB : 0≤B := a03ZeroModeRatioGaussianConstant_nonneg _ _
  have hl := a03ZeroModeRatio_contour_arguments_lower hε hα huv
  have hrootU : u≠a03ZeroModeRatioRoot α 0 := by
    intro he
    rw [a03ZeroModeRatioDifferenceArgument_norm_distance,he,sub_self,norm_zero] at hsepU
    linarith
  have hrootV : v≠a03ZeroModeRatioRoot α 1 := by
    intro he
    rw [a03ZeroModeRatioDifferenceArgument_norm_distance,he,sub_self,norm_zero] at hsepV
    linarith
  have hgu := a03ZeroModeRatioWeight_gaussian_bound α (by norm_num : (0:ℝ)≤1) hu
  have hgv := a03ZeroModeRatioWeight_gaussian_bound α (by norm_num : (0:ℝ)≤1) hv
  have hz (j : Fin 2) (z : ℂ)
      (hzre : ε≤(a03ZeroModeRatioDifferenceArgument α j z).re)
      (hzsep : ε≤‖1-a03ZeroModeRatioDifferenceArgument α j z‖) :
      ‖riemannZeta (a03ZeroModeRatioDifferenceArgument α j z)‖≤
        E*Real.exp (Real.pi*(|z.im|+ε/8)) := by
    have him : |(a03ZeroModeRatioDifferenceArgument α j z).im|≤2*(|z.im|+ε/8) := by
      rw [a03ZeroModeRatioDifferenceArgument_im_abs]
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
      exact (abs_sub _ _).trans (add_le_add le_rfl
        ((Complex.abs_im_le_norm _).trans (a03ZeroModeRatioRoot_norm_le hα j)))
    exact (hZeta _ hzre hzsep).trans (by gcongr; nlinarith [Real.pi_pos])
  have hzu := hz 0 u hl.1 hsepU
  have hzv := hz 1 v hl.2.1 hsepV
  rw [a03ZeroModeRatioDifferenceArgument_zero] at hzu
  rw [a03ZeroModeRatioDifferenceArgument_one] at hzv
  have hzs : ‖riemannZeta s‖≤Z :=
    Sechstmoment.riemannZeta_norm_le_dirichlet (by linarith : 1<1+ε) hs
  have hzm : ‖riemannZeta (a03ZeroModeRatioEulerArgument α u v-1+s)‖≤Z := by
    apply Sechstmoment.riemannZeta_norm_le_dirichlet (by linarith : 1<1+ε)
    simp only [add_re,sub_re,one_re]
    linarith [hl.2.2]
  have hzi : ‖(riemannZeta (a03ZeroModeRatioEulerArgument α u v))⁻¹‖≤Z :=
    Sechstmoment.riemannZeta_inv_norm_le_dirichlet (by linarith : 1<1+ε) hl.2.2
  have hzi' : ‖riemannZeta (2+α 0-α 1+α 2-α 3+2*u+2*v)‖⁻¹≤Z := by
    simpa only [a03ZeroModeRatioEulerArgument,norm_inv] using hzi
  have het := hEta α a b ha hb u v s (by linarith : 1≤s.re)
    (hε.le.trans hl.1) (hε.le.trans hl.2.1) (by linarith [hl.2.2])
  unfold a03ZeroModeRatioArithmeticKernel
  rw [a03ZeroModeRatioArithmeticNumerator_eq α a b s hρ hrootU hrootV]
  have he : 1+α 0-α 1+α 2-α 3+2*u+2*v+s=
      a03ZeroModeRatioEulerArgument α u v-1+s := by
    unfold a03ZeroModeRatioEulerArgument
    ring
  rw [he]
  change ‖_‖≤_
  simp only [norm_mul,div_eq_mul_inv,norm_inv]
  calc
    _ ≤ ((B*(1+|u.im|)^4*Real.exp (-u.im^2))*‖u‖⁻¹)*
        ((B*(1+|v.im|)^4*Real.exp (-v.im^2))*‖v‖⁻¹)*
          (Z*Z*(E*Real.exp (Real.pi*(|u.im|+ε/8)))*
            (E*Real.exp (Real.pi*(|v.im|+ε/8)))*Z)*
              (D*(a:ℝ)^δ*(b:ℝ)^δ) := by
                gcongr
    _ = _ := by
      have hexp : Real.exp (-u.im^2)*Real.exp (-v.im^2)*
          Real.exp (Real.pi*(|u.im|+ε/8))*Real.exp (Real.pi*(|v.im|+ε/8))=
            Real.exp (Real.pi*(ε/4))*
              Real.exp (Real.pi*(|u.im|+|v.im|)-u.im^2-v.im^2) := by
        rw [←Real.exp_add,←Real.exp_add,←Real.exp_add,←Real.exp_add]
        congr 1
        ring
      calc
        _ = B^2*E^2*Z^3*D*(a:ℝ)^δ*(b:ℝ)^δ*
            ‖u‖⁻¹*‖v‖⁻¹*(1+|u.im|)^4*(1+|v.im|)^4*
              (Real.exp (-u.im^2)*Real.exp (-v.im^2)*
                Real.exp (Real.pi*(|u.im|+ε/8))*Real.exp (Real.pi*(|v.im|+ε/8))) := by ring
        _ = _ := by rw [hexp]; dsimp [C,B]; ring

end
end Sechstmoment.Source
