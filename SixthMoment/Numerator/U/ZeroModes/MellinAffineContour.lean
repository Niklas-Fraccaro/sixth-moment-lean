import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import SixthMoment.Numerator.U.ZeroModes.GammaCos

namespace SixthMoment.Source
open Complex Real MeasureTheory Filter
noncomputable section
set_option maxHeartbeats 300000

theorem a03VerticalIntegral_affine_substitution (F : ℂ→ℂ) (A : ℂ) (cs : ℝ)
    {d : ℝ} (hd : 0<d) :
    verticalIntegral cs (fun s => F ((s-A)/(d:ℂ)))=
      (d:ℂ)*verticalIntegral ((cs-A.re)/d) F := by
  let f : ℝ→ℂ := fun v => F (((cs-A.re)/d:ℝ)+(v:ℂ)*I)
  have he (v : ℝ) : F ((((cs:ℂ)+(v:ℂ)*I)-A)/(d:ℂ))=f ((v-A.im)/d) := by
    congr 1
    apply Complex.ext <;> simp [Complex.div_re,Complex.div_im]
  unfold verticalIntegral
  simp_rw [he]
  have hshift := integral_add_right_eq_self (μ:=volume) (fun v : ℝ => f (v/d)) (-A.im)
  have hs : (∫v : ℝ,f ((v-A.im)/d))=∫v : ℝ,f (v/d) := by
    simpa only [sub_eq_add_neg] using hshift
  rw [hs,Measure.integral_comp_div,abs_of_pos hd,Complex.real_smul]
  dsimp only [f]
  ring

theorem a03ZeroModeAfterXMellin_vertical_eq_M (N₁ N₂ : ℕ) (a b : ℕ→ℂ)
    (α : MomentShifts) (G : ℂ→ℂ) {cs : ℝ} (hcs : 1<cs) :
    verticalIntegral cs (a03ZeroModeAfterXMellin N₁ N₂ a b α G)=
      verticalIntegral ((cs-(α 1+α 3).re)/2)
        (fun w => G w/w*a03EtaMainFunction N₁ N₂ a b α w) := by
  let A : ℂ := α 1+α 3
  let F : ℂ→ℂ := fun w => G w/w*a03EtaMainFunction N₁ N₂ a b α w
  have he (v : ℝ) : a03ZeroModeAfterXMellin N₁ N₂ a b α G ((cs:ℂ)+(v:ℂ)*I)=
      (1/2:ℂ)*F ((((cs:ℂ)+(v:ℂ)*I)-A)/2) := by
    let w : ℂ := (((cs:ℂ)+(v:ℂ)*I)-A)/2
    have hw : α 1+α 3+2*w=(cs:ℂ)+(v:ℂ)*I := by dsimp [w,A]; ring
    have hp : 0<(α 1+α 3+2*w).re := by rw [hw]; simpa using zero_lt_one.trans hcs
    have hne : α 1+α 3+2*w≠1 := by
      rw [hw]
      intro hh
      have hr := congrArg Complex.re hh
      simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
        Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero,Complex.one_re] at hr
      linarith only [hr,hcs]
    have hm := a03ZeroModeAfterXMellin_affine_eq_M N₁ N₂ a b α G w hp hne
    rw [hw] at hm
    dsimp only [F,w]
    linear_combination (1/2:ℂ)*hm
  have hi : verticalIntegral cs (a03ZeroModeAfterXMellin N₁ N₂ a b α G)=
      (1/2:ℂ)*verticalIntegral cs (fun s => F ((s-A)/2)) := by
    unfold verticalIntegral
    simp_rw [he]
    rw [integral_const_mul]
    ring
  have hh := a03VerticalIntegral_affine_substitution F A cs (by norm_num : (0:ℝ)<2)
  simp only [Complex.ofReal_ofNat] at hh
  rw [hi,hh]
  dsimp only [A,F]
  ring

end
end SixthMoment.Source
