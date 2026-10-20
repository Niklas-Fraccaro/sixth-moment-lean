import Sechstmoment.Numerator.U.ZeroModes.Ratio.WeightedDoubleShift


namespace Sechstmoment.Source
open Complex Real MeasureTheory
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0

def a03ZeroModeRatioPhysicalLogLeft (g a : ℕ) (x : ℝ) : ℝ :=
  Real.log (x/(g*a:ℕ))

def a03ZeroModeRatioPhysicalLogRight (g b : ℕ) (x : ℝ) : ℝ :=
  Real.log (x/(g*b:ℕ))

def a03ZeroModeRatioPhysicalPrefactor (α : MomentShifts) (g a b : ℕ)
    (A B : ℕ→ℂ) (x : ℝ) (s : ℂ) : ℂ :=
  A (g*a)*B (g*b)*(g:ℂ)^(-1+α 1+α 3-s)*(a:ℂ)^(-1+α 1)*
    (b:ℂ)^(-1+α 3)*(x:ℂ)^(-α 1-α 3)

def a03ZeroModeRatioPhysicalKernel (α : MomentShifts) (g a b : ℕ)
    (A B : ℕ→ℂ) (x : ℝ) (u v s : ℂ) : ℂ :=
  A (g*a)*B (g*b)*(g:ℂ)^(-1+α 1+α 3-u-v-s)*(a:ℂ)^(-1+α 1-u)*
    (b:ℂ)^(-1+α 3-v)*(x:ℂ)^(-α 1-α 3+u+v)*
      a03ZeroModeRatioArithmeticKernel α a b u v s

theorem a03ZeroModeRatioPhysicalLogLeft_eq {g a : ℕ} (hg : 0<g) (ha : 0<a)
    {x : ℝ} (hx : 0<x) :
    a03ZeroModeRatioPhysicalLogLeft g a x=Real.log x-Real.log g-Real.log a := by
  unfold a03ZeroModeRatioPhysicalLogLeft
  rw [Nat.cast_mul,Real.log_div hx.ne' (mul_pos (by exact_mod_cast hg) (by exact_mod_cast ha)).ne',
    Real.log_mul (by exact_mod_cast hg.ne') (by exact_mod_cast ha.ne')]
  ring

theorem a03ZeroModeRatioPhysicalLogRight_eq {g b : ℕ} (hg : 0<g) (hb : 0<b)
    {x : ℝ} (hx : 0<x) :
    a03ZeroModeRatioPhysicalLogRight g b x=Real.log x-Real.log g-Real.log b :=
  a03ZeroModeRatioPhysicalLogLeft_eq hg hb hx

theorem a03ZeroModeRatioPhysicalPowers_factor (α : MomentShifts)
    {g a b : ℕ} (hg : 0<g) (ha : 0<a) (hb : 0<b) {x : ℝ} (hx : 0<x) (u v s : ℂ) :
    (g:ℂ)^(-1+α 1+α 3-u-v-s)*(a:ℂ)^(-1+α 1-u)*
      (b:ℂ)^(-1+α 3-v)*(x:ℂ)^(-α 1-α 3+u+v)=
    ((g:ℂ)^(-1+α 1+α 3-s)*(a:ℂ)^(-1+α 1)*(b:ℂ)^(-1+α 3)*(x:ℂ)^(-α 1-α 3))*
      a03ZeroModeRatioExponential (a03ZeroModeRatioPhysicalLogLeft g a x)
        (a03ZeroModeRatioPhysicalLogRight g b x) u v := by
  have hc (r : ℝ) (hr : 0<r) (z : ℂ) : (r:ℂ)^z=exp ((Real.log r:ℂ)*z) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),←Complex.ofReal_log hr.le]
  have hgc : (g:ℂ)=((g:ℝ):ℂ) := by simp
  have hac : (a:ℂ)=((a:ℝ):ℂ) := by simp
  have hbc : (b:ℂ)=((b:ℝ):ℂ) := by simp
  simp_rw [hgc,hac,hbc,hc g (by exact_mod_cast hg),hc a (by exact_mod_cast ha),
    hc b (by exact_mod_cast hb),hc x hx]
  unfold a03ZeroModeRatioExponential
  rw [a03ZeroModeRatioPhysicalLogLeft_eq hg ha hx,a03ZeroModeRatioPhysicalLogRight_eq hg hb hx]
  simp only [Complex.ofReal_sub]
  rw [←Complex.exp_add,←Complex.exp_add,←Complex.exp_add,←Complex.exp_add,
    ←Complex.exp_add,←Complex.exp_add,←Complex.exp_add]
  congr 1
  ring

theorem a03ZeroModeRatioPhysicalKernel_eq_weighted (α : MomentShifts)
    {g a b : ℕ} (hg : 0<g) (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ)
    {x : ℝ} (hx : 0<x) (u v s : ℂ) :
    a03ZeroModeRatioPhysicalKernel α g a b A B x u v s=
      a03ZeroModeRatioPhysicalPrefactor α g a b A B x s*
        a03ZeroModeRatioWeightedKernel (a03ZeroModeRatioPhysicalLogLeft g a x)
          (a03ZeroModeRatioPhysicalLogRight g b x) α a b u v s := by
  have hp := a03ZeroModeRatioPhysicalPowers_factor α hg ha hb hx u v s
  unfold a03ZeroModeRatioPhysicalKernel a03ZeroModeRatioPhysicalPrefactor a03ZeroModeRatioWeightedKernel
  calc
    _ = (A (g*a)*B (g*b))*
      ((g:ℂ)^(-1+α 1+α 3-u-v-s)*(a:ℂ)^(-1+α 1-u)*
        (b:ℂ)^(-1+α 3-v)*(x:ℂ)^(-α 1-α 3+u+v))*
          a03ZeroModeRatioArithmeticKernel α a b u v s := by ring
    _ = _ := by rw [hp]; ring

theorem a03ZeroModeRatioDoubleIntegral_const_mul (c d : ℝ) (C : ℂ) (F : ℂ→ℂ→ℂ) :
    a03ZeroModeRatioDoubleIntegral c d (fun u v => C*F u v)=
      C*a03ZeroModeRatioDoubleIntegral c d F := by
  unfold a03ZeroModeRatioDoubleIntegral verticalIntegral
  simp only [integral_const_mul]
  ring

theorem a03ZeroModeRatioPhysicalKernel_double_shift
    {ε δ : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {g a b : ℕ} (hg : 0<g) (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ)
    {x : ℝ} (hx : 0<x) {s : ℂ} (hs : 1+ε≤s.re) :
    a03ZeroModeRatioDoubleIntegral ε ε (fun u v => a03ZeroModeRatioPhysicalKernel α g a b A B x u v s)=
      a03ZeroModeRatioDoubleIntegral (a03ZeroModeRatioPrimaryLine ε) (a03ZeroModeRatioPrimaryLine ε)
        (fun u v => a03ZeroModeRatioPhysicalKernel α g a b A B x u v s)+
      a03ZeroModeRatioPhysicalPrefactor α g a b A B x s*
        (verticalIntegral (a03ZeroModeRatioSecondaryLine ε)
          (a03ZeroModeRatioWeightedLeftResidue (a03ZeroModeRatioPhysicalLogLeft g a x)
            (a03ZeroModeRatioPhysicalLogRight g b x) α a b s)+
         verticalIntegral (a03ZeroModeRatioSecondaryLine ε)
          (a03ZeroModeRatioWeightedRightResidue (a03ZeroModeRatioPhysicalLogLeft g a x)
            (a03ZeroModeRatioPhysicalLogRight g b x) α a b s)+
         a03ZeroModeRatioArithmeticNumerator α a b 0 0 s) := by
  simp_rw [a03ZeroModeRatioPhysicalKernel_eq_weighted α hg ha hb A B hx]
  rw [a03ZeroModeRatioDoubleIntegral_const_mul,a03ZeroModeRatioDoubleIntegral_const_mul,
    a03ZeroModeRatioWeightedKernel_double_shift _ _ hε hε1 hδ α hα hρ ha.ne' hb.ne' hs]
  ring

end
end Sechstmoment.Source
