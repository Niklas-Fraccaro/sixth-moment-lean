import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Sechstmoment.Numerator.U.ZeroModes.Ratio.HorizontalMajorants


namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 0

def a03ZeroModeRatioExponential (L M : ℝ) (u v : ℂ) : ℂ :=
  exp ((L:ℂ)*u+(M:ℂ)*v)

def a03ZeroModeRatioWeightedNumerator (L M : ℝ) (α : MomentShifts) (a b : ℕ)
    (u v s : ℂ) : ℂ :=
  a03ZeroModeRatioExponential L M u v*a03ZeroModeRatioArithmeticNumerator α a b u v s

def a03ZeroModeRatioWeightedKernel (L M : ℝ) (α : MomentShifts) (a b : ℕ)
    (u v s : ℂ) : ℂ :=
  a03ZeroModeRatioExponential L M u v*a03ZeroModeRatioArithmeticKernel α a b u v s

def a03ZeroModeRatioWeightedLeftResidue (_L M : ℝ) (α : MomentShifts) (a b : ℕ)
    (s v : ℂ) : ℂ :=
  exp ((M:ℂ)*v)*a03ZeroModeRatioLeftResidueKernel α a b s v

def a03ZeroModeRatioWeightedRightResidue (L _M : ℝ) (α : MomentShifts) (a b : ℕ)
    (s u : ℂ) : ℂ :=
  exp ((L:ℂ)*u)*a03ZeroModeRatioRightResidueKernel α a b s u

theorem a03ZeroModeRatioExponential_norm (L M : ℝ) (u v : ℂ) :
    ‖a03ZeroModeRatioExponential L M u v‖=Real.exp (L*u.re+M*v.re) := by
  simp [a03ZeroModeRatioExponential,Complex.norm_exp]

theorem a03ZeroModeRatioExponential_eq_positive_powers {r t : ℝ}
    (hr : 0<r) (ht : 0<t) (u v : ℂ) :
    a03ZeroModeRatioExponential (Real.log r) (Real.log t) u v=(r:ℂ)^u*(t:ℂ)^v := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'),
    ←Complex.ofReal_log hr.le,←Complex.ofReal_log ht.le,←Complex.exp_add]
  rfl

theorem a03ZeroModeRatioWeightedNumerator_differentiableAt_comp
    (L M : ℝ) (α : MomentShifts)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1≤s.re)
    {U V : E→ℂ} {z : E} (hU : DifferentiableAt ℂ U z) (hV : DifferentiableAt ℂ V z)
    (hden : 1<(a03ZeroModeRatioEulerArgument α (U z) (V z)).re) :
    DifferentiableAt ℂ
      (fun y => a03ZeroModeRatioWeightedNumerator L M α a b (U y) (V y) s) z :=
  ((hU.const_mul (L:ℂ)).add (hV.const_mul (M:ℂ))).cexp.mul
    (a03ZeroModeRatioArithmeticNumerator_differentiableAt_comp α ha hb hs hU hV hden)

theorem a03ZeroModeRatioWeightedNumerator_div_eq (L M : ℝ) (α : MomentShifts)
    (a b : ℕ) (u v s : ℂ) :
    a03ZeroModeRatioWeightedNumerator L M α a b u v s/(u*v)=
      a03ZeroModeRatioWeightedKernel L M α a b u v s := by
  unfold a03ZeroModeRatioWeightedNumerator a03ZeroModeRatioWeightedKernel a03ZeroModeRatioArithmeticKernel
  ring

theorem a03ZeroModeRatioWeightedKernel_split (L M : ℝ) (α : MomentShifts)
    (a b : ℕ) (u v s : ℂ) :
    a03ZeroModeRatioWeightedKernel L M α a b u v s=
      exp ((M:ℂ)*v)*(exp ((L:ℂ)*u)*a03ZeroModeRatioArithmeticKernel α a b u v s) := by
  unfold a03ZeroModeRatioWeightedKernel a03ZeroModeRatioExponential
  rw [Complex.exp_add]
  ring

theorem a03ZeroModeRatioWeightedNumerator_left_residue (L M : ℝ) (α : MomentShifts)
    (a b : ℕ) (s v : ℂ) :
    a03ZeroModeRatioWeightedNumerator L M α a b 0 v s/v=
      a03ZeroModeRatioWeightedLeftResidue L M α a b s v := by
  simp only [a03ZeroModeRatioWeightedNumerator,a03ZeroModeRatioExponential,mul_zero,zero_add,
    a03ZeroModeRatioWeightedLeftResidue,a03ZeroModeRatioLeftResidueKernel]
  ring

theorem a03ZeroModeRatioWeightedNumerator_right_residue (L M : ℝ) (α : MomentShifts)
    (a b : ℕ) (s u : ℂ) :
    a03ZeroModeRatioWeightedNumerator L M α a b u 0 s/u=
      a03ZeroModeRatioWeightedRightResidue L M α a b s u := by
  simp only [a03ZeroModeRatioWeightedNumerator,a03ZeroModeRatioExponential,mul_zero,add_zero,
    a03ZeroModeRatioWeightedRightResidue,a03ZeroModeRatioRightResidueKernel]
  ring

theorem a03ZeroModeRatioWeightedNumerator_zero (L M : ℝ) (α : MomentShifts)
    (a b : ℕ) (s : ℂ) :
    a03ZeroModeRatioWeightedNumerator L M α a b 0 0 s=
      a03ZeroModeRatioArithmeticNumerator α a b 0 0 s := by
  simp [a03ZeroModeRatioWeightedNumerator,a03ZeroModeRatioExponential]

theorem a03ZeroModeRatioWeightedNumerator_sideSwap (L M : ℝ) (α : MomentShifts)
    (a b : ℕ) (u v s : ℂ) :
    a03ZeroModeRatioWeightedNumerator M L (a03ZeroModeRatioSideSwap α) b a v u s=
      a03ZeroModeRatioWeightedNumerator L M α a b u v s := by
  unfold a03ZeroModeRatioWeightedNumerator a03ZeroModeRatioExponential
  rw [a03ZeroModeRatioArithmeticNumerator_sideSwap,add_comm ((M:ℂ)*v) ((L:ℂ)*u)]

theorem a03ZeroModeRatioWeightedKernel_sideSwap (L M : ℝ) (α : MomentShifts)
    (a b : ℕ) (u v s : ℂ) :
    a03ZeroModeRatioWeightedKernel M L (a03ZeroModeRatioSideSwap α) b a v u s=
      a03ZeroModeRatioWeightedKernel L M α a b u v s := by
  unfold a03ZeroModeRatioWeightedKernel a03ZeroModeRatioExponential
  rw [a03ZeroModeRatioArithmeticKernel_sideSwap,add_comm ((M:ℂ)*v) ((L:ℂ)*u)]

theorem a03ZeroModeRatioWeightedLeftResidue_sideSwap (L M : ℝ) (α : MomentShifts)
    (a b : ℕ) (s u : ℂ) :
    a03ZeroModeRatioWeightedLeftResidue M L (a03ZeroModeRatioSideSwap α) b a s u=
      a03ZeroModeRatioWeightedRightResidue L M α a b s u := by
  unfold a03ZeroModeRatioWeightedLeftResidue a03ZeroModeRatioWeightedRightResidue
    a03ZeroModeRatioLeftResidueKernel a03ZeroModeRatioRightResidueKernel
  rw [a03ZeroModeRatioArithmeticNumerator_sideSwap]

theorem a03RatioExponential_line_integrable (L c : ℝ) (F : ℂ→ℂ)
    (hF : Integrable (fun y : ℝ => F ((c:ℂ)+(y:ℂ)*I))) :
    Integrable (fun y : ℝ => exp ((L:ℂ)*((c:ℂ)+(y:ℂ)*I))*F ((c:ℂ)+(y:ℂ)*I)) := by
  have hmeas : AEStronglyMeasurable (fun y : ℝ => exp ((L:ℂ)*((c:ℂ)+(y:ℂ)*I))*
      F ((c:ℂ)+(y:ℂ)*I)) :=
    (by fun_prop : Continuous (fun y : ℝ => exp ((L:ℂ)*((c:ℂ)+(y:ℂ)*I)))).aestronglyMeasurable.mul
      hF.aestronglyMeasurable
  apply (hF.norm.const_mul (Real.exp (L*c))).mono' hmeas
  exact Eventually.of_forall (fun y => by
    rw [norm_mul,Complex.norm_exp]
    simp)

theorem a03RatioExponentialPair_line_integrable (L M c : ℝ) (v : ℂ) (F : ℂ→ℂ)
    (hF : Integrable (fun y : ℝ => F ((c:ℂ)+(y:ℂ)*I))) :
    Integrable (fun y : ℝ => a03ZeroModeRatioExponential L M ((c:ℂ)+(y:ℂ)*I) v*
      F ((c:ℂ)+(y:ℂ)*I)) := by
  have h := (a03RatioExponential_line_integrable L c F hF).const_mul (exp ((M:ℂ)*v))
  convert h using 1
  funext y
  unfold a03ZeroModeRatioExponential
  rw [Complex.exp_add]
  ring

theorem a03RatioExponentialPair_joint_integrable (L M c d : ℝ) (F : ℂ→ℂ→ℂ)
    (hF : Integrable (fun p : ℝ×ℝ => F ((c:ℂ)+(p.1:ℂ)*I) ((d:ℂ)+(p.2:ℂ)*I))
      (volume.prod volume)) :
    Integrable (fun p : ℝ×ℝ => a03ZeroModeRatioExponential L M
      ((c:ℂ)+(p.1:ℂ)*I) ((d:ℂ)+(p.2:ℂ)*I)*F
        ((c:ℂ)+(p.1:ℂ)*I) ((d:ℂ)+(p.2:ℂ)*I)) (volume.prod volume) := by
  have hmeas := (by fun_prop : Continuous (fun p : ℝ×ℝ =>
    exp ((L:ℂ)*((c:ℂ)+(p.1:ℂ)*I)+(M:ℂ)*((d:ℂ)+(p.2:ℂ)*I)))).aestronglyMeasurable.mul
      hF.aestronglyMeasurable
  apply (hF.norm.const_mul (Real.exp (L*c+M*d))).mono' hmeas
  exact Eventually.of_forall (fun p => by
    change ‖a03ZeroModeRatioExponential L M ((c:ℂ)+(p.1:ℂ)*I) ((d:ℂ)+(p.2:ℂ)*I)*
      F ((c:ℂ)+(p.1:ℂ)*I) ((d:ℂ)+(p.2:ℂ)*I)‖≤_
    rw [norm_mul,a03ZeroModeRatioExponential_norm]
    simp)

theorem a03RatioExponential_horizontal_tendsto_zero (L l r : ℝ) (F : ℂ→ℂ)
    (hlr : l≤r) (habs : ∀ c∈Icc l r,|c|≤1)
    (hb : ∃ Q : ℝ,0≤Q ∧ ∀ y : ℝ,1≤|y| → ∀ c∈Icc l r,
      ‖F ((c:ℂ)+(y:ℂ)*I)‖≤Q*((1+|y|)^4*Real.exp (Real.pi*|y|-y^2))) :
    Tendsto (fun y : ℝ => ∫ c in l..r,
      exp ((L:ℂ)*((c:ℂ)+(y:ℂ)*I))*F ((c:ℂ)+(y:ℂ)*I)) (cocompact ℝ) (𝓝 0) := by
  obtain ⟨Q,hQ,hbnd⟩ := hb
  have hyv : Tendsto (fun y : ℝ => |y|) (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop]
    exact tendsto_abs_atBot_atTop.sup tendsto_abs_atTop_atTop
  have hlim := (Sechstmoment.gaussianPolynomialExponential_tendsto_zero 4 Real.pi).const_mul
    (|r-l| * Real.exp |L| * Q)
  simp only [mul_zero] at hlim
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [hyv.eventually (eventually_ge_atTop (1:ℝ))] with y hy
  have hnorm (c : ℝ) (hc : c∈uIoc l r) :
      ‖exp ((L:ℂ)*((c:ℂ)+(y:ℂ)*I))*F ((c:ℂ)+(y:ℂ)*I)‖≤
        Real.exp |L| * Q*((1+|y|)^4*Real.exp (Real.pi*|y|-y^2)) := by
    rw [uIoc_of_le hlr] at hc
    have he : ‖exp ((L:ℂ)*((c:ℂ)+(y:ℂ)*I))‖≤Real.exp |L| := by
      rw [Complex.norm_exp]
      have hre : ((L:ℂ)*((c:ℂ)+(y:ℂ)*I)).re=L*c := by simp
      rw [hre]
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ |L*c| := le_abs_self _
        _ = |L| * |c| := abs_mul _ _
        _ ≤ |L| * 1 := mul_le_mul_of_nonneg_left (habs c ⟨hc.1.le,hc.2⟩) (abs_nonneg _)
        _ = _ := mul_one _
    rw [norm_mul]
    exact (mul_le_mul he (hbnd y hy c ⟨hc.1.le,hc.2⟩) (norm_nonneg _) (Real.exp_pos _).le).trans_eq
      (by ring)
  exact (intervalIntegral.norm_integral_le_of_norm_le_const hnorm).trans_eq (by ring)

end
end Sechstmoment.Source
