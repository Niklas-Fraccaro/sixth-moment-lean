import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Sechstmoment.Numerator.U.Separation.LogarithmicMellinWeights
import Sechstmoment.Numerator.U.Separation.Tensor.LogCutoff

namespace Sechstmoment
open Complex Real Set
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

def a03TensorMellinLinear (α : MomentShifts) (z : ℂ) : A03SixTensorSpace →L[ℝ] ℂ :=
  ∑ i : Fin 4, (EuclideanSpace.proj i.succ.succ).smulRight (-(1/2+α i+z))

def a03TensorMellinFactor (α : MomentShifts) (z : ℂ) (y : A03SixTensorSpace) : ℂ :=
  Complex.exp (a03TensorMellinLinear α z y)

theorem a03TensorMellinFactor_eq_exp (α : MomentShifts) (z : ℂ) (y : A03SixTensorSpace) :
    a03TensorMellinFactor α z y =
      Complex.exp (∑ i : Fin 4, -(1/2+α i+z)*(y i.succ.succ : ℂ)) := by
  unfold a03TensorMellinFactor a03TensorMellinLinear
  congr 1
  simp only [sum_apply,ContinuousLinearMap.smulRight_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.real_smul,mul_comm]
  rfl

theorem a03TensorMellinFactor_contDiff (α : MomentShifts) (z : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (a03TensorMellinFactor α z) := by
  exact (a03TensorMellinLinear α z).contDiff.cexp

theorem a03TensorMellinLinear_norm_le {α : MomentShifts}
    (hα : ∀ i, ‖α i‖ ≤ 1/4) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) (v : ℝ) :
    ‖a03TensorMellinLinear α ((c : ℂ)+(v : ℂ)*I)‖ ≤ 8*(1+|v|) := by
  have hcoef (i : Fin 4) : ‖-(1/2+α i+((c : ℂ)+(v : ℂ)*I))‖ ≤ 2*(1+|v|) := by
    rw [norm_neg]
    have hz : ‖(c : ℂ)+(v : ℂ)*I‖ ≤ c+|v| := by
      exact (norm_add_le _ _).trans_eq (by
        simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one,abs_of_nonneg hc])
    have h := norm_add_le ((1/2 : ℂ)+α i) ((c : ℂ)+(v : ℂ)*I)
    have h' := norm_add_le (1/2 : ℂ) (α i)
    norm_num at h'
    nlinarith [hα i,abs_nonneg v]
  apply (a03TensorMellinLinear α ((c : ℂ)+(v : ℂ)*I)).opNorm_le_bound (by positivity)
  intro y
  unfold a03TensorMellinLinear
  simp only [sum_apply,ContinuousLinearMap.smulRight_apply,
    ]
  change ‖∑ i : Fin 4, y i.succ.succ • -(1/2+α i+((c : ℂ)+(v : ℂ)*I))‖ ≤ _
  calc
    _ ≤ ∑ i : Fin 4, ‖y i.succ.succ • -(1/2+α i+((c : ℂ)+(v : ℂ)*I))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 4, (8*(1+|v|)/4)*‖y‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      have hy := PiLp.norm_apply_le y i.succ.succ
      calc
        _ ≤ ‖y‖*(2*(1+|v|)) := mul_le_mul hy (hcoef i) (norm_nonneg _) (norm_nonneg y)
        _ = _ := by ring
    _ = _ := by simp; ring

theorem a03TensorMellinFactor_box_norm_le {α : MomentShifts}
    (hα : ∀ i, ‖α i‖ ≤ 1/4) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (v : ℝ) {y : A03SixTensorSpace} (hy : y ∈ a03TensorLogCutoffBox) :
    ‖a03TensorMellinFactor α ((c : ℂ)+(v : ℂ)*I) y‖ ≤ Real.exp 8 := by
  rw [a03TensorMellinFactor_eq_exp,Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  rw [Complex.re_sum]
  have hh (i : Fin 4) :
      (-(1/2+α i+((c : ℂ)+(v : ℂ)*I))*(y i.succ.succ : ℂ)).re ≤ 2 := by
    have ha := abs_le.mp ((Complex.abs_re_le_norm (α i)).trans (hα i))
    have hya := hy i.succ.succ
    norm_num [Complex.mul_re,Complex.add_re,Complex.add_im]
    have hk : -c+(-(α i).re+-(1/2 : ℝ)) ≤ 0 := by linarith
    have hm := mul_le_mul_of_nonpos_left hya.1 hk
    nlinarith
  calc
    _ ≤ ∑ _i : Fin 4, (2 : ℝ) := Finset.sum_le_sum (fun i _ => hh i)
    _ = 8 := by norm_num

theorem a03_cexp_norm_iteratedFDeriv (j : ℕ) (w : ℂ) :
    ‖iteratedFDeriv ℝ j Complex.exp w‖ = ‖Complex.exp w‖ := by
  have hc : ContDiffAt ℂ (j : ℕ∞ω) Complex.exp w := Complex.contDiff_exp.contDiffAt
  rw [← hc.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp only [Function.comp_apply,ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_eq_iterate,Complex.iter_deriv_exp]

theorem a03TensorMellinFactor_polynomial_derivative_bounds {α : MomentShifts}
    (hα : ∀ i, ‖α i‖ ≤ 1/4) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (v : ℝ) (j : ℕ) {y : A03SixTensorSpace} (hy : y ∈ a03TensorLogCutoffBox) :
    ‖iteratedFDeriv ℝ j (a03TensorMellinFactor α ((c : ℂ)+(v : ℂ)*I)) y‖ ≤
      Real.exp 8*(8*(1+|v|))^j := by
  let L := a03TensorMellinLinear α ((c : ℂ)+(v : ℂ)*I)
  change ‖iteratedFDeriv ℝ j (Complex.exp ∘ L) y‖ ≤ _
  rw [L.iteratedFDeriv_comp_right (Complex.contDiff_exp : ContDiff ℝ (⊤ : ℕ∞) Complex.exp) y (by simp)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j Complex.exp (L y)‖*(∏ _i : Fin j, ‖L‖) :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖Complex.exp (L y)‖*‖L‖^j := by rw [a03_cexp_norm_iteratedFDeriv]; simp
    _ ≤ Real.exp 8*(8*(1+|v|))^j := by
      apply mul_le_mul
      · exact a03TensorMellinFactor_box_norm_le hα hc hc1 v hy
      · exact pow_le_pow_left₀ (norm_nonneg L) (a03TensorMellinLinear_norm_le hα hc hc1 v) j
      · positivity
      · positivity

theorem a03TensorMellinFactor_logarithmic_uniform_derivative_bounds
    {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 ≤ θ) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧ ∀ T : ℝ, 1 ≤ T →
      ∀ α : MomentShifts, (∀ i, ‖α i‖ ≤ 1/4) → ∀ c : ℝ, 0 ≤ c → c ≤ 1 →
      ∀ v : ℝ, |v| ≤ θ*Real.log T → ∀ j : ℕ, ∀ y ∈ a03TensorLogCutoffBox,
      ‖iteratedFDeriv ℝ j (a03TensorMellinFactor α ((c : ℂ)+(v : ℂ)*I)) y‖ ≤ B j*T^ε := by
  let B : ℕ → ℝ := fun j => Real.exp 8*(8*(1+θ))^j*((j.factorial : ℝ)/ε^j*Real.exp ε)
  refine ⟨B,fun j => by dsimp [B]; positivity,?_⟩
  intro T hT α hα c hc hc1 v hv j y hy
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  have hp : 8*(1+|v|) ≤ (8*(1+θ))*(1+Real.log T) := by nlinarith
  calc
    _ ≤ Real.exp 8*(8*(1+|v|))^j := a03TensorMellinFactor_polynomial_derivative_bounds hα hc hc1 v j hy
    _ ≤ Real.exp 8*((8*(1+θ))*(1+Real.log T))^j := by gcongr
    _ = (Real.exp 8*(8*(1+θ))^j)*(1+Real.log T)^j := by rw [mul_pow]; ring
    _ ≤ (Real.exp 8*(8*(1+θ))^j)*(((j.factorial : ℝ)/ε^j*Real.exp ε)*T^ε) :=
      mul_le_mul_of_nonneg_left (logarithmic_power_le_rpow hε hT j) (by positivity)
    _ = B j*T^ε := by dsimp [B]; ring

end
