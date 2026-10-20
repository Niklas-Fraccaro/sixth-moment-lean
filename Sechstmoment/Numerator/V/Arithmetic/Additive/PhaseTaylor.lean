import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds


namespace Sechstmoment.Source
open Complex Real
noncomputable section

theorem norm_pure_exp_sub_le (a b : ℝ) :
    ‖Complex.exp (I*(a:ℂ))-Complex.exp (I*(b:ℂ))‖ ≤ |a-b| := by
  have he : Complex.exp (I*(a:ℂ))-Complex.exp (I*(b:ℂ)) =
      Complex.exp (I*(b:ℂ))*(Complex.exp (I*((a-b:ℝ):ℂ))-1) := by
    rw [mul_sub,mul_one,← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hnorm : ‖Complex.exp (I*(b:ℂ))‖ = 1 := by simp [Complex.norm_exp]
  rw [he,norm_mul,hnorm,one_mul]
  simpa only [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := a-b))

theorem additive_exp_phase_linearization (a v : ℝ) (hv : |v| ≤ 1) :
    ‖Complex.exp (I*((a*Real.exp v:ℝ):ℂ))-
      Complex.exp (I*(a:ℂ))*Complex.exp (I*((a*v:ℝ):ℂ))‖ ≤ |a| * v^2 := by
  have he : Complex.exp (I*(a:ℂ))*Complex.exp (I*((a*v:ℝ):ℂ)) =
      Complex.exp (I*((a*(1+v):ℝ):ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  calc
    _ ≤ |a*Real.exp v-a*(1+v)| := norm_pure_exp_sub_le _ _
    _ = |a| * |Real.exp v-1-v| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.abs_exp_sub_one_sub_id_le hv) (abs_nonneg _)

theorem additive_weighted_exp_linearization (a c v : ℝ)
    (hv : |v| ≤ 1) (hcv : |c*v| ≤ 1) :
    ‖(Real.exp (c*v):ℂ)*Complex.exp (I*((a*Real.exp v:ℝ):ℂ))-
      Complex.exp (I*(a:ℂ))*Complex.exp (I*((a*v:ℝ):ℂ))‖ ≤
      2* |c*v|+|a| * v^2 := by
  let E := Complex.exp (I*((a*Real.exp v:ℝ):ℂ))
  let F := Complex.exp (I*(a:ℂ))*Complex.exp (I*((a*v:ℝ):ℂ))
  have hE : ‖E‖ = 1 := by simp [E,Complex.norm_exp]
  have he : (Real.exp (c*v):ℂ)*E-F = ((Real.exp (c*v):ℂ)-1)*E+(E-F) := by ring
  change ‖(Real.exp (c*v):ℂ)*E-F‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖((Real.exp (c*v):ℂ)-1)*E‖+‖E-F‖ := norm_add_le _ _
    _ = |Real.exp (c*v)-1|+‖E-F‖ := by
      rw [norm_mul,hE,mul_one,← Complex.ofReal_one,← Complex.ofReal_sub,
        Complex.norm_real,Real.norm_eq_abs]
    _ ≤ _ := add_le_add (Real.abs_exp_sub_one_le hcv)
      (additive_exp_phase_linearization a v hv)

end
end Sechstmoment.Source
