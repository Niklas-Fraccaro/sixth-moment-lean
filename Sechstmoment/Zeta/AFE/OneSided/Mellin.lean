import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Sechstmoment.Zeta.AFE.Two.DirichletInterchange
import Sechstmoment.Zeta.Gamma.MellinBounds


namespace Sechstmoment
open Complex Real MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section

def d04MellinLine (v : ℝ) : ℂ := (2 : ℂ)+(v : ℂ)*I

@[simp] theorem d04MellinLine_re (v : ℝ) : (d04MellinLine v).re = 2 := by
  simp [d04MellinLine]

@[simp] theorem d04MellinLine_im (v : ℝ) : (d04MellinLine v).im = v := by
  simp [d04MellinLine]

private theorem d04MellinLine_ne_zero (v : ℝ) : d04MellinLine v ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num at this

private theorem d04MellinLine_add_one_ne_zero (v : ℝ) : d04MellinLine v+1 ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num at this

theorem d04Gamma_line_two_norm_le (v : ℝ) :
    ‖Complex.Gamma (d04MellinLine v)‖ ≤ 6*(1+v^2)⁻¹ := by
  let z := d04MellinLine v
  have hΓ : ‖Complex.Gamma (z+2)‖ ≤ 6 := by
    have h := gamma_norm_le_realGamma_re (s := z+2) (by simp [z])
    have h4 : Real.Gamma 4 = 6 := by
      norm_num [show (4 : ℝ)=(3 : ℕ)+1 by norm_num, Real.Gamma_nat_eq_factorial]
    simpa only [z, Complex.add_re, d04MellinLine_re,
      show (2 : ℂ).re=2 from rfl, show (2 : ℝ)+2=4 by norm_num, h4] using h
  have hsq : ‖z‖^2 = 4+v^2 := by
    rw [Complex.sq_norm]
    simp [z, d04MellinLine, Complex.normSq_apply]
    ring
  have hsq' : ‖z+1‖^2 = 9+v^2 := by
    rw [Complex.sq_norm]
    simp [z, d04MellinLine, Complex.normSq_apply]
    ring
  have hn : ‖z‖ ≤ ‖z+1‖ := by
    nlinarith [norm_nonneg z, norm_nonneg (z+1)]
  have hp : 1+v^2 ≤ ‖z+1‖*‖z‖ := by
    have hm := mul_le_mul_of_nonneg_right hn (norm_nonneg z)
    nlinarith
  have hrec : Complex.Gamma (z+2) = (z+1)*z*Complex.Gamma z := by
    rw [show z+2=(z+1)+1 by ring,
      Complex.Gamma_add_one _ (d04MellinLine_add_one_ne_zero v),
      Complex.Gamma_add_one _ (d04MellinLine_ne_zero v)]
    ring
  rw [hrec, norm_mul, norm_mul] at hΓ
  have hh := mul_le_mul_of_nonneg_right hp (norm_nonneg (Complex.Gamma z))
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0<1+v^2)]
  dsimp [z] at *
  nlinarith

theorem d04Gamma_line_two_integrable :
    Integrable (fun v : ℝ => Complex.Gamma (d04MellinLine v)) := by
  apply (integrable_inv_one_add_sq.const_mul (6 : ℝ)).mono'
  · apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    intro v
    apply (Complex.continuousAt_Gamma _ ?_).comp
      (by unfold d04MellinLine; fun_prop)
    intro n hn
    have h := congrArg Complex.re hn
    simp only [d04MellinLine_re, Complex.neg_re, Complex.natCast_re] at h
    have hn0 : (0 : ℝ)≤n := Nat.cast_nonneg n
    linarith
  · exact Eventually.of_forall d04Gamma_line_two_norm_le

private theorem d04Mellin_exp_eq_Gamma {s : ℂ} (hs : 0<s.re) :
    mellin (fun x : ℝ => (Real.exp (-x) : ℂ)) s = Complex.Gamma s := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral, mellin]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only [smul_eq_mul]
  ring

theorem d04GammaMellin_exponential {x : ℝ} (hx : 0<x) :
    (1/(2*Real.pi) : ℂ)*∫ v : ℝ,
      (x : ℂ)^(-d04MellinLine v)*Complex.Gamma (d04MellinLine v) =
      (Real.exp (-x) : ℂ) := by
  have hconv : MellinConvergent (fun x : ℝ => (Real.exp (-x) : ℂ)) (2 : ℂ) := by
    simpa only [MellinConvergent, smul_eq_mul, mul_comm] using
      (Complex.GammaIntegral_convergent (s := (2 : ℂ)) (by norm_num))
  have hvertical : VerticalIntegrable
      (mellin (fun x : ℝ => (Real.exp (-x) : ℂ))) 2 := by
    change Integrable (fun v : ℝ => mellin (fun x : ℝ => (Real.exp (-x) : ℂ))
      (d04MellinLine v))
    have he (v : ℝ) : mellin (fun x : ℝ => (Real.exp (-x) : ℂ))
        (d04MellinLine v)=Complex.Gamma (d04MellinLine v) :=
      d04Mellin_exp_eq_Gamma (by simp)
    simp_rw [he]
    exact d04Gamma_line_two_integrable
  have h := mellinInv_mellin_eq 2 (fun x : ℝ => (Real.exp (-x) : ℂ))
    hx hconv hvertical (by fun_prop)
  have he (v : ℝ) : mellin (fun x : ℝ => (Real.exp (-x) : ℂ))
      (d04MellinLine v)=Complex.Gamma (d04MellinLine v) :=
    d04Mellin_exp_eq_Gamma (by simp)
  simp only [mellinInv, smul_eq_mul, real_smul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat] at h
  change (1/(2*Real.pi) : ℂ)*∫ v : ℝ, (x : ℂ)^(-d04MellinLine v)*
    mellin (fun x : ℝ => (Real.exp (-x) : ℂ)) (d04MellinLine v) = _ at h
  simp_rw [he] at h
  exact h

end
end Sechstmoment
