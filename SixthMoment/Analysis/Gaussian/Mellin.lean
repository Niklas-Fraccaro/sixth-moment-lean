import Lean.Elab.Tactic.NormCast
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Tactic.LinearCombination
import SixthMoment.Analysis.Gaussian.Weight


namespace SixthMoment
open Complex Real MeasureTheory Set Filter
open scoped Topology
noncomputable section

def d02GaussianMellinIntegrand (y v : ℝ) : ℂ :=
  let z : ℂ := 1+(v : ℂ)*I
  Complex.exp (z^2-(y : ℂ)*z)/z

def d02GaussianMellin (y : ℝ) : ℂ :=
  (1/(2*Real.pi) : ℂ)*∫ v : ℝ, d02GaussianMellinIntegrand y v

def d02GaussianMellinV0 (x : ℝ) : ℂ :=
  (1/(2*Real.pi) : ℂ)*∫ v : ℝ,
    let z : ℂ := 1+(v : ℂ)*I
    Complex.exp (z^2)/z*(x : ℂ)^(-z)

private theorem d02MellinLine_norm_lower (v : ℝ) :
    1 ≤ ‖(1 : ℂ)+(v : ℂ)*I‖ := by
  simpa using Complex.abs_re_le_norm ((1 : ℂ)+(v : ℂ)*I)

private theorem d02MellinLine_ne_zero (v : ℝ) :
    (1 : ℂ)+(v : ℂ)*I ≠ 0 := by
  intro h
  have hh := d02MellinLine_norm_lower v
  rw [h, norm_zero] at hh
  linarith

private theorem d02MellinExponent_re (y v : ℝ) :
    (((1 : ℂ)+(v : ℂ)*I)^2-(y : ℂ)*(1+(v : ℂ)*I)).re = 1-y-v^2 := by
  (simp [pow_two, Complex.mul_re, Complex.mul_im]; ring)

theorem d02GaussianMellinIntegrand_norm_le (y v : ℝ) :
    ‖d02GaussianMellinIntegrand y v‖ ≤ Real.exp (1-y)*Real.exp (-v^2) := by
  unfold d02GaussianMellinIntegrand
  rw [norm_div, Complex.norm_exp, d02MellinExponent_re]
  calc
    _ ≤ Real.exp (1-y-v^2) := div_le_self (Real.exp_pos _).le (d02MellinLine_norm_lower v)
    _ = _ := by rw [← Real.exp_add]; congr 1

theorem d02GaussianMellinIntegrand_integrable (y : ℝ) :
    Integrable (d02GaussianMellinIntegrand y) := by
  apply (d02Gaussian_integrable.const_mul (Real.exp (1-y))).mono'
    (by
      unfold d02GaussianMellinIntegrand
      apply Continuous.aestronglyMeasurable
      exact (by fun_prop : Continuous (fun v : ℝ =>
        Complex.exp (((1 : ℂ)+(v : ℂ)*I)^2-(y : ℂ)*(1+(v : ℂ)*I)))).div
          (by fun_prop) d02MellinLine_ne_zero)
  exact Eventually.of_forall (d02GaussianMellinIntegrand_norm_le y)

private theorem d02GaussianMellinIntegrand_hasDeriv (y v : ℝ) :
    HasDerivAt (fun u : ℝ => d02GaussianMellinIntegrand u v)
      (-Complex.exp (((1 : ℂ)+(v : ℂ)*I)^2-(y : ℂ)*(1+(v : ℂ)*I))) y := by
  let z : ℂ := 1+(v : ℂ)*I
  have h := ((hasDerivAt_const y (z^2)).sub
    ((hasDerivAt_id y).ofReal_comp.mul_const z)).cexp.div_const z
  convert h using 1
  · rfl
  · dsimp [z]
    field_simp [d02MellinLine_ne_zero v]
    ring

theorem d02GaussianMellin_norm_le (y : ℝ) :
    ‖d02GaussianMellin y‖ ≤
      (Real.sqrt Real.pi/(2*Real.pi))*Real.exp (1-y) := by
  have hi : ‖∫ v : ℝ, d02GaussianMellinIntegrand y v‖ ≤
      Real.exp (1-y)*Real.sqrt Real.pi := by
    calc
      _ ≤ ∫ v : ℝ, Real.exp (1-y)*Real.exp (-v^2) :=
        norm_integral_le_of_norm_le (d02Gaussian_integrable.const_mul _)
          (Eventually.of_forall (d02GaussianMellinIntegrand_norm_le y))
      _ = _ := by rw [integral_const_mul, d02Gaussian_total_mass]
  unfold d02GaussianMellin
  rw [norm_mul]
  have hp : ‖(1/(2*Real.pi) : ℂ)‖ = 1/(2*Real.pi) := by
    simp [Complex.norm_real, abs_of_pos Real.pi_pos]
  rw [hp]
  calc
    _ ≤ (1/(2*Real.pi))*(Real.exp (1-y)*Real.sqrt Real.pi) := by gcongr
    _ = _ := by ring

private theorem d02GaussianMellin_density_integral (y : ℝ) :
    (∫ v : ℝ, Complex.exp (((1 : ℂ)+(v : ℂ)*I)^2-(y : ℂ)*(1+(v : ℂ)*I))) =
      (Real.sqrt Real.pi : ℂ)*Complex.exp (-(y : ℂ)^2/4) := by
  have h := integral_cexp_quadratic (b := (-1 : ℂ)) (by norm_num)
    ((2-(y : ℂ))*I) (1-(y : ℂ))
  have he (v : ℝ) :
      ((1 : ℂ)+(v : ℂ)*I)^2-(y : ℂ)*(1+(v : ℂ)*I) =
        (-1 : ℂ)*(v : ℂ)^2+((2-(y : ℂ))*I)*(v : ℂ)+(1-(y : ℂ)) := by
    ring_nf
    (simp [I_sq]; ring)
  simp_rw [he]
  rw [h]
  have hsqrt : (Real.pi : ℂ)^(1/2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
    norm_num
  have hexp : (1-(y : ℂ))-((2-(y : ℂ))*I)^2/(4*(-1)) = -(y : ℂ)^2/4 := by
    ring_nf
    (simp [I_sq]; ring)
  simp only [neg_neg, div_one]
  rw [hsqrt, hexp]

theorem d02GaussianMellin_hasDeriv (y : ℝ) :
    HasDerivAt d02GaussianMellin
      (-(1/(2*Real.sqrt Real.pi) : ℂ)*Complex.exp (-(y : ℂ)^2/4)) y := by
  let F' : ℝ → ℝ → ℂ := fun u v =>
    -Complex.exp (((1 : ℂ)+(v : ℂ)*I)^2-(u : ℂ)*(1+(v : ℂ)*I))
  let B : ℝ → ℝ := fun v => Real.exp (2-y)*Real.exp (-v^2)
  have hB : Integrable B := d02Gaussian_integrable.const_mul _
  have hbound : ∀ᵐ v : ℝ, ∀ u ∈ Ioo (y-1) (y+1), ‖F' u v‖ ≤ B v := by
    filter_upwards [] with v
    intro u hu
    dsimp [F', B]
    rw [norm_neg, Complex.norm_exp, d02MellinExponent_re, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hu.1]
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := d02GaussianMellinIntegrand) (F' := F') (bound := B)
    (Ioo_mem_nhds (by linarith : y-1 < y) (by linarith : y < y+1))
    (Eventually.of_forall (fun u => (d02GaussianMellinIntegrand_integrable u).aestronglyMeasurable))
    (d02GaussianMellinIntegrand_integrable y)
    (by dsimp [F']; fun_prop) hbound hB
    (Eventually.of_forall (fun v u _ => d02GaussianMellinIntegrand_hasDeriv u v))
  have hh := h.2.const_mul (1/(2*Real.pi) : ℂ)
  change HasDerivAt d02GaussianMellin _ y at hh
  dsimp [F'] at hh
  rw [integral_neg, d02GaussianMellin_density_integral] at hh
  convert hh using 1
  have hs : (Real.sqrt Real.pi : ℂ)^2 = (Real.pi : ℂ) := by
    norm_cast
    exact Real.sq_sqrt Real.pi_pos.le
  have hsn : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 Real.pi_pos).ne'
  field_simp
  rw [← hs]

theorem d02GaussianMellin_tendsto_zero :
    Tendsto d02GaussianMellin atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have he : Tendsto (fun y : ℝ => Real.exp (1-y)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    apply (tendsto_atBot_add_const_left atTop 1 tendsto_neg_atTop_atBot).congr
    intro u
    ring
  have hh := he.const_mul (Real.sqrt Real.pi/(2*Real.pi))
  simp only [mul_zero] at hh
  exact squeeze_zero (fun _ => norm_nonneg _) d02GaussianMellin_norm_le hh

theorem d02GaussianMellin_eq_tail (y : ℝ) :
    d02GaussianMellin y = (d02GaussianTail (y/2) : ℂ) := by
  let d : ℝ → ℂ := fun u =>
    -(1/(2*Real.sqrt Real.pi) : ℂ)*Complex.exp (-(u : ℂ)^2/4)
  have hd : Integrable d := by
    convert ((integrable_exp_neg_mul_sq (b := (1/4 : ℝ)) (by norm_num)).ofReal).const_mul
      (-(1/(2*Real.sqrt Real.pi) : ℂ)) using 1
    ext u
    dsimp [d]
    rw [Complex.ofReal_exp]
    apply congrArg (fun w : ℂ => -(1/(2*Real.sqrt Real.pi) : ℂ)*Complex.exp w)
    push_cast
    ring
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := y) (f := d02GaussianMellin) (f' := d)
    (fun u _ => d02GaussianMellin_hasDeriv u) hd.integrableOn d02GaussianMellin_tendsto_zero
  dsimp [d] at hi
  rw [integral_const_mul] at hi
  have hg : (∫ u in Ioi y, Complex.exp (-(u : ℂ)^2/4)) =
      (2 : ℂ)*((∫ v in Ioi (y/2), Real.exp (-v^2) : ℝ) : ℂ) := by
    have h := integral_comp_mul_left_Ioi (fun v : ℝ => Real.exp (-v^2)) y
      (by norm_num : (0 : ℝ)<1/2)
    have h' : (∫ u in Ioi y, Real.exp (-(u/2)^2)) =
        2*(∫ v in Ioi (y/2), Real.exp (-v^2)) := by
      convert h using 1 <;> norm_num [smul_eq_mul, div_eq_mul_inv, mul_comm]
    have hc : (∫ u in Ioi y, Complex.exp (-(u : ℂ)^2/4)) =
        ((∫ u in Ioi y, Real.exp (-(u/2)^2) : ℝ) : ℂ) := by
      calc
        _ = ∫ u in Ioi y, (Real.exp (-(u/2)^2) : ℂ) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro u _
          dsimp only
          rw [Complex.ofReal_exp]
          apply congrArg Complex.exp
          push_cast
          ring
        _ = _ := _root_.integral_ofReal
    rw [hc, h']
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [hg] at hi
  unfold d02GaussianTail
  push_cast
  have hsn : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 Real.pi_pos).ne'
  field_simp at hi ⊢
  linear_combination hi

theorem d02GaussianMellinV0_eq_gaussianV0 {x : ℝ} (hx : 0 < x) :
    d02GaussianMellinV0 x = (d02GaussianV0 x : ℂ) := by
  have he : d02GaussianMellinV0 x = d02GaussianMellin (Real.log x) := by
    unfold d02GaussianMellinV0 d02GaussianMellin d02GaussianMellinIntegrand
    congr 1
    apply integral_congr_ae
    filter_upwards [] with v
    dsimp only
    have hc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    rw [Complex.cpow_def_of_ne_zero hc, Complex.ofReal_log hx.le]
    calc
      _ = (Complex.exp (((1 : ℂ)+(v : ℂ)*I)^2)*
        Complex.exp (Complex.log (x : ℂ)*(-((1 : ℂ)+(v : ℂ)*I)))) /
          ((1 : ℂ)+(v : ℂ)*I) := by ring
      _ = _ := by
        rw [← Complex.exp_add]
        apply congrArg (fun w : ℂ => Complex.exp w/((1 : ℂ)+(v : ℂ)*I))
        ring
  rw [he, d02GaussianMellin_eq_tail]
  rfl

end
end SixthMoment
