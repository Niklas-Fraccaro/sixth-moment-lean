import Mathlib.Analysis.Calculus.MeanValue
import SixthMoment.Analysis.Gaussian.Mellin


namespace SixthMoment
open Complex Real MeasureTheory Set Filter
open scoped Topology
noncomputable section

def d02GaussianMellinIntegrandOnLine (c y v : ℝ) : ℂ :=
  let z : ℂ := (c : ℂ)+(v : ℂ)*I
  Complex.exp (z^2-(y : ℂ)*z)/z

def d02GaussianMellinOnLine (c y : ℝ) : ℂ :=
  (1/(2*Real.pi) : ℂ)*∫ v : ℝ, d02GaussianMellinIntegrandOnLine c y v

def d02GaussianMellinV0OnLine (c x : ℝ) : ℂ :=
  (1/(2*Real.pi) : ℂ)*∫ v : ℝ,
    let z : ℂ := (c : ℂ)+(v : ℂ)*I
    Complex.exp (z^2)/z*(x : ℂ)^(-z)

private theorem d02GaussianLine_norm_lower (c v : ℝ) :
    c ≤ ‖(c : ℂ)+(v : ℂ)*I‖ := by
  simpa using Complex.re_le_norm ((c : ℂ)+(v : ℂ)*I)

private theorem d02GaussianLine_ne_zero {c : ℝ} (hc : 0 < c) (v : ℝ) :
    (c : ℂ)+(v : ℂ)*I ≠ 0 := by
  intro h
  have hh := d02GaussianLine_norm_lower c v
  simp only [h, norm_zero] at hh
  linarith

private theorem d02GaussianLineExponent_re (c y v : ℝ) :
    (((c : ℂ)+(v : ℂ)*I)^2-(y : ℂ)*((c : ℂ)+(v : ℂ)*I)).re =
      c^2-y*c-v^2 := by
  (simp [pow_two, Complex.mul_re, Complex.mul_im]; ring)

theorem d02GaussianMellinIntegrandOnLine_norm_le {c : ℝ} (hc : 0 < c) (y v : ℝ) :
    ‖d02GaussianMellinIntegrandOnLine c y v‖ ≤
      (Real.exp (c^2-y*c)/c)*Real.exp (-v^2) := by
  unfold d02GaussianMellinIntegrandOnLine
  rw [norm_div, Complex.norm_exp, d02GaussianLineExponent_re]
  calc
    _ ≤ Real.exp (c^2-y*c-v^2)/c := div_le_div_of_nonneg_left
      (Real.exp_pos _).le hc (d02GaussianLine_norm_lower c v)
    _ = _ := by rw [show c^2-y*c-v^2 = (c^2-y*c)+(-v^2) by ring, Real.exp_add]; ring

theorem d02GaussianMellinIntegrandOnLine_integrable {c : ℝ} (hc : 0 < c) (y : ℝ) :
    Integrable (d02GaussianMellinIntegrandOnLine c y) := by
  apply (d02Gaussian_integrable.const_mul (Real.exp (c^2-y*c)/c)).mono'
    (by
      unfold d02GaussianMellinIntegrandOnLine
      apply Continuous.aestronglyMeasurable
      exact (by fun_prop : Continuous (fun v : ℝ =>
        Complex.exp (((c : ℂ)+(v : ℂ)*I)^2-(y : ℂ)*((c : ℂ)+(v : ℂ)*I)))).div
          (by fun_prop) (d02GaussianLine_ne_zero hc))
  exact Eventually.of_forall (d02GaussianMellinIntegrandOnLine_norm_le hc y)

private theorem d02GaussianMellinIntegrandOnLine_hasDeriv {c : ℝ} (hc : 0 < c) (y v : ℝ) :
    HasDerivAt (fun u : ℝ => d02GaussianMellinIntegrandOnLine c u v)
      (-Complex.exp (((c : ℂ)+(v : ℂ)*I)^2-(y : ℂ)*((c : ℂ)+(v : ℂ)*I))) y := by
  let z : ℂ := (c : ℂ)+(v : ℂ)*I
  have h := ((hasDerivAt_const y (z^2)).sub
    ((hasDerivAt_id y).ofReal_comp.mul_const z)).cexp.div_const z
  convert h using 1
  · rfl
  · dsimp [z]
    field_simp [d02GaussianLine_ne_zero hc v]
    ring

private theorem d02GaussianMellinOnLine_density_integral (c y : ℝ) :
    (∫ v : ℝ, Complex.exp (((c : ℂ)+(v : ℂ)*I)^2-(y : ℂ)*((c : ℂ)+(v : ℂ)*I))) =
      (Real.sqrt Real.pi : ℂ)*Complex.exp (-(y : ℂ)^2/4) := by
  have h := integral_cexp_quadratic (b := (-1 : ℂ)) (by norm_num)
    ((2*(c : ℂ)-(y : ℂ))*I) ((c : ℂ)^2-(y : ℂ)*(c : ℂ))
  have he (v : ℝ) :
      ((c : ℂ)+(v : ℂ)*I)^2-(y : ℂ)*((c : ℂ)+(v : ℂ)*I) =
        (-1 : ℂ)*(v : ℂ)^2+((2*(c : ℂ)-(y : ℂ))*I)*(v : ℂ)+
          ((c : ℂ)^2-(y : ℂ)*(c : ℂ)) := by
    ring_nf
    (simp [I_sq]; ring)
  simp_rw [he]
  rw [h]
  have hsqrt : (Real.pi : ℂ)^(1/2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
    norm_num
  have hexp : ((c : ℂ)^2-(y : ℂ)*(c : ℂ))-
      ((2*(c : ℂ)-(y : ℂ))*I)^2/(4*(-1)) = -(y : ℂ)^2/4 := by
    ring_nf
    (simp [I_sq]; ring)
  simp only [neg_neg, div_one]
  rw [hsqrt, hexp]

theorem d02GaussianMellinOnLine_hasDeriv {c : ℝ} (hc : 0 < c) (y : ℝ) :
    HasDerivAt (d02GaussianMellinOnLine c)
      (-(1/(2*Real.sqrt Real.pi) : ℂ)*Complex.exp (-(y : ℂ)^2/4)) y := by
  let F' : ℝ → ℝ → ℂ := fun u v =>
    -Complex.exp (((c : ℂ)+(v : ℂ)*I)^2-(u : ℂ)*((c : ℂ)+(v : ℂ)*I))
  let B : ℝ → ℝ := fun v => Real.exp (c^2+c*(1-y))*Real.exp (-v^2)
  have hB : Integrable B := d02Gaussian_integrable.const_mul _
  have hbound : ∀ᵐ v : ℝ, ∀ u ∈ Ioo (y-1) (y+1), ‖F' u v‖ ≤ B v := by
    filter_upwards [] with v
    intro u hu
    dsimp [F', B]
    rw [norm_neg, Complex.norm_exp, d02GaussianLineExponent_re, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hu.1]
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := d02GaussianMellinIntegrandOnLine c) (F' := F') (bound := B)
    (Ioo_mem_nhds (by linarith : y-1 < y) (by linarith : y < y+1))
    (Eventually.of_forall (fun u =>
      (d02GaussianMellinIntegrandOnLine_integrable hc u).aestronglyMeasurable))
    (d02GaussianMellinIntegrandOnLine_integrable hc y)
    (by dsimp [F']; fun_prop) hbound hB
    (Eventually.of_forall (fun v u _ => d02GaussianMellinIntegrandOnLine_hasDeriv hc u v))
  have hh := h.2.const_mul (1/(2*Real.pi) : ℂ)
  change HasDerivAt (d02GaussianMellinOnLine c) _ y at hh
  dsimp [F'] at hh
  rw [integral_neg, d02GaussianMellinOnLine_density_integral] at hh
  convert hh using 1
  have hs : (Real.sqrt Real.pi : ℂ)^2 = (Real.pi : ℂ) := by
    norm_cast
    exact Real.sq_sqrt Real.pi_pos.le
  have hsn : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 Real.pi_pos).ne'
  field_simp
  rw [← hs]

theorem d02GaussianMellinOnLine_norm_le {c : ℝ} (hc : 0 < c) (y : ℝ) :
    ‖d02GaussianMellinOnLine c y‖ ≤
      (Real.sqrt Real.pi/(2*Real.pi*c))*Real.exp (c^2-y*c) := by
  have hi : ‖∫ v : ℝ, d02GaussianMellinIntegrandOnLine c y v‖ ≤
      (Real.exp (c^2-y*c)/c)*Real.sqrt Real.pi := by
    calc
      _ ≤ ∫ v : ℝ, (Real.exp (c^2-y*c)/c)*Real.exp (-v^2) :=
        norm_integral_le_of_norm_le (d02Gaussian_integrable.const_mul _)
          (Eventually.of_forall (d02GaussianMellinIntegrandOnLine_norm_le hc y))
      _ = _ := by rw [integral_const_mul, d02Gaussian_total_mass]
  unfold d02GaussianMellinOnLine
  rw [norm_mul]
  have hp : ‖(1/(2*Real.pi) : ℂ)‖ = 1/(2*Real.pi) := by
    simp [Complex.norm_real, abs_of_pos Real.pi_pos]
  rw [hp]
  calc
    _ ≤ (1/(2*Real.pi))*((Real.exp (c^2-y*c)/c)*Real.sqrt Real.pi) := by gcongr
    _ = _ := by ring

theorem d02GaussianMellinOnLine_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (d02GaussianMellinOnLine c) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have he : Tendsto (fun y : ℝ => Real.exp (c^2-y*c)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    have h := tendsto_atBot_add_const_left atTop (c^2)
      (tendsto_id.atTop_mul_const_of_neg (by linarith : -c < 0))
    simpa only [sub_eq_add_neg, mul_neg, id_eq] using h
  have hh := he.const_mul (Real.sqrt Real.pi/(2*Real.pi*c))
  simp only [mul_zero] at hh
  exact squeeze_zero (fun _ => norm_nonneg _) (d02GaussianMellinOnLine_norm_le hc) hh

theorem d02GaussianMellinOnLine_eq_line_one {c : ℝ} (hc : 0 < c) (y : ℝ) :
    d02GaussianMellinOnLine c y = d02GaussianMellin y := by
  let f : ℝ → ℂ := fun u => d02GaussianMellinOnLine c u-d02GaussianMellin u
  have hd (u : ℝ) : HasDerivAt f 0 u := by
    convert (d02GaussianMellinOnLine_hasDeriv hc u).sub (d02GaussianMellin_hasDeriv u) using 1
    simp
  have hconst (u v : ℝ) : f u = f v := is_const_of_deriv_eq_zero
    (fun z => (hd z).differentiableAt) (fun z => (hd z).deriv) u v
  have ht : Tendsto f atTop (𝓝 0) := by
    simpa only [sub_self] using
      (d02GaussianMellinOnLine_tendsto_zero hc).sub d02GaussianMellin_tendsto_zero
  have ht' : Tendsto f atTop (𝓝 (f y)) :=
    tendsto_const_nhds.congr (fun u => (hconst u y).symm)
  have hz : f y = 0 := tendsto_nhds_unique ht' ht
  exact sub_eq_zero.mp hz

theorem d02GaussianMellinOnLine_eq_tail {c : ℝ} (hc : 0 < c) (y : ℝ) :
    d02GaussianMellinOnLine c y = (d02GaussianTail (y/2) : ℂ) := by
  rw [d02GaussianMellinOnLine_eq_line_one hc, d02GaussianMellin_eq_tail]

theorem d02GaussianMellinV0OnLine_eq_gaussianV0 {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    d02GaussianMellinV0OnLine c x = (d02GaussianV0 x : ℂ) := by
  have he : d02GaussianMellinV0OnLine c x = d02GaussianMellinOnLine c (Real.log x) := by
    unfold d02GaussianMellinV0OnLine d02GaussianMellinOnLine d02GaussianMellinIntegrandOnLine
    congr 1
    apply integral_congr_ae
    filter_upwards [] with v
    dsimp only
    have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    rw [Complex.cpow_def_of_ne_zero hx', Complex.ofReal_log hx.le]
    calc
      _ = (Complex.exp (((c : ℂ)+(v : ℂ)*I)^2)*
        Complex.exp (Complex.log (x : ℂ)*(-((c : ℂ)+(v : ℂ)*I)))) /
          ((c : ℂ)+(v : ℂ)*I) := by ring
      _ = _ := by
        rw [← Complex.exp_add]
        apply congrArg (fun w : ℂ => Complex.exp w/((c : ℂ)+(v : ℂ)*I))
        ring
  rw [he, d02GaussianMellinOnLine_eq_tail hc]
  rfl

end
end SixthMoment
