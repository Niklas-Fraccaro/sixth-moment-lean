import SixthMoment.Zeta.Bounds.MellinZetaGrowth
import SixthMoment.Zeta.DirichletL.DivisorSeries


namespace SixthMoment.Source
open Complex Real MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section

theorem gammaR_norm_bound {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gammaℝ z‖ ≤ Real.pi^(-z.re/2)*Real.Gamma (z.re/2) := by
  rw [Complex.Gammaℝ_def, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  simp only [Complex.div_ofNat_re, neg_re]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [Complex.div_ofNat_re] using gamma_norm_le_realGamma_re
    (s := z/2) (by simp only [Complex.div_ofNat_re]; linarith)

theorem gammaR_continuousAt {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt Complex.Gammaℝ z := by
  have h := (Complex.differentiable_Gammaℝ_inv z).continuousAt.inv₀
    (inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hz))
  change ContinuousAt (fun s : ℂ => ((Complex.Gammaℝ s)⁻¹)⁻¹) z at h
  simpa only [inv_inv] using h

theorem conductorGammaFactor_continuousAt {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt (conductorGammaFactor χ) z := by
  classical
  unfold conductorGammaFactor DirichletCharacter.gammaFactor
  apply ContinuousAt.mul (by fun_prop)
  split_ifs
  · exact gammaR_continuousAt hz
  · exact ContinuousAt.comp (f := fun w : ℂ => w+1) (g := Complex.Gammaℝ)
      (gammaR_continuousAt (show 0 < (z+1).re by simpa using (by linarith : 0 < z.re+1)))
      (by fun_prop)

theorem conductorGammaFactor_vertical_bound {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (c : ℝ) (hc : 0 < c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, z.re = c → ‖conductorGammaFactor χ z‖ ≤ B := by
  classical
  let B₀ := Real.pi^(-c/2)*Real.Gamma (c/2)
  let B₁ := Real.pi^(-(c+1)/2)*Real.Gamma ((c+1)/2)
  have hB₀ : 0 ≤ B₀ := mul_nonneg (by positivity) (Real.Gamma_pos_of_pos (by linarith)).le
  refine ⟨(N : ℝ)^(c/2)*max B₀ B₁, by positivity, ?_⟩
  intro z hz
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [conductorGammaFactor, norm_mul,
    show (N : ℂ) = ((N : ℝ) : ℂ) by norm_cast,
    Complex.norm_cpow_eq_rpow_re_of_pos hN, Complex.div_ofNat_re, hz]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold DirichletCharacter.gammaFactor
  split_ifs
  · exact (gammaR_norm_bound (by simpa only [hz] using hc)).trans (by
      rw [hz]; exact le_max_left _ _)
  · have hz' : (z+1).re = c+1 := by simp [hz]
    exact (gammaR_norm_bound (by rw [hz']; linarith)).trans (by
      rw [hz']; exact le_max_right _ _)

def dirichletSquareKernel {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s w : ℂ) : ℂ :=
  Complex.exp (w^2) * (conductorGammaFactor χ (s+w)/conductorGammaFactor χ s)^2/w

theorem dirichletSquareKernel_vertical_integrable {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun v : ℝ => dirichletSquareKernel χ s (2+(v : ℂ)*I)) := by
  obtain ⟨B,hB,hbound⟩ := conductorGammaFactor_vertical_bound χ (s.re+2) (by linarith)
  have hgauss : Integrable (fun v : ℝ => Real.exp (-v^2)) := by
    simpa using gaussianPolynomialExponential_integrable 0 0
  apply (hgauss.const_mul (Real.exp 4*(B/‖conductorGammaFactor χ s‖)^2)).mono'
  · have hγ : Continuous (fun v : ℝ => conductorGammaFactor χ (s+(2+(v : ℂ)*I))) := by
      apply continuous_iff_continuousAt.mpr
      intro v
      exact (conductorGammaFactor_continuousAt χ (by simp; linarith)).comp (by fun_prop)
    apply Continuous.aestronglyMeasurable
    unfold dirichletSquareKernel
    exact (by fun_prop : Continuous (fun v : ℝ => Complex.exp ((2+(v : ℂ)*I)^2))).mul
      (hγ.div_const _ |>.pow 2) |>.div (by fun_prop) (fun v => by
        intro h; have hr := congrArg Complex.re h; norm_num at hr)
  · apply Eventually.of_forall
    intro v
    have hnum := hbound (s+(2+(v : ℂ)*I)) (by simp)
    have hden : 1 ≤ ‖(2 : ℂ)+(v : ℂ)*I‖ := by
      have h := Complex.abs_re_le_norm ((2 : ℂ)+(v : ℂ)*I)
      norm_num at h
      linarith
    have he : ‖Complex.exp ((2+(v : ℂ)*I)^2)‖ = Real.exp 4*Real.exp (-v^2) := by
      rw [Complex.norm_exp, ← Real.exp_add]
      congr 1
      norm_num [pow_two, sub_eq_add_neg]
    rw [dirichletSquareKernel, norm_div, norm_mul, norm_pow, norm_div, he]
    apply (div_le_self (by positivity) hden).trans
    calc
      _ ≤ (Real.exp 4*Real.exp (-v^2))*(B/‖conductorGammaFactor χ s‖)^2 := by gcongr
      _ = _ := by ring

theorem dirichletSquareLIntegral_eq_kernel_integral {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    dirichletSquareLIntegral χ s =
      (∫ v : ℝ, dirichletSquareKernel χ s (2+(v : ℂ)*I)*
        (χ.LFunction (s+(2+(v : ℂ)*I)))^2)/(2*Real.pi : ℂ) := by
  unfold dirichletSquareLIntegral dirichletSquareCompletedIntegral
  rw [div_right_comm, ← integral_div]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun v => by
    dsimp only
    have hpos : 0 < (s+(2+(v : ℂ)*I)).re := by simp; linarith
    rw [dirichletSquareContour, conductorCompletedL_eq_gamma_mul_L χ hpos]
    unfold dirichletSquareKernel
    ring

def dirichletSquareSeriesWeight {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) (n : ℕ) : ℂ :=
  (∫ v : ℝ, dirichletSquareKernel χ s (2+(v : ℂ)*I)*
    (n : ℂ)^(-(2+(v : ℂ)*I)))/(2*Real.pi : ℂ)

theorem lSeriesTerm_add (f : ℕ → ℂ) (s w : ℂ) (n : ℕ) :
    LSeries.term f (s+w) n = LSeries.term f s n * (n : ℂ)^(-w) := by
  by_cases hn : n = 0
  · simp [hn]
  · have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simp only [LSeries.term_of_ne_zero hn, Complex.cpow_add _ _ hn', Complex.cpow_neg]
    ring

theorem dirichletSquareLIntegral_hasSum {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun n : ℕ => LSeries.term (dirichletDivisorCoefficients χ) s n *
      dirichletSquareSeriesWeight χ s n) (dirichletSquareLIntegral χ s) := by
  have hs' : 1 < (s+2).re := by simp; linarith
  have h := lSeries_vertical_integral_hasSum (dirichletDivisorCoefficients χ) (s+2)
    (dirichletL_square_hasSum χ hs').summable _ (dirichletSquareKernel_vertical_integrable χ hs)
  have he (v : ℝ) : LSeries (dirichletDivisorCoefficients χ) (s+2+(v : ℂ)*I) =
      (χ.LFunction (s+(2+(v : ℂ)*I)))^2 := by
    rw [← add_assoc]
    exact (dirichletL_square_hasSum χ (by simp; linarith)).tsum_eq
  simp_rw [he] at h
  have hdiv := h.div_const (2*Real.pi : ℂ)
  rw [← dirichletSquareLIntegral_eq_kernel_integral χ hs] at hdiv
  convert hdiv using 1
  funext n
  unfold dirichletSquareSeriesWeight
  rw [← mul_div_assoc, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun v => by
    dsimp only
    rw [show s+2+(v : ℂ)*I = s+(2+(v : ℂ)*I) by ring, lSeriesTerm_add]
    ring

theorem dirichletL_square_eq_smooth_series {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hprim : χ.IsPrimitive)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    (χ.LFunction s)^2 =
      (∑' n : ℕ, LSeries.term (dirichletDivisorCoefficients χ) s n *
        dirichletSquareSeriesWeight χ s n) +
      (dirichletSquareDualFactor χ s)^2 *
        (∑' n : ℕ, LSeries.term (dirichletDivisorCoefficients χ⁻¹) (1-s) n *
          dirichletSquareSeriesWeight χ⁻¹ (1-s) n) := by
  rw [(dirichletSquareLIntegral_hasSum χ hs0).tsum_eq,
    (dirichletSquareLIntegral_hasSum χ⁻¹ (by simp; linarith : 0 < (1-s).re)).tsum_eq]
  exact dirichletL_square_smooth_decomposition χ hχ hprim hs0 hs1

end
end SixthMoment.Source
