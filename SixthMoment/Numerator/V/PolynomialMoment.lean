import SixthMoment.Numerator.V.Asymptotic.VGeneratorLeading
import SixthMoment.Numerator.V.DP.VPolynomialAsymptotic


namespace SixthMoment.Source
open Complex Real Set MeasureTheory Filter Metric
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem noDP_disk_uniform_derivative_tendsto (F : ℝ → ℂ → ℂ) (G : ℂ → ℂ)
    (hF : ∀ᶠ T : ℝ in atTop, DifferentiableOn ℂ (F T) (ball (0:ℂ) 4))
    (hG : DifferentiableOn ℂ G (ball (0:ℂ) 4))
    (hB : ∀ r : ℝ, 0 < r → ∀ᶠ T : ℝ in atTop,
      ∀ z : ℂ, ‖z‖ ≤ 4 → ‖F T z-G z‖ < r)
    (n : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 2) :
    Tendsto (fun T : ℝ => iteratedDeriv n (F T) z) atTop (𝓝 (iteratedDeriv n G z)) := by
  have hclosed : closedBall z 1 ⊆ ball (0:ℂ) 4 := by
    intro w hw
    have hwn : ‖w-z‖ ≤ 1 := by simpa only [mem_closedBall,dist_eq_norm] using hw
    have hn : ‖w‖ ≤ ‖w-z‖+‖z‖ := by convert norm_add_le (w-z) z using 1; simp
    have hw4 : ‖w‖ < 4 := by linarith
    simpa only [mem_ball,dist_zero_right] using hw4
  have hN : 0 < (n.factorial:ℝ) := by positivity
  apply Metric.tendsto_nhds.2
  intro r hr
  filter_upwards [hF,hB (r/(2*(n.factorial:ℝ))) (by positivity)] with T hd hb
  have hf := (hd.mono hclosed).diffContOnCl_ball Subset.rfl
  have hg := (hG.mono hclosed).diffContOnCl_ball Subset.rfl
  have hh := cauchy_iteratedDeriv_bound n (by norm_num : (0:ℝ) < 1) (hf.sub hg)
    (show ∀ w ∈ sphere z 1, ‖F T w-G w‖ ≤ r/(2*(n.factorial:ℝ)) from by
      intro w hw
      have hmem := hclosed (sphere_subset_closedBall hw)
      have hn : ‖w‖ ≤ 4 :=
        (show ‖w‖ < 4 by simpa only [mem_ball,dist_zero_right] using hmem).le
      exact (hb w hn).le)
  change ‖iteratedDeriv n (fun w : ℂ => F T w-G w) z‖ ≤
    (n.factorial:ℝ)/1^n*(r/(2*(n.factorial:ℝ))) at hh
  rw [iteratedDeriv_sub_of_diffContOnCl n (by norm_num : (0:ℝ) < 1) hf hg] at hh
  simp only [one_pow,div_one] at hh
  rw [dist_eq_norm]
  apply hh.trans_lt
  have he : (n.factorial:ℝ)*(r/(2*(n.factorial:ℝ))) = r/2 := by field_simp
  rw [he]
  linarith

theorem noDP_vReflectedPolynomialJ_analyticAt {η : ℝ} (hη : 0 ≤ η)
    (P Q : Polynomial ℝ) (z : ℂ) (hz : ‖z‖ < 4) :
    AnalyticAt ℂ (vReflectedPolynomialJ η P Q) z := by
  exact (by fun_prop : AnalyticAt ℂ (fun w : ℂ => Complex.exp (-w/2)) z).mul
    ((polarPolynomialBilinearJ_analyticAt η hη P Q (-z)
      (by simpa only [norm_neg] using hz)).comp (by fun_prop))

theorem noDP_vPolynomialMixedGenerator_derivative_tendsto (n : ℕ)
    {η : ℝ} (hη : 0 < η) (hηu : η < 1/4) (P Q : Polynomial ℝ)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (z : ℂ) (hz : ‖z‖ ≤ 2) :
    Tendsto (fun T : ℝ => iteratedDeriv n (vPolynomialMixedGenerator T
      (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) Φ) z/
      ((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
        iteratedDeriv n (vReflectedPolynomialJ η P Q) z)) := by
  let F : ℝ → ℂ → ℂ := fun T w => vPolynomialMixedGenerator T
    (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) Φ w/
      ((T:ℂ)*(Real.log T:ℂ)^9)
  let G : ℂ → ℂ := fun w => (arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
    vReflectedPolynomialJ η P Q w
  have hF : ∀ᶠ T : ℝ in atTop, DifferentiableOn ℂ (F T) (ball (0:ℂ) 4) := by
    filter_upwards [eventually_gt_atTop (1:ℝ),
      Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16:ℝ))] with T hT hL
    exact (vPolynomialMixedGenerator_differentiableOn hT hL η η _ _ Φ
      (zeroExtendedPolynomialProfile_zero_above η P)
      (zeroExtendedPolynomialProfile_zero_above η Q) hΦ).div_const _
  have hG : DifferentiableOn ℂ G (ball (0:ℂ) 4) := by
    intro w hw
    have hn : ‖w‖ < 4 := by simpa only [mem_ball,dist_zero_right] using hw
    exact ((noDP_vReflectedPolynomialJ_analyticAt hη.le P Q w hn).differentiableAt.const_mul
      ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ)))).differentiableWithinAt
  have ht := noDP_disk_uniform_derivative_tendsto F G hF hG
    (noDP_vPolynomialMixedGenerator_uniform_tendsto hη hηu P Q Φ hΦ) n z hz
  convert ht using 1
  · funext T
    have he : F T = fun w => ((T:ℂ)*(Real.log T:ℂ)^9)⁻¹*
        vPolynomialMixedGenerator T (zeroExtendedPolynomialProfile η P)
          (zeroExtendedPolynomialProfile η Q) Φ w := by
      funext w
      dsimp only [F]
      ring
    rw [he,iteratedDeriv_const_mul_field]
    ring
  · dsimp only [G]
    rw [iteratedDeriv_const_mul_field]

theorem noDP_vPolynomialMixedGenerator_operator_tendsto (N : ℕ) (q : Fin (N+1) → ℂ)
    {η : ℝ} (hη : 0 < η) (hηu : η < 1/4) (P Q : Polynomial ℝ)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (z : ℂ) (hz : ‖z‖ ≤ 2) :
    Tendsto (fun T : ℝ => finiteDifferentialOperator N q (vPolynomialMixedGenerator T
      (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) Φ) z/
      ((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
        finiteDifferentialOperator N q (vReflectedPolynomialJ η P Q) z)) := by
  have ht := tendsto_finsetSum Finset.univ (fun j (_hj : j ∈ Finset.univ) =>
    (tendsto_const_nhds (x := q j)).mul
      (noDP_vPolynomialMixedGenerator_derivative_tendsto j.val hη hηu P Q Φ hΦ z hz))
  convert ht using 1
  · funext T
    unfold finiteDifferentialOperator
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · congr 1
    unfold finiteDifferentialOperator
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem noDP_vPolynomialRawMixedMoment_tendsto (N : ℕ)
    {η : ℝ} (hη : 0 < η) (hηu : η < 1/4) (P Q p : Polynomial ℝ) (hp : p.natDegree ≤ N)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun T : ℝ => vPolynomialRawMixedMoment T p
      (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) Φ/
      ((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
        finiteDifferentialOperator N (fun j => (p.coeff j.val:ℂ))
          (vReflectedPolynomialJ η P Q) 0)) := by
  have ht := noDP_vPolynomialMixedGenerator_operator_tendsto N (fun j => (p.coeff j.val:ℂ))
    hη hηu P Q Φ hΦ 0 (by norm_num)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16:ℝ))] with T hT hL
  rw [vPolynomialRawMixedMoment_eq_finiteDifferentialOperator N hT hL η η p hp
    _ _ Φ (zeroExtendedPolynomialProfile_zero_above η P)
      (zeroExtendedPolynomialProfile_zero_above η Q) hΦ]

end
end SixthMoment.Source
