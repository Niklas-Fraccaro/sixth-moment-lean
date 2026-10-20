import SixthMoment.Numerator.V.DP.DPAllPositiveCoincidence
import SixthMoment.Numerator.V.DP.ShiftLine

namespace SixthMoment.Source
open Complex Set Metric Filter MeasureTheory Polynomial
open scoped Topology
noncomputable section

def dpAllPositiveShiftLineError (T η : ℝ) (P : ℝ[X]) (Φ : ℝ → ℝ)
    (v : MomentShifts) (z : ℂ) : ℂ :=
  dpAllPositiveMoment T η P (momentShiftLine v z) Φ-
    (T : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*
      dpAllPositiveRegularLeadingDensity T η P (momentShiftLine v z)

theorem dpAllPositiveMoment_shiftLine_uniform_derivative_bound (n : ℕ)
    (hsource : DPv2SharpInput) (η : ℝ) (hη : 0 < η) (hηu : η < 1/4)
    (P : ℝ[X]) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ v ∈ rectangularClosedPolydisc dpCauchyRadii,
      ∀ Φ : ℝ → ℝ, SmoothDyadicWeight Φ → WeightSeminormBound 1 B Φ →
      ‖iteratedDeriv n (dpAllPositiveShiftLineError T η P Φ v) 0‖ ≤
        C*T*(Real.log T)^8 := by
  obtain ⟨C,hC,hbound⟩ := dpAllPositiveMoment_coincident_uniform_smoothing hsource η hη hηu P B hB
  refine ⟨(n.factorial : ℝ)*C,mul_nonneg (by positivity) hC,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16 : ℝ))]
    with T hbound hT hL v hv Φ hΦ hseminorm
  have hR : ∀ j, 2*dpCauchyRadii j < Real.log T := by
    intro j
    have hr : dpCauchyRadii j ≤ (8 : ℝ) := by fin_cases j <;> norm_num [dpCauchyRadii]
    linarith
  have hm := dpAllPositiveMoment_differentiableOn_polydisc hT dpCauchyRadii hR η P Φ hΦ
  have hf := hm.sub ((dpAllPositiveRegularLeadingDensity_differentiableOn hη.le T P).const_mul
    ((T : ℂ)*(∫ x : ℝ, (Φ x : ℂ))))
  have hh := shiftLine_cauchy_polydisc_bound n dpCauchyRadii v hv _ hf
    (fun σ hσ => hbound σ hσ Φ hΦ hseminorm)
  change ‖iteratedDeriv n (dpAllPositiveShiftLineError T η P Φ v) 0‖ ≤ _ at hh
  convert hh using 1; ring

def dpPolarMomentError (T η : ℝ) (P : ℝ[X]) (Φ : ℝ → ℝ) (z : ℂ) : ℂ :=
  dpAllPositiveMoment T η P (dpCoincidentShifts z) Φ-
    ((T : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*(arithmeticFactor : ℂ)*(Real.log T : ℂ)^9)*
      polarPolynomialJ η P z

private theorem dpCoincidentShifts_eq_shiftLine (z : ℂ) :
    dpCoincidentShifts z=momentShiftLine (![0,0,-1,0] : MomentShifts) z := by
  funext j
  fin_cases j <;> simp [dpCoincidentShifts,momentShiftLine]

private theorem dpPolarMomentError_eventuallyEq (T η : ℝ) (P : ℝ[X]) (Φ : ℝ → ℝ) :
    dpPolarMomentError T η P Φ =ᶠ[𝓝 (0:ℂ)]
      dpAllPositiveShiftLineError T η P Φ (![0,0,-1,0] : MomentShifts) := by
  filter_upwards [ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ)<1)] with z hz
  have hz16 : ‖z‖ < 16 := by
    have hz1 : ‖z‖<1 := by simpa only [mem_ball,dist_zero_right] using hz
    linarith
  unfold dpPolarMomentError dpAllPositiveShiftLineError
  rw [← dpCoincidentShifts_eq_shiftLine]
  unfold dpAllPositiveRegularLeadingDensity
  rw [dpAllPositiveRegularKernel_coincident η P z hz16]
  ring

theorem dpPolarMoment_uniform_derivative_bound (n : ℕ)
    (hsource : DPv2SharpInput) (η : ℝ) (hη : 0 < η) (hηu : η < 1/4)
    (P : ℝ[X]) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ Φ : ℝ → ℝ, SmoothDyadicWeight Φ → WeightSeminormBound 1 B Φ →
      ‖iteratedDeriv n (dpPolarMomentError T η P Φ) 0‖ ≤ C*T*(Real.log T)^8 := by
  obtain ⟨C,hC,hbound⟩ := dpAllPositiveMoment_shiftLine_uniform_derivative_bound n
    hsource η hη hηu P B hB
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with T hbound Φ hΦ hseminorm
  rw [(dpPolarMomentError_eventuallyEq T η P Φ).iteratedDeriv_eq n]
  apply hbound _ (dpCoincidentShifts_mem_polydisc (z := 1) (by norm_num)) Φ hΦ hseminorm

private theorem dpPolarKernel_analyticAt (η : ℝ) (hη : 0 ≤ η) (P : ℝ[X])
    (z : ℂ) (hz : ‖z‖<4) : AnalyticAt ℂ (polarPolynomialJ η P) z := by
  have hg : DifferentiableOn ℂ (fun z => dpAllPositiveRegularKernel η P (dpCoincidentShifts z))
      (ball 0 4) :=
    (dpAllPositiveRegularKernel_differentiableOn hη P).comp
      dpCoincidentShifts_differentiable.differentiableOn (by
        intro z hz
        apply dpCoincidentShifts_mem_polydisc
        exact (show ‖z‖<4 by simpa only [mem_ball,dist_zero_right] using hz).le)
  have hzball : z ∈ ball (0:ℂ) 4 := by simpa only [mem_ball,dist_zero_right] using hz
  have he : polarPolynomialJ η P =ᶠ[𝓝 z]
      (fun z => dpAllPositiveRegularKernel η P (dpCoincidentShifts z)) := by
    filter_upwards [isOpen_ball.mem_nhds hzball] with z hz
    symm
    apply dpAllPositiveRegularKernel_coincident
    have hz4 : ‖z‖<4 := by simpa only [mem_ball,dist_zero_right] using hz
    linarith
  exact (hg.analyticAt (isOpen_ball.mem_nhds hzball)).congr he.symm

private theorem dpPolarMoment_analyticAt {T : ℝ} (hT : 1 < T)
    (hL : 16 < Real.log T) (η : ℝ) (P : ℝ[X]) (Φ : ℝ → ℝ)
    (hΦ : SmoothDyadicWeight Φ) (z : ℂ) (hz : ‖z‖<4) :
    AnalyticAt ℂ (fun z => dpAllPositiveMoment T η P (dpCoincidentShifts z) Φ) z := by
  have hR : ∀ j, 2*dpCauchyRadii j < Real.log T := by
    intro j
    have hr : dpCauchyRadii j ≤ (8 : ℝ) := by fin_cases j <;> norm_num [dpCauchyRadii]
    linarith
  have hm := dpAllPositiveMoment_differentiableOn_polydisc hT dpCauchyRadii hR η P Φ hΦ
  have hd : DifferentiableOn ℂ (fun z => dpAllPositiveMoment T η P (dpCoincidentShifts z) Φ)
      (ball 0 4) := hm.comp dpCoincidentShifts_differentiable.differentiableOn (by
        intro z hz
        apply dpCoincidentShifts_mem_polydisc
        exact (show ‖z‖<4 by simpa only [mem_ball,dist_zero_right] using hz).le)
  exact hd.analyticAt (isOpen_ball.mem_nhds
    (by simpa only [mem_ball,dist_zero_right] using hz))

theorem dpAllPositiveMoment_polarPolynomialJ_derivative_tendsto (n : ℕ)
    (hsource : DPv2SharpInput) (η : ℝ) (hη : 0 < η) (hηu : η < 1/4) (P : ℝ[X])
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun T : ℝ =>
      iteratedDeriv n (fun z => dpAllPositiveMoment T η P (dpCoincidentShifts z) Φ) 0/
      ((T : ℂ)*(Real.log T : ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*
        iteratedDeriv n (polarPolynomialJ η P) 0)) := by
  obtain ⟨B,hB,hseminorm⟩ := smoothDyadicWeight_seminorm_one_bound Φ hΦ
  obtain ⟨C,_,hbound⟩ := dpPolarMoment_uniform_derivative_bound n hsource η hη hηu P B hB
  let E : ℝ → ℂ := fun T => iteratedDeriv n (dpPolarMomentError T η P Φ) 0
  have hE := logNormalizedRemainder_tendsto E C
    (hbound.mono (fun T h => h Φ hΦ hseminorm))
  have ht := (tendsto_const_nhds (x := (arithmeticFactor : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*
      iteratedDeriv n (polarPolynomialJ η P) 0)).add hE
  simp only [add_zero] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16 : ℝ))] with T hT hL
  have hT0 : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hT).ne'
  have hL0 : (Real.log T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hT).ne'
  have hm := (dpPolarMoment_analyticAt hT hL η P Φ hΦ 0 (by norm_num)).contDiffAt (n := n)
  have hj := (dpPolarKernel_analyticAt η hη.le P 0 (by norm_num)).contDiffAt (n := n)
  have he : E T =
      iteratedDeriv n (fun z => dpAllPositiveMoment T η P (dpCoincidentShifts z) Φ) 0-
      ((T : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*(arithmeticFactor : ℂ)*(Real.log T : ℂ)^9)*
        iteratedDeriv n (polarPolynomialJ η P) 0 := by
    dsimp only [E]
    unfold dpPolarMomentError
    rw [iteratedDeriv_fun_sub hm (contDiffAt_const.mul hj),iteratedDeriv_const_mul_field]
  rw [he]
  field_simp
  ring

theorem dpPolarMoment_uniform_derivative_bound_on_disk (n : ℕ)
    (hsource : DPv2SharpInput) (η : ℝ) (hη : 0 < η) (hηu : η < 1/4)
    (P : ℝ[X]) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ Φ : ℝ → ℝ, SmoothDyadicWeight Φ → WeightSeminormBound 1 B Φ →
      ∀ z : ℂ, ‖z‖ ≤ 2 →
      ‖iteratedDeriv n (dpPolarMomentError T η P Φ) z‖ ≤ C*T*(Real.log T)^8 := by
  obtain ⟨C,hC,hbound⟩ := dpAllPositiveMoment_coincident_uniform_smoothing hsource η hη hηu P B hB
  refine ⟨(n.factorial : ℝ)*C,mul_nonneg (by positivity) hC,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16 : ℝ))]
    with T hbound hT hL Φ hΦ hseminorm z hz
  have ha : DifferentiableOn ℂ (dpPolarMomentError T η P Φ) (ball 0 4) := by
    intro w hw
    have hw4 : ‖w‖<4 := by simpa only [mem_ball,dist_zero_right] using hw
    exact ((dpPolarMoment_analyticAt hT hL η P Φ hΦ w hw4).sub
      (analyticAt_const.mul (dpPolarKernel_analyticAt η hη.le P w hw4))).differentiableWithinAt
  have hclosed : closedBall z 1 ⊆ ball (0:ℂ) 4 := by
    intro w hw
    have hwn : ‖w-z‖≤1 := by simpa only [mem_closedBall,dist_eq_norm] using hw
    have hn : ‖w‖≤‖w-z‖+‖z‖ := by
      convert norm_add_le (w-z) z using 1; simp
    have hw4 : ‖w‖<4 := by linarith
    simpa only [mem_ball,dist_zero_right] using hw4
  have hb (w : ℂ) (hw : w ∈ sphere z 1) :
      ‖dpPolarMomentError T η P Φ w‖≤C*T*(Real.log T)^8 := by
    have hw4 : ‖w‖<4 := by
      simpa only [mem_ball,dist_zero_right] using hclosed (sphere_subset_closedBall hw)
    have hh := hbound (dpCoincidentShifts w) (dpCoincidentShifts_mem_polydisc hw4.le) Φ hΦ hseminorm
    have he : dpPolarMomentError T η P Φ w =
        dpAllPositiveMoment T η P (dpCoincidentShifts w) Φ-
          (T : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*
            dpAllPositiveRegularLeadingDensity T η P (dpCoincidentShifts w) := by
      unfold dpPolarMomentError dpAllPositiveRegularLeadingDensity
      rw [dpAllPositiveRegularKernel_coincident η P w (by linarith)]
      ring
    rw [he]
    exact hh
  have hh := cauchy_iteratedDeriv_bound n (by norm_num : (0:ℝ)<1)
    ((ha.mono hclosed).diffContOnCl_ball Subset.rfl) hb
  simp only [one_pow,div_one] at hh
  convert hh using 1; ring

theorem dpAllPositiveMoment_polarPolynomialJ_derivative_tendsto_at (n : ℕ)
    (hsource : DPv2SharpInput) (η : ℝ) (hη : 0 < η) (hηu : η < 1/4) (P : ℝ[X])
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (z : ℂ) (hz : ‖z‖≤2) :
    Tendsto (fun T : ℝ =>
      iteratedDeriv n (fun z => dpAllPositiveMoment T η P (dpCoincidentShifts z) Φ) z/
      ((T : ℂ)*(Real.log T : ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*
        iteratedDeriv n (polarPolynomialJ η P) z)) := by
  obtain ⟨B,hB,hseminorm⟩ := smoothDyadicWeight_seminorm_one_bound Φ hΦ
  obtain ⟨C,_,hbound⟩ := dpPolarMoment_uniform_derivative_bound_on_disk n hsource η hη hηu P B hB
  let E : ℝ → ℂ := fun T => iteratedDeriv n (dpPolarMomentError T η P Φ) z
  have hE := logNormalizedRemainder_tendsto E C
    (hbound.mono (fun T h => h Φ hΦ hseminorm z hz))
  have ht := (tendsto_const_nhds (x := (arithmeticFactor : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*
      iteratedDeriv n (polarPolynomialJ η P) z)).add hE
  simp only [add_zero] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16 : ℝ))] with T hT hL
  have hT0 : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hT).ne'
  have hL0 : (Real.log T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hT).ne'
  have hz4 : ‖z‖<4 := by linarith
  have hm := (dpPolarMoment_analyticAt hT hL η P Φ hΦ z hz4).contDiffAt (n := n)
  have hj := (dpPolarKernel_analyticAt η hη.le P z hz4).contDiffAt (n := n)
  have he : E T =
      iteratedDeriv n (fun z => dpAllPositiveMoment T η P (dpCoincidentShifts z) Φ) z-
      ((T : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*(arithmeticFactor : ℂ)*(Real.log T : ℂ)^9)*
        iteratedDeriv n (polarPolynomialJ η P) z := by
    dsimp only [E]
    unfold dpPolarMomentError
    rw [iteratedDeriv_fun_sub hm (contDiffAt_const.mul hj),iteratedDeriv_const_mul_field]
  rw [he]
  field_simp
  ring

theorem dpAllPositiveMoment_polarPolynomialJ_operator_tendsto (N : ℕ)
    (q : Fin (N+1) → ℂ) (hsource : DPv2SharpInput)
    (η : ℝ) (hη : 0 < η) (hηu : η < 1/4) (P : ℝ[X])
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (z : ℂ) (hz : ‖z‖≤2) :
    Tendsto (fun T : ℝ =>
      finiteDifferentialOperator N q
        (fun z => dpAllPositiveMoment T η P (dpCoincidentShifts z) Φ) z/
      ((T : ℂ)*(Real.log T : ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*
        finiteDifferentialOperator N q (polarPolynomialJ η P) z)) := by
  have ht := tendsto_finsetSum Finset.univ (fun j (_hj : j ∈ Finset.univ) =>
    (tendsto_const_nhds (x := q j)).mul
      (dpAllPositiveMoment_polarPolynomialJ_derivative_tendsto_at j.val
        hsource η hη hηu P Φ hΦ z hz))
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

end
end SixthMoment.Source
