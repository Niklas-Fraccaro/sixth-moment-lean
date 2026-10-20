import SixthMoment.Numerator.U.MainTerm.HolomorphicDerivativeTransfer
import SixthMoment.Numerator.U.MainTerm.MainTermGeneratorIdentity
import SixthMoment.Numerator.U.MainTerm.MomentBoundaryLimit
import SixthMoment.Numerator.U.TwistedMomentHolomorphy


namespace SixthMoment
open Complex Real MeasureTheory Set Filter Source Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

def normalizedTwistedFourthMoment (T : ℝ) (f g Φ : ℝ → ℝ)
    (σ : MomentShifts) : ℂ :=
  twistedFourthMoment T (rawMomentShifts T σ) f g Φ/
    ((T:ℂ)*(Real.log T:ℂ)^9)

theorem smoothInteriorProfile_complex_zero_outside_Icc {a : ℝ} {f : ℝ → ℝ}
    (hf : SmoothInteriorProfile a f) :
    ∀ x ∉ Icc 0 a, (f x:ℂ) = 0 := by
  intro x hx
  have hn : x ∉ tsupport f := fun h => hx ⟨(hf.2.2 h).1.le,(hf.2.2 h).2.le⟩
  simp [image_eq_zero_of_notMem_tsupport hn]

theorem actualSixPrincipalPolarLimit_eq_regular_on_dpCauchyBoundary
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (f g Φ : ℝ → ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (σ : MomentShifts) (hσ : σ ∈ rectangularDistinguishedBoundary dpCauchyRadii) :
    actualSixPrincipalPolarLimit σ (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) Φ 33 =
      actualRegularProfileGenerator a b (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) Φ σ := by
  have hnorm : ∀ j : Fin 4, ‖σ j‖ ≤ 8 :=
    (dpCauchyBoundary_subset_boundedSeparatedPolarShifts hσ).1
  apply actualSixPrincipalPolarLimit_eq_regularProfileGenerator σ
    (dpCauchyBoundary_separated σ hσ) a b ha hb
    (fun x => (f x:ℂ)) (fun x => (g x:ℂ))
    (hf.2.1.comp_left (show Complex.ofReal 0=0 from rfl))
    (Complex.ofRealCLM.contDiff.comp hf.1)
    (hg.2.1.comp_left (show Complex.ofReal 0=0 from rfl))
    (Complex.ofRealCLM.contDiff.comp hg.1)
    (smoothInteriorProfile_complex_zero_outside_Icc hf)
    (smoothInteriorProfile_complex_zero_outside_Icc hg) Φ 33 (by norm_num)
  intro m j
  have hn := bblrSixShifts_norm_le σ hnorm m j
  have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hn)).1
  linarith

theorem normalizedTwistedFourthMoment_eventually_differentiableOn_polydisc
    (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∀ᶠ T : ℝ in atTop, DifferentiableOn ℂ (normalizedTwistedFourthMoment T f g Φ)
      (rectangularClosedPolydisc dpCauchyRadii) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16:ℝ))] with T hT hL
  have hR : ∀ j : Fin 4, 2*dpCauchyRadii j < Real.log T := by
    intro j
    fin_cases j <;> norm_num [dpCauchyRadii] <;> linarith
  have hfs : ∀ x, a<x → f x=0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro ht
    linarith [(hf.2.2 ht).2]
  have hgs : ∀ x, b<x → g x=0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro ht
    linarith [(hg.2.2 ht).2]
  have hm : DifferentiableOn ℂ
      (fun σ => twistedFourthMoment T (rawMomentShifts T σ) f g Φ)
      (rectangularClosedPolydisc dpCauchyRadii) :=
    twistedFourthMoment_differentiableOn_polydisc hT dpCauchyRadii hR
      a b f g Φ hfs hgs hΦ
  have hd : DifferentiableOn ℂ
      (fun σ => (((T:ℂ)*(Real.log T:ℂ)^9)⁻¹) •
        twistedFourthMoment T (rawMomentShifts T σ) f g Φ)
      (rectangularClosedPolydisc dpCauchyRadii) :=
    hm.const_smul (((T:ℂ)*(Real.log T:ℂ)^9)⁻¹)
  have heq : (fun σ => (((T:ℂ)*(Real.log T:ℂ)^9)⁻¹) •
      twistedFourthMoment T (rawMomentShifts T σ) f g Φ) =
      normalizedTwistedFourthMoment T f g Φ := by
    funext σ
    simp only [normalizedTwistedFourthMoment, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq] at hd
  exact hd

theorem normalizedTwistedFourthMoment_uniform_regular_on_boundary
    (hAFE : BBLRv1FixedApproximateFEInput) (hSource : SeparatedQuadraticInput)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hlen : 3*a+5*b < 2)
    (f g Φ : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    TendstoUniformlyOn (fun T => normalizedTwistedFourthMoment T f g Φ)
      (actualRegularProfileGenerator a b (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) Φ)
      atTop (rectangularDistinguishedBoundary dpCauchyRadii) := by
  have hb := twistedFourthMoment_normalized_uniform_on_dpCauchyBoundary
    hAFE hSource ha hab hlen f g Φ hf hg hΦ
  rw [Metric.tendstoUniformlyOn_iff] at hb ⊢
  intro ε hε
  filter_upwards [hb ε hε] with T hT σ hσ
  rw [← actualSixPrincipalPolarLimit_eq_regular_on_dpCauchyBoundary
    ha (ha.trans hab) f g Φ hf hg σ hσ]
  exact hT σ hσ

theorem normalizedTwistedFourthMoment_uniform_regular_on_polydisc
    (hAFE : BBLRv1FixedApproximateFEInput) (hSource : SeparatedQuadraticInput)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hlen : 3*a+5*b < 2)
    (f g Φ : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    TendstoUniformlyOn (fun T => normalizedTwistedFourthMoment T f g Φ)
      (actualRegularProfileGenerator a b (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) Φ)
      atTop (rectangularClosedPolydisc dpCauchyRadii) := by
  let G := actualRegularProfileGenerator a b (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) Φ
  have hG : Differentiable ℂ G := actualRegularProfileGenerator_differentiable
    a b _ _ Φ (Complex.continuous_ofReal.comp hf.1.continuous)
      (Complex.continuous_ofReal.comp hg.1.continuous)
  have hF := normalizedTwistedFourthMoment_eventually_differentiableOn_polydisc
    a b f g Φ hf hg hΦ
  have hb := normalizedTwistedFourthMoment_uniform_regular_on_boundary
    hAFE hSource ha hab hlen f g Φ hf hg hΦ
  have hhol : ∀ᶠ T : ℝ in atTop, DifferentiableOn ℂ
      (fun σ => normalizedTwistedFourthMoment T f g Φ σ-G σ)
      (rectangularClosedPolydisc dpCauchyRadii) := hF.mono (fun _ h => h.sub hG.differentiableOn)
  have hzero : TendstoUniformlyOn
      (fun T σ => normalizedTwistedFourthMoment T f g Φ σ-G σ) (fun _ => (0:ℂ))
      atTop (rectangularDistinguishedBoundary dpCauchyRadii) := by
    rw [Metric.tendstoUniformlyOn_iff] at hb ⊢
    intro ε hε
    filter_upwards [hb ε hε] with T hT σ hσ
    simpa only [dist_eq_norm, zero_sub, norm_neg, norm_sub_rev] using hT σ hσ
  have hz := rectangular_uniform_boundary_zero_to_polydisc_zero dpCauchyRadii
    dpCauchyRadii_positive _ hhol hzero
  rw [Metric.tendstoUniformlyOn_iff] at hz ⊢
  intro ε hε
  filter_upwards [hz ε hε] with T hT σ hσ
  simpa only [dist_eq_norm, zero_sub, norm_neg, norm_sub_rev] using hT σ hσ

theorem normalizedTwistedFourthMoment_coordinate_derivatives_uniform_regular
    (hAFE : BBLRv1FixedApproximateFEInput) (hSource : SeparatedQuadraticInput)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hlen : 3*a+5*b < 2)
    (f g Φ : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (i : Fin 4) (r : ℝ) (hr : 0 < r)
    (hri : 2*r ≤ dpCauchyRadii i) (n : ℕ) :
    TendstoUniformlyOn
      (fun T => iteratedDeriv n (fun z =>
        normalizedTwistedFourthMoment T f g Φ (rectangularCoordinateLine i z)))
      (iteratedDeriv n (fun z => actualRegularProfileGenerator a b
        (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) Φ (rectangularCoordinateLine i z)))
      atTop (closedBall (0:ℂ) r) :=
  rectangular_coordinate_iteratedDeriv_uniform_limit dpCauchyRadii dpCauchyRadii_positive
    i r hr hri _ _
    (normalizedTwistedFourthMoment_eventually_differentiableOn_polydisc a b f g Φ hf hg hΦ)
    (actualRegularProfileGenerator_differentiable a b _ _ Φ
      (Complex.continuous_ofReal.comp hf.1.continuous)
      (Complex.continuous_ofReal.comp hg.1.continuous)).differentiableOn
    (normalizedTwistedFourthMoment_uniform_regular_on_boundary
      hAFE hSource ha hab hlen f g Φ hf hg hΦ) n

end
end SixthMoment
