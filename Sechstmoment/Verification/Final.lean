import Sechstmoment.Theorem

example : Sechstmoment.LiteratureRelativeGoal := @Sechstmoment.fullProof

example : DivisorProof.Watt41 →
  Sechstmoment.FullGoal := @Sechstmoment.fullProof

example : DivisorProof.Watt41 →
    (Multipliable (fun p : {n : ℕ // Nat.Prime n} => Sechstmoment.eulerFactor (p.val : ℝ)) ∧
    0 < Sechstmoment.arithmeticFactor) ∧
  ((Sechstmoment.declaredBound : ℝ) : EReal) ≤
    Filter.liminf (fun T : ℝ => ((Sechstmoment.sixthMoment T /
      ((Sechstmoment.arithmeticFactor/(Nat.factorial 9 : ℝ))*T*(Real.log T)^9) : ℝ) : EReal))
      Filter.atTop := @Sechstmoment.fullProof

example : DivisorProof.Watt41 →
  Sechstmoment.MainClaim := @Sechstmoment.f01MainClaim

example : Sechstmoment.Source.BBLRv1FixedApproximateFEInput :=
  @Sechstmoment.Source.bblrFixedAFE_proved

open MeasureTheory

example : (DivisorProof.Watt41 →
∀ (Φ : ℝ → ℝ), Sechstmoment.SmoothDyadicWeight Φ →
  (∀ n : ℕ, 12 ≤ n → Filter.Tendsto
    (fun T : ℝ => Sechstmoment.actual250RawMixedMoment n T Φ /
      ((T:ℂ)*(Real.log T:ℂ)^9)) Filter.atTop
    (nhds ((Sechstmoment.arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
      Complex.ofReal (Sechstmoment.certificateProfileNumerator n)))) ∧
  (∀ n : ℕ, 12 ≤ n → Filter.Tendsto
    (fun T : ℝ => Sechstmoment.actual250ProjectedMixedMoment n T Φ /
      ((T:ℂ)*(Real.log T:ℂ)^9)) Filter.atTop
    (nhds ((Sechstmoment.arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
      Complex.ofReal (Sechstmoment.certificateProfileNumerator n)))) ∧
  Filter.Tendsto (fun n : ℕ => (Sechstmoment.arithmeticFactor:ℂ)*
    (∫ x : ℝ, (Φ x:ℂ))*Complex.ofReal (Sechstmoment.certificateProfileNumerator n))
    Filter.atTop (nhds ((Sechstmoment.arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
      Complex.ofReal (Sechstmoment.finiteNumerator:ℝ)))) := @Sechstmoment.firstRowNumeratorConsumer

open MeasureTheory

example : DivisorProof.Watt41 → Sechstmoment.Source.SeparatedQuadraticInput :=
  Sechstmoment.Source.separatedQuadraticInput_of_watt41

example : DivisorProof.Watt41 → DivisorProof.WeightedWattBound :=
  DivisorProof.weightedWattBound_of_watt41

open MeasureTheory

open scoped BigOperators

example : Sechstmoment.LiteratureRelativeGoal =
    (DivisorProof.Watt41 → Sechstmoment.FullGoal) := rfl

example : Sechstmoment.LiteratureInputs = DivisorProof.Watt41 := rfl

example : Sechstmoment.Source.SeparatedQuadraticInput ↔
    (∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∀ K : ℝ, 1 ≤ K →
    ∀ bounds : ℕ → ℝ, (∀ j, 0 ≤ bounds j) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Sechstmoment.Source.QuadraticScales) (α β : ℕ → ℂ)
        (W : Fin 5 → ℝ → ℝ),
        Sechstmoment.Source.QuadraticAdmissible (DivisorProof.inputExponent ε δ) δ K bounds q α β W →
        ∀ positive : Bool, ‖Sechstmoment.Source.signedQuadraticDiscrepancy positive q α β W‖ ≤
          C*((q.mass*q.H^2)^ε*Sechstmoment.Source.orientedQuadraticMajorant q+q.mass^ε*q.H^2)) := Iff.rfl

example (h : Sechstmoment.Source.SeparatedQuadraticInput)
    {ε δ K : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hK : 1 ≤ K)
    (bounds : ℕ → ℝ) (hb : ∀ j, 0 ≤ bounds j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Sechstmoment.Source.QuadraticScales) (α β : ℕ → ℂ)
      (W : Fin 5 → ℝ → ℂ),
      (∀ component, Sechstmoment.Source.QuadraticAdmissible (DivisorProof.inputExponent ε δ)
        δ K bounds q α β (Sechstmoment.rectangularRealComponent W component)) →
      (∀ i, Sechstmoment.RectangularComplexWeight (W i)) → ∀ positive : Bool,
      ‖Sechstmoment.rectangularComplexDiscrepancy positive q α β W‖ ≤
        C * Sechstmoment.phaseSourceMajorant ε q :=
  Sechstmoment.phase_BBLRv1_component_discrepancy_bound h hε hδ hK bounds hb

example {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    0 < DivisorProof.inputExponent ε δ := DivisorProof.inputExponent_pos hε hδ

#print axioms Sechstmoment.exists_smoothDyadicWeight_mass_gt
#print axioms Sechstmoment.f01SixthMomentScale
#print axioms Sechstmoment.f01SixthMomentScale_pos
#print axioms Sechstmoment.f01LogRatio_tendsto
#print axioms Sechstmoment.f01ScaleRatio_tendsto
#print axioms Sechstmoment.f01DyadicMass
#print axioms Sechstmoment.f01CertificateLowerBound
#print axioms Sechstmoment.f01ActualGram_eventually_pos
#print axioms Sechstmoment.f01CertificateLowerBound_tendsto
#print axioms Sechstmoment.f01FiniteDyadicLowerBound
#print axioms Sechstmoment.f01FiniteDyadicLowerBound_tendsto
#print axioms Sechstmoment.f01FiniteDyadicLowerBound_eventually_le
#print axioms Sechstmoment.f01NormalizedSixthMoment_eventually_gt_declared
#print axioms Sechstmoment.f01MainClaim
#print axioms Sechstmoment.fullProof
#print axioms Sechstmoment.LiteratureInputs
#print axioms Sechstmoment.LiteratureRelativeGoal
#print axioms Sechstmoment.literatureRelativeGoal_iff
#print axioms Sechstmoment.FirstRowNumeratorConsumer
#print axioms Sechstmoment.actual250RawMixedMoment_fixed_stage_tendsto
#print axioms Sechstmoment.actual250ProjectedMixedMoment_fixed_stage_tendsto
#print axioms Sechstmoment.actual250_two_stage_numerator_limit
#print axioms Sechstmoment.firstRowNumeratorConsumer
#print axioms Sechstmoment.Source.eventually_rawMomentShifts_norm_le_quarter
#print axioms Sechstmoment.Source.bblrFixedAFE_of_uniform_smallShifts
#print axioms Sechstmoment.Source.fixedAFECompletedKernel_eq_gamma_zeta_of_ne_poles
#print axioms Sechstmoment.Source.fixedAFECompletedKernel_div_eq_explicit
#print axioms Sechstmoment.Source.fixedAFECompletedKernel_div_eq_explicit_on_neighborhood
#print axioms Sechstmoment.Source.fixedAFECompletedKernel_div_eq_explicit_on_rectangle
#print axioms Sechstmoment.Source.fixedAFECompletedKernel_div_eq_explicit_rightLine
#print axioms Sechstmoment.Source.fixedAFEFourDirichlet_factorization
#print axioms Sechstmoment.fixedAFERectangleBoundary
#print axioms Sechstmoment.fixedAFE_horizontalInverse_integral
#print axioms Sechstmoment.fixedAFE_inverse_rectangle_boundary
#print axioms Sechstmoment.fixedAFE_dslope_side
#print axioms Sechstmoment.fixedAFE_finite_rectangle_residue
#print axioms Sechstmoment.Source.fixedAFE_finitePi_norm_summable
#print axioms Sechstmoment.Source.fixedAFE_finitePi_tsum_prod
#print axioms Sechstmoment.Source.fixedAFEFourDirichletKernel
#print axioms Sechstmoment.Source.fixedAFEFourDirichletMass
#print axioms Sechstmoment.Source.fixedAFEFourDirichletKernel_norm
#print axioms Sechstmoment.Source.fixedAFE_oneDirichlet_norm_summable
#print axioms Sechstmoment.Source.fixedAFEFourDirichletMass_summable
#print axioms Sechstmoment.Source.fixedAFEFourDirichletKernel_tsum
#print axioms Sechstmoment.Source.fixedAFEFourDirichletKernel_continuous
#print axioms Sechstmoment.Source.fixedAFEFourDirichlet_integral_interchange
#print axioms Sechstmoment.Source.fixedAFEWeightOnLine
#print axioms Sechstmoment.Source.fixedAFE_entireWeight_line_norm_integrable
#print axioms Sechstmoment.Source.fixedAFEWeightOnLine_integrable
#print axioms Sechstmoment.Source.fixedAFE_AFESummand_summable_of_entireWeight
#print axioms Sechstmoment.Source.fixedAFE_AFESummand_eq_integral
#print axioms Sechstmoment.Source.fixedAFE_AFESum_eq_right_integral
#print axioms Sechstmoment.Source.fixedAFE_AFESum_eq_right_integral_of_entireWeight
#print axioms Sechstmoment.Source.fixedAFE_AFESum_eq_completed_right_integral
#print axioms Sechstmoment.Source.fixedAFERectangle
#print axioms Sechstmoment.Source.fixedAFERectangleNeighborhood
#print axioms Sechstmoment.Source.fixedAFERectangleNeighborhood_isOpen
#print axioms Sechstmoment.Source.fixedAFERectangle_subset_neighborhood
#print axioms Sechstmoment.Source.fixedAFEShiftedPoint_re_pos
#print axioms Sechstmoment.Source.fixedAFEShiftedPoint_Gammaℝ_ne_zero
#print axioms Sechstmoment.Source.fixedAFEShiftedPoint_ne_zero
#print axioms Sechstmoment.Source.fixedAFEShiftedPoint_ne_one
#print axioms Sechstmoment.Source.fixedAFEShiftedPoint_dual_Gammaℝ_ne_zero
#print axioms Sechstmoment.Source.fixedAFEArgument_im_abs_lower
#print axioms Sechstmoment.Source.fixedAFEArgument_im_ne_zero
#print axioms Sechstmoment.Source.fixedAFEArgument_ne_zero
#print axioms Sechstmoment.Source.fixedAFEArgument_ne_one
#print axioms Sechstmoment.Source.fixedAFEArgument_Gammaℝ_ne_zero
#print axioms Sechstmoment.Source.fixedAFEArgument_rightLine_re_gt_one
#print axioms Sechstmoment.Source.fixedAFEArgument_im_abs_lower_on_rectangle
#print axioms Sechstmoment.Source.fixedAFEArgument_re_mem
#print axioms Sechstmoment.Source.fixedAFEArgument_half_re_mem
#print axioms Sechstmoment.Source.fixedAFEArgument_half_one_le_abs_im
#print axioms Sechstmoment.Source.fixedAFEArgument_one_le_norm_sub_one
#print axioms Sechstmoment.Source.fixedAFECompletedKernel_differentiableOn_neighborhood
#print axioms Sechstmoment.Source.fixedAFECompletedKernel_differentiableOn_rectangle
#print axioms Sechstmoment.Source.fixedAFECompletedKernel_zero_smallShifts
#print axioms Sechstmoment.Source.fixedAFECompletedKernel_reflection_smallShifts
#print axioms Sechstmoment.Source.four_heights_abs_sum_le
#print axioms Sechstmoment.Source.four_heights_abs_sum_eq
#print axioms Sechstmoment.Source.bblr_gamma_imaginary_abs_sum_le
#print axioms Sechstmoment.Source.bblr_gamma_imaginary_abs_sum_eq
#print axioms Sechstmoment.Source.bblrGammaQuotient_polynomial_rectangle_bound
#print axioms Sechstmoment.Source.bblrZetaProduct_polynomial_rectangle_bound
#print axioms Sechstmoment.Source.bblrGammaZetaProduct_polynomial_rectangle_bound
#print axioms Sechstmoment.Source.bblrExplicitAFEIntegrand
#print axioms Sechstmoment.Source.bblrExplicitAFEIntegrand_horizontal_weighted_bound
#print axioms Sechstmoment.Source.horizontal_weighted_budget_to_inverse_power
#print axioms Sechstmoment.Source.bblrExplicitAFEIntegrand_horizontal_inverse_power_bound
#print axioms Sechstmoment.Source.zetaChi_central_strip_polynomial_bound
#print axioms Sechstmoment.Source.bblrDualMultiplier_polynomial_bound
#print axioms Sechstmoment.Source.fixedAFELambda
#print axioms Sechstmoment.Source.fixedAFEShiftedPoint
#print axioms Sechstmoment.Source.fixedAFECompletedKernel
#print axioms Sechstmoment.Source.fixedAFELambda_eq_completed
#print axioms Sechstmoment.Source.fixedAFELambda_one_sub
#print axioms Sechstmoment.Source.fixedAFELambda_differentiableAt
#print axioms Sechstmoment.Source.fixedAFEDualIndex
#print axioms Sechstmoment.Source.fixedAFEShiftedPoint_dual
#print axioms Sechstmoment.Source.fixedAFECompletedKernel_zero
#print axioms Sechstmoment.Source.fixedAFECompletedKernel_reflection
#print axioms Sechstmoment.Source.fixedAFECompletedKernel_eq_gamma_zeta
#print axioms Sechstmoment.Source.fixedAFECompletedKernel_div_eq_gamma_zeta
#print axioms Sechstmoment.Source.bblrFixedAFE_proved
#print axioms Sechstmoment.Source.fixedAFEMellinIntegrand
#print axioms Sechstmoment.Source.fixedAFEHorizontalError
#print axioms Sechstmoment.Source.fixedAFEVerticalTail
#print axioms Sechstmoment.Source.fixedAFEMellinIntegrand_reflection
#print axioms Sechstmoment.Source.fixedAFE_truncated_left_eq_dual
#print axioms Sechstmoment.Source.fixedAFE_discrepancy_eq_three_errors
#print axioms Sechstmoment.Source.fixedAFEHorizontalError_inverse_power_bound
#print axioms Sechstmoment.Source.fixedAFEVerticalTail_inverse_power_bound
#print axioms Sechstmoment.Source.fixedAFE_uniform_smallShifts
#print axioms Sechstmoment.Source.integral_sub_truncation_norm_le_of_weighted_moment
#print axioms Sechstmoment.Source.fixedAFE_entireWeight_line_moment_integrable
#print axioms Sechstmoment.Source.bblrZetaProduct_uniform_right_line_bound
#print axioms Sechstmoment.Source.bblrExplicitAFEIntegrand_polynomial_right_line_bound
#print axioms Sechstmoment.Source.bblrExplicitAFEIntegrand_right_integrable
#print axioms Sechstmoment.Source.bblrExplicitAFEIntegrand_right_tail
#print axioms Sechstmoment.Source.bblrExplicitAFEIntegral_right_tail
#print axioms Sechstmoment.Source.fixedAFECompletedKernel_right_eq_explicit
#print axioms Sechstmoment.Source.fixedAFECompletedIntegral_right_tail
#print axioms Sechstmoment.Source.noDP_vCertificateRawMixedMoment_fixed_stage_tendsto
#print axioms Sechstmoment.Source.noDP_vCertificateProjectedMixedMoment_fixed_stage_tendsto
#print axioms Sechstmoment.Source.separatedQuadraticInput_of_watt41
#print axioms DivisorProof.weightedWattBound_of_watt41
#print axioms DivisorProof.inputExponent_pos
#print axioms Sechstmoment.phase_BBLRv1_component_discrepancy_bound
#print axioms Sechstmoment.phase_BBLRv1_integrable_component_source
