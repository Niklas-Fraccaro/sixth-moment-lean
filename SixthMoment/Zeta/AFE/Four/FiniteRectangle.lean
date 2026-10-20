import SixthMoment.Analysis.Complex.SimplePole


namespace SixthMoment
open Complex Real Set MeasureTheory
open scoped Topology
noncomputable section

def fixedAFERectangleBoundary (f : ℂ → ℂ) (h : ℝ) : ℂ :=
  (∫ c in (-1 : ℝ)..1, f ((c : ℂ) + ((-h : ℝ) : ℂ) * I)) -
  (∫ c in (-1 : ℝ)..1, f ((c : ℂ) + (h : ℂ) * I)) +
  I * (∫ v in (-h)..h, f (1 + (v : ℂ) * I)) -
  I * (∫ v in (-h)..h, f (-1 + (v : ℂ) * I))

theorem fixedAFE_horizontalInverse_integral {h : ℝ} (hh : h ≠ 0) :
    (∫ c in (-1 : ℝ)..1, ((c : ℂ) + (h : ℂ) * I)⁻¹) =
      -I * (2 * Real.arctan (1 / h) : ℝ) := by
  have hp (c : ℝ) :
      ((c : ℂ) + (h : ℂ) * I)⁻¹ =
        -I * ((h : ℂ) + ((-c : ℝ) : ℂ) * I)⁻¹ := by
    have he : (c : ℂ) + (h : ℂ) * I =
        I * ((h : ℂ) + ((-c : ℝ) : ℂ) * I) := by
      push_cast
      calc
        _ = (h : ℂ) * I + (c : ℂ) := by ring
        _ = _ := by ring_nf; simp [I_sq]
    rw [he, mul_inv_rev, Complex.inv_I]
    ring
  simp_rw [hp]
  rw [intervalIntegral.integral_const_mul]
  have hneg := intervalIntegral.integral_comp_neg
    (fun y : ℝ => ((h : ℂ) + (y : ℂ) * I)⁻¹) (a := -1) (b := 1)
  change (∫ c in (-1 : ℝ)..1, ((h : ℂ) + ((-c : ℝ) : ℂ) * I)⁻¹) = _ at hneg
  rw [hneg]
  norm_num only [neg_neg]
  rw [verticalInverse_symmetric_integral hh 1]

theorem fixedAFE_inverse_rectangle_boundary {h : ℝ} (hh : 0 < h) :
    fixedAFERectangleBoundary (fun z => z⁻¹) h = (2 * Real.pi : ℂ) * I := by
  unfold fixedAFERectangleBoundary
  dsimp only
  have hvp : (∫ v in (-h)..h, (1 + (v : ℂ) * I)⁻¹) =
      (2 * Real.arctan h : ℝ) := by
    simpa using verticalInverse_symmetric_integral (by norm_num : (1 : ℝ) ≠ 0) h
  have hvn : (∫ v in (-h)..h, (-1 + (v : ℂ) * I)⁻¹) =
      (-2 * Real.arctan h : ℝ) := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_one, div_neg, div_one,
      Real.arctan_neg, Complex.ofReal_mul, Complex.ofReal_ofNat, mul_neg, neg_mul] using
      verticalInverse_symmetric_integral (by norm_num : (-1 : ℝ) ≠ 0) h
  rw [fixedAFE_horizontalInverse_integral (neg_ne_zero.mpr hh.ne'),
    fixedAFE_horizontalInverse_integral hh.ne', hvp, hvn]
  simp only [one_div, Real.arctan_neg, div_neg, neg_mul,
    Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [Real.arctan_inv_of_pos hh]
  push_cast
  ring

theorem fixedAFE_dslope_side (H : ℂ → ℂ) {U : Set ℂ}
    (hH : ContinuousOn H U) (p : ℝ → ℂ) (hp : Continuous p)
    (a b : ℝ) (hmap : ∀ x ∈ uIcc a b, p x ∈ U)
    (hne : ∀ x : ℝ, p x ≠ 0) :
    (∫ x in a..b, dslope H 0 (p x)) =
      (∫ x in a..b, H (p x) / p x) -
        H 0 * (∫ x in a..b, (p x)⁻¹) := by
  have hHC : ContinuousOn (fun x => H (p x)) (uIcc a b) :=
    hH.comp hp.continuousOn hmap
  have hI : IntervalIntegrable (fun x => H (p x) / p x) volume a b :=
    (hHC.div hp.continuousOn (fun x _ => hne x)).intervalIntegrable
  have hInv : IntervalIntegrable (fun x => (p x)⁻¹) volume a b :=
    (hp.inv₀ hne).intervalIntegrable (μ := volume) a b
  calc
    _ = ∫ x in a..b, H (p x) / p x - H 0 * (p x)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [dslope_of_ne H (hne x), slope_def_field, sub_zero]
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub hI (hInv.const_mul (H 0)),
        intervalIntegral.integral_const_mul]

theorem fixedAFE_finite_rectangle_residue (H : ℂ → ℂ) {U : Set ℂ}
    (hU : IsOpen U) (hH : DifferentiableOn ℂ H U)
    {h : ℝ} (hh : 0 < h)
    (hrect : ∀ z : ℂ, |z.re| ≤ 1 → |z.im| ≤ h → z ∈ U) :
    fixedAFERectangleBoundary (fun z => H z / z) h =
      (2 * Real.pi : ℂ) * I * H 0 := by
  have hzero : (0 : ℂ) ∈ U := hrect 0 (by norm_num) (by simpa using hh.le)
  have hQ : DifferentiableOn ℂ (dslope H 0) U :=
    (Complex.differentiableOn_dslope (hU.mem_nhds hzero)).mpr hH
  have hclosed : DifferentiableOn ℂ (dslope H 0)
      (uIcc (-1 : ℝ) 1 ×ℂ uIcc (-h) h) := by
    apply hQ.mono
    intro z hz
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hz
    rw [uIcc_of_le (by linarith : -h ≤ h)] at hz
    exact hrect z (abs_le.mpr hz.1) (abs_le.mpr hz.2)
  have hboundary : fixedAFERectangleBoundary (dslope H 0) h = 0 := by
    have he := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      (dslope H 0) ((-1 : ℂ) + ((-h : ℝ) : ℂ) * I)
      (1 + (h : ℂ) * I) (by simpa using hclosed)
    simpa [fixedAFERectangleBoundary, smul_eq_mul] using he
  have hsideV (c : ℝ) (hc : |c| = 1) :
      (∫ v in (-h)..h, dslope H 0 ((c : ℂ) + (v : ℂ) * I)) =
      (∫ v in (-h)..h, H ((c : ℂ) + (v : ℂ) * I) /
        ((c : ℂ) + (v : ℂ) * I)) -
        H 0 * (∫ v in (-h)..h, ((c : ℂ) + (v : ℂ) * I)⁻¹) := by
    apply fixedAFE_dslope_side H hH.continuousOn _ (by fun_prop)
    · intro v hv
      rw [uIcc_of_le (by linarith : -h ≤ h)] at hv
      apply hrect
      · simpa using hc.le
      · simpa using abs_le.mpr hv
    · intro v he
      have he' := congrArg Complex.re he
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero, zero_re] at he'
      simp [he'] at hc
  have hsideH (v : ℝ) (hv : |v| = h) :
      (∫ c in (-1 : ℝ)..1, dslope H 0 ((c : ℂ) + (v : ℂ) * I)) =
      (∫ c in (-1 : ℝ)..1, H ((c : ℂ) + (v : ℂ) * I) /
        ((c : ℂ) + (v : ℂ) * I)) -
        H 0 * (∫ c in (-1 : ℝ)..1, ((c : ℂ) + (v : ℂ) * I)⁻¹) := by
    apply fixedAFE_dslope_side H hH.continuousOn _ (by fun_prop)
    · intro c hc
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hc
      apply hrect
      · simpa using abs_le.mpr hc
      · simpa using hv.le
    · intro c he
      have he' := congrArg Complex.im he
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
        mul_one, mul_zero, add_zero, zero_add, zero_im] at he'
      have hv0 : v ≠ 0 := by intro he; simp [he] at hv; linarith
      exact hv0 he'
  unfold fixedAFERectangleBoundary at hboundary
  have hright := hsideV 1 (by norm_num)
  have hleft := hsideV (-1) (by norm_num)
  norm_num only [Complex.ofReal_one, Complex.ofReal_neg] at hright hleft
  rw [hsideH (-h) (by simp [abs_of_pos hh]),
    hsideH h (abs_of_pos hh), hright, hleft] at hboundary
  have hi := fixedAFE_inverse_rectangle_boundary hh
  unfold fixedAFERectangleBoundary at hi ⊢
  linear_combination hboundary + H 0 * hi

end
end SixthMoment
