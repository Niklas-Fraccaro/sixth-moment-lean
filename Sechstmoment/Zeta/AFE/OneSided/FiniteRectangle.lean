import Sechstmoment.Analysis.Complex.SimplePole

/-! Finite rectangle displacement through the sole pole at zero. This form
keeps the rectangle below the moving zeta poles of the one-sided expansion. -/
namespace Sechstmoment
open Complex Real MeasureTheory Filter Set
open scoped Topology
noncomputable section

def d04RectangleBoundary (f : ℂ → ℂ) (a b R : ℝ) : ℂ :=
  (∫ c in a..b, f ((c : ℂ)+((-R : ℝ) : ℂ)*I))-
  (∫ c in a..b, f ((c : ℂ)+(R : ℂ)*I))+
  I*(∫ v in (-R)..R, f ((b : ℂ)+(v : ℂ)*I))-
  I*(∫ v in (-R)..R, f ((a : ℂ)+(v : ℂ)*I))

private theorem d04HorizontalInverse_continuous {R : ℝ} (hR : R≠0) :
    Continuous (fun c : ℝ => ((c : ℂ)+(R : ℂ)*I)⁻¹) := by
  apply Continuous.inv₀ (by fun_prop)
  intro c hc
  have := congrArg Complex.im hc
  simp at this
  exact hR this

theorem d04HorizontalInverse_difference (a b : ℝ) {R : ℝ} (hR : R≠0) :
    (∫ c in a..b, ((c : ℂ)+((-R : ℝ) : ℂ)*I)⁻¹)-
      (∫ c in a..b, ((c : ℂ)+(R : ℂ)*I)⁻¹) =
      2*I*(Real.arctan (b/R)-Real.arctan (a/R) : ℝ) := by
  have hpos := (d04HorizontalInverse_continuous hR).intervalIntegrable (μ:=volume) a b
  have hneg := (d04HorizontalInverse_continuous (neg_ne_zero.mpr hR)).intervalIntegrable
    (μ:=volume) a b
  rw [← intervalIntegral.integral_sub hneg hpos]
  have hpoint (c : ℝ) : ((c : ℂ)+((-R : ℝ) : ℂ)*I)⁻¹-
      ((c : ℂ)+(R : ℂ)*I)⁻¹ = 2*I*(R/(R^2+c^2) : ℝ) := by
    have hnplus : (c : ℂ)+(R : ℂ)*I≠0 := by
      intro hz; have hi := congrArg Complex.im hz
      simp at hi; exact hR hi
    have hnminus : (c : ℂ)+((-R : ℝ) : ℂ)*I≠0 := by
      intro hz; have hi := congrArg Complex.im hz
      simp at hi; exact hR hi
    have he : ((c : ℂ)+((-R : ℝ) : ℂ)*I)⁻¹-
        ((c : ℂ)+(R : ℂ)*I)⁻¹ =
        (((c : ℂ)+(R : ℂ)*I)-((c : ℂ)+((-R : ℝ) : ℂ)*I))/
          (((c : ℂ)+((-R : ℝ) : ℂ)*I)*((c : ℂ)+(R : ℂ)*I)) := by
      exact inv_sub_inv hnminus hnplus
    have hp : ((c : ℂ)+((-R : ℝ) : ℂ)*I)*((c : ℂ)+(R : ℂ)*I)=
        ((R^2+c^2 : ℝ) : ℂ) := by
      push_cast
      ring_nf
      simp [I_sq]
    rw [he, hp]
    push_cast
    ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    integral_div_sq_add_sq]

theorem d04RectangleBoundary_inverse {a b R : ℝ}
    (ha : a<0) (hb : 0<b) (hR : 0<R) :
    d04RectangleBoundary (fun z : ℂ => z⁻¹) a b R = 2*Real.pi*I := by
  unfold d04RectangleBoundary
  rw [d04HorizontalInverse_difference a b hR.ne',
    verticalInverse_symmetric_integral hb.ne' R,
    verticalInverse_symmetric_integral ha.ne R]
  have hpa : (a/R)⁻¹=R/a := inv_div _ _
  have hpb : (b/R)⁻¹=R/b := inv_div _ _
  have hA := Real.arctan_inv_of_neg (div_neg_of_neg_of_pos ha hR)
  have hB := Real.arctan_inv_of_pos (div_pos hb hR)
  rw [hpa] at hA
  rw [hpb] at hB
  rw [hA, hB]
  push_cast
  ring

theorem d04MellinDslope_interval_integral_eq
    (H : ℂ → ℂ) (γ : ℝ → ℂ) {l u : ℝ}
    (hγ : ∀ t ∈ uIcc l u, γ t ≠ 0)
    (hH : IntervalIntegrable (fun t => H (γ t)/γ t) volume l u)
    (hInv : IntervalIntegrable (fun t => (γ t)⁻¹) volume l u) :
    (∫ t in l..u, dslope H 0 (γ t)) =
      (∫ t in l..u, H (γ t)/γ t)-H 0*(∫ t in l..u, (γ t)⁻¹) := by
  calc
    _ = ∫ t in l..u, H (γ t)/γ t-H 0*(γ t)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [dslope_of_ne H (hγ t ht), slope_def_field, sub_zero]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub hH (hInv.const_mul (H 0)),
        intervalIntegral.integral_const_mul]

theorem d04Rectangle_simplePole_identity (H : ℂ → ℂ) {U : Set ℂ}
    (hU : IsOpen U) (hH : DifferentiableOn ℂ H U)
    {a b R : ℝ} (ha : a<0) (hb : 0<b) (hR : 0<R)
    (hrect : uIcc a b ×ℂ uIcc (-R) R ⊆ U) :
    d04RectangleBoundary (fun z => H z/z) a b R = 2*Real.pi*I*H 0 := by
  have hab : a≤b := (ha.trans hb).le
  have hRR : -R≤R := by linarith
  have h0 : (0 : ℂ)∈U := hrect (by
    constructor
    · rw [uIcc_of_le hab]; exact ⟨ha.le, hb.le⟩
    · change (0 : ℝ)∈uIcc (-R) R
      rw [uIcc_of_le hRR]; constructor <;> linarith)
  have hQ : DifferentiableOn ℂ (dslope H 0) U :=
    (Complex.differentiableOn_dslope (hU.mem_nhds h0)).mpr hH
  have hzero : d04RectangleBoundary (dslope H 0) a b R=0 := by
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (dslope H 0)
      ((a : ℂ)+((-R : ℝ) : ℂ)*I) ((b : ℂ)+(R : ℂ)*I)
      (by simpa using hQ.mono hrect)
    simpa [d04RectangleBoundary, smul_eq_mul] using h
  have hvert (c : ℝ) (hc : c≠0) (hcab : c∈uIcc a b) :
      (∫ v in (-R)..R, dslope H 0 ((c : ℂ)+(v : ℂ)*I))=
      (∫ v in (-R)..R, H ((c : ℂ)+(v : ℂ)*I)/((c : ℂ)+(v : ℂ)*I))-
        H 0*(∫ v in (-R)..R, ((c : ℂ)+(v : ℂ)*I)⁻¹) := by
    have hn (v : ℝ) : (c : ℂ)+(v : ℂ)*I≠0 := by
      intro hz; have hr := congrArg Complex.re hz
      simp at hr; exact hc hr
    have hcont : ContinuousOn (fun v : ℝ => H ((c : ℂ)+(v : ℂ)*I))
        (uIcc (-R) R) := hH.continuousOn.comp (by fun_prop) (by
      intro v hv
      apply hrect
      exact ⟨by simpa using hcab, by simpa using hv⟩)
    apply d04MellinDslope_interval_integral_eq H _ (fun v _ => hn v)
    · exact (hcont.div (by fun_prop) (fun v _ => hn v)).intervalIntegrable
    · exact (verticalInverse_continuous hc).intervalIntegrable (μ:=volume) (-R) R
  have hhor (v : ℝ) (hv : v≠0) (hvRR : v∈uIcc (-R) R) :
      (∫ c in a..b, dslope H 0 ((c : ℂ)+(v : ℂ)*I))=
      (∫ c in a..b, H ((c : ℂ)+(v : ℂ)*I)/((c : ℂ)+(v : ℂ)*I))-
        H 0*(∫ c in a..b, ((c : ℂ)+(v : ℂ)*I)⁻¹) := by
    have hn (c : ℝ) : (c : ℂ)+(v : ℂ)*I≠0 := by
      intro hz; have hi := congrArg Complex.im hz
      simp at hi; exact hv hi
    have hcont : ContinuousOn (fun c : ℝ => H ((c : ℂ)+(v : ℂ)*I)) (uIcc a b) :=
      hH.continuousOn.comp (by fun_prop) (by
        intro c hc
        apply hrect
        exact ⟨by simpa using hc, by simpa using hvRR⟩)
    apply d04MellinDslope_interval_integral_eq H _ (fun c _ => hn c)
    · exact (hcont.div (by fun_prop) (fun c _ => hn c)).intervalIntegrable
    · exact (d04HorizontalInverse_continuous hv).intervalIntegrable (μ:=volume) a b
  unfold d04RectangleBoundary at hzero ⊢
  rw [hhor (-R) (neg_ne_zero.mpr hR.ne') (left_mem_uIcc),
    hhor R hR.ne' right_mem_uIcc,
    hvert b hb.ne' right_mem_uIcc, hvert a ha.ne left_mem_uIcc] at hzero
  have hInv := d04RectangleBoundary_inverse ha hb hR
  unfold d04RectangleBoundary at hInv
  linear_combination hzero+H 0*hInv

end
end Sechstmoment
