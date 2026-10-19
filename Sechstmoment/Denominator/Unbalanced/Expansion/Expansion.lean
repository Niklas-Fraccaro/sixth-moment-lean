import Sechstmoment.Denominator.Unbalanced.Expansion.Series
import Sechstmoment.Zeta.AFE.OneSided.FiniteRectangle

/-! The finite Gamma rectangle behind the one-sided expansion. Its upper
and lower edges remain strictly below both moving zeta poles. -/
namespace Sechstmoment
open Complex Real MeasureTheory Filter Set
open scoped Topology
noncomputable section

def d04OneSidedPoleRemovedContour (X : ℝ) (s r z : ℂ) : ℂ :=
  Complex.Gamma (z+1)*(X : ℂ)^z*riemannZeta (s+z)*riemannZeta (r+z)

def d04OneSidedContourRegion (s r : ℂ) : Set ℂ :=
  {z | -1<z.re ∧ |z.im|<min |s.im| |r.im|}

def d04OneSidedVerticalTruncated (X : ℝ) (s r : ℂ) (c R : ℝ) : ℂ :=
  ∫ v in (-R)..R,
    d04OneSidedMellinIntegrand X s r ((c : ℂ)+(v : ℂ)*I)

def d04OneSidedHorizontalIntegral (X : ℝ) (s r : ℂ) (a v : ℝ) : ℂ :=
  ∫ c in a..2, d04OneSidedMellinIntegrand X s r ((c : ℂ)+(v : ℂ)*I)

def d04OneSidedRightTail (X : ℝ) (s r : ℂ) (R : ℝ) : ℂ :=
  (∫ v : ℝ, d04OneSidedMellinIntegrand X s r (d04MellinLine v))-
    d04OneSidedVerticalTruncated X s r 2 R

theorem d04OneSidedContourRegion_isOpen (s r : ℂ) :
    IsOpen (d04OneSidedContourRegion s r) := by
  exact (isOpen_Ioi.preimage continuous_re).inter
    (isOpen_Iio.preimage (continuous_abs.comp continuous_im))

private theorem d04OneSided_zetaArgument_ne_one (s : ℂ) {z : ℂ}
    (hz : |z.im| < |s.im|) : s+z≠1 := by
  intro he
  have hi := congrArg Complex.im he
  simp only [add_im, one_im] at hi
  have he' : z.im=-s.im := by linarith
  rw [he', abs_neg] at hz
  exact (lt_irrefl _) hz

theorem d04OneSidedPoleRemovedContour_differentiableOn {X : ℝ} (hX : 0<X)
    (s r : ℂ) : DifferentiableOn ℂ (d04OneSidedPoleRemovedContour X s r)
      (d04OneSidedContourRegion s r) := by
  intro z hz
  have hΓ : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w+1)) z := by
    have hnΓ : ∀ n : ℕ, z+1≠-n := by
      intro n hn
      have h := congrArg Complex.re hn
      simp only [add_re, one_re, neg_re, natCast_re] at h
      have hn0 : (0 : ℝ)≤n := Nat.cast_nonneg n
      have hzr := hz.1
      linarith
    exact (Complex.differentiableAt_Gamma (z+1) hnΓ).comp z (by fun_prop)
  have hPow : DifferentiableAt ℂ (fun w : ℂ => (X : ℂ)^w) z :=
    DifferentiableAt.const_cpow differentiableAt_id
      (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  have hs : DifferentiableAt ℂ (fun w : ℂ => riemannZeta (s+w)) z :=
    (differentiableAt_riemannZeta (d04OneSided_zetaArgument_ne_one s
      (hz.2.trans_le (min_le_left _ _)))).comp z (by fun_prop)
  have hr : DifferentiableAt ℂ (fun w : ℂ => riemannZeta (r+w)) z :=
    (differentiableAt_riemannZeta (d04OneSided_zetaArgument_ne_one r
      (hz.2.trans_le (min_le_right _ _)))).comp z (by fun_prop)
  exact (((hΓ.mul hPow).mul hs).mul hr).differentiableWithinAt

theorem d04OneSidedPoleRemovedContour_zero (X : ℝ) (s r : ℂ) :
    d04OneSidedPoleRemovedContour X s r 0=riemannZeta s*riemannZeta r := by
  simp [d04OneSidedPoleRemovedContour]

theorem d04OneSidedPoleRemovedContour_div (X : ℝ) (s r z : ℂ) (hz : z≠0) :
    d04OneSidedPoleRemovedContour X s r z/z=d04OneSidedMellinIntegrand X s r z := by
  unfold d04OneSidedPoleRemovedContour d04OneSidedMellinIntegrand
  rw [Complex.Gamma_add_one z hz]
  field_simp

theorem d04OneSidedGamma_rectangle_identity {X a R : ℝ} (hX : 0<X)
    (ha : -1<a) (ha0 : a<0) (hR : 0<R) (s r : ℂ)
    (hs : R < |s.im|) (hr : R < |r.im|) :
    d04RectangleBoundary
      (fun z => d04OneSidedPoleRemovedContour X s r z/z) a 2 R =
      2*Real.pi*I*(riemannZeta s*riemannZeta r) := by
  rw [← d04OneSidedPoleRemovedContour_zero X s r]
  apply d04Rectangle_simplePole_identity (d04OneSidedPoleRemovedContour X s r)
    (d04OneSidedContourRegion_isOpen s r)
    (d04OneSidedPoleRemovedContour_differentiableOn hX s r) ha0 (by norm_num) hR
  intro z hz
  rw [uIcc_of_le (by linarith : a≤(2 : ℝ))] at hz
  rw [uIcc_of_le (by linarith : -R≤R)] at hz
  refine ⟨ha.trans_le hz.1.1, ?_⟩
  have hzR : |z.im|≤R := abs_le.mpr hz.2
  exact hzR.trans_lt (lt_min hs hr)

theorem d04OneSidedGamma_rectangle_integrals {X a R : ℝ} (hX : 0<X)
    (ha : -1<a) (ha0 : a<0) (hR : 0<R) (s r : ℂ)
    (hs : R < |s.im|) (hr : R < |r.im|) :
    d04OneSidedHorizontalIntegral X s r a (-R)-
      d04OneSidedHorizontalIntegral X s r a R+
      I*d04OneSidedVerticalTruncated X s r 2 R-
      I*d04OneSidedVerticalTruncated X s r a R =
      2*Real.pi*I*(riemannZeta s*riemannZeta r) := by
  have h := d04OneSidedGamma_rectangle_identity hX ha ha0 hR s r hs hr
  have hver (c : ℝ) (hc : c≠0) :
      (∫ v in (-R)..R, d04OneSidedPoleRemovedContour X s r
        ((c : ℂ)+(v : ℂ)*I)/((c : ℂ)+(v : ℂ)*I))=
      d04OneSidedVerticalTruncated X s r c R := by
    apply intervalIntegral.integral_congr
    intro v hv
    dsimp only
    apply d04OneSidedPoleRemovedContour_div
    intro hz
    have hh := congrArg Complex.re hz
    simp at hh
    exact hc hh
  have hhor (v : ℝ) (hv : v≠0) :
      (∫ c in a..2, d04OneSidedPoleRemovedContour X s r
        ((c : ℂ)+(v : ℂ)*I)/((c : ℂ)+(v : ℂ)*I))=
      d04OneSidedHorizontalIntegral X s r a v := by
    apply intervalIntegral.integral_congr
    intro c hc
    dsimp only
    apply d04OneSidedPoleRemovedContour_div
    intro hz
    have hh := congrArg Complex.im hz
    simp at hh
    exact hv hh
  unfold d04RectangleBoundary at h
  dsimp only at h
  rw [hhor (-R) (neg_ne_zero.mpr hR.ne'), hhor R hR.ne',
    hver 2 (by norm_num), hver a ha0.ne] at h
  exact h

/-- The actual expansion error consists exactly of the three displaced
boundaries and the original positive-line tail. -/
theorem d04OneSidedRawSeries_error_decomposition {X a R : ℝ} (hX : 0<X)
    (ha : -1<a) (ha0 : a<0) (hR : 0<R) (s r : ℂ)
    (hs : R < |s.im|) (hr : R < |r.im|) (hsre : -1<s.re) (hrre : -1<r.re) :
    d04OneSidedRawSeries X s r-riemannZeta s*riemannZeta r =
      (1/(2*Real.pi) : ℂ)*(d04OneSidedRightTail X s r R+
        d04OneSidedVerticalTruncated X s r a R+
        I*(d04OneSidedHorizontalIntegral X s r a (-R)-
          d04OneSidedHorizontalIntegral X s r a R)) := by
  rw [d04OneSidedRawSeries_eq_mellin hX hsre hrre]
  unfold d04OneSidedMellinIntegral d04OneSidedRightTail
  have h := d04OneSidedGamma_rectangle_integrals hX ha ha0 hR s r hs hr
  have hpi : (Real.pi : ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  linear_combination (norm := ring_nf) -I*h
  simp [I_sq]

theorem d04OneSidedRawSeries_error_norm_le {X a R : ℝ} (hX : 0<X)
    (ha : -1<a) (ha0 : a<0) (hR : 0<R) (s r : ℂ)
    (hs : R < |s.im|) (hr : R < |r.im|) (hsre : -1<s.re) (hrre : -1<r.re) :
    ‖riemannZeta s*riemannZeta r-d04OneSidedRawSeries X s r‖≤
      (1/(2*Real.pi))*(‖d04OneSidedRightTail X s r R‖+
        ‖d04OneSidedVerticalTruncated X s r a R‖+
        ‖d04OneSidedHorizontalIntegral X s r a (-R)‖+
        ‖d04OneSidedHorizontalIntegral X s r a R‖) := by
  rw [norm_sub_rev, d04OneSidedRawSeries_error_decomposition hX ha ha0 hR s r hs hr hsre hrre,
    norm_mul]
  have hc : ‖(1/(2*Real.pi) : ℂ)‖=1/(2*Real.pi) := by
    simp [Complex.norm_real, abs_of_pos Real.pi_pos]
  rw [hc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ‖d04OneSidedRightTail X s r R+d04OneSidedVerticalTruncated X s r a R‖+
        ‖I*(d04OneSidedHorizontalIntegral X s r a (-R)-
          d04OneSidedHorizontalIntegral X s r a R)‖ := norm_add_le _ _
    _ ≤ (‖d04OneSidedRightTail X s r R‖+‖d04OneSidedVerticalTruncated X s r a R‖)+
        (‖d04OneSidedHorizontalIntegral X s r a (-R)‖+
          ‖d04OneSidedHorizontalIntegral X s r a R‖) := by
      rw [norm_mul, norm_I, one_mul]
      exact add_le_add (norm_add_le _ _) (norm_sub_le _ _)
    _ = _ := by ring

end
end Sechstmoment
