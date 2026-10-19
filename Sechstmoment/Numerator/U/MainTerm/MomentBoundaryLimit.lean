import Sechstmoment.Numerator.U.MainTerm.CauchyBoundary
import Sechstmoment.Numerator.U.OffDiagonal

/-!
# The actual normalized fourth moment on the separated Cauchy boundary

The source-only A03 discrepancy is divided by the actual normalization
`T * log(T)^9`. Combining this uniform zero limit with the existing A04
six-main-term boundary limit proves the boundary limit of the literal
`twistedFourthMoment`, under only the two unchanged BBLR paper inputs.

The profiles and dyadic time weight are fixed before `T`. This module does
not identify the boundary limit with a regular manuscript generator and
does not claim collision continuation or derivative convergence.
-/

namespace Sechstmoment
open Complex Real Source Set Filter
open scoped Topology
noncomputable section

set_option maxHeartbeats 2000000

private theorem uniform_oT_div_time_log_pow_tendsto_zero
    {ι : Type*} (E : ℝ → ι → ℂ) (K : Set ι) (n : ℕ)
    (hE : ∀ δ : ℝ, 0 < δ → ∀ᶠ T : ℝ in atTop, ∀ x ∈ K, ‖E T x‖ ≤ δ*T) :
    TendstoUniformlyOn
      (fun T : ℝ => fun x : ι => E T x / ((T:ℂ)*(Real.log T:ℂ)^n))
      (fun _ => (0:ℂ)) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hE (ε/2) (by positivity), eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with T hET hT hL x hx
  have hTp : 0 < T := zero_lt_one.trans hT
  have hLp : 0 < Real.log T := Real.log_pos hT
  have hn : ‖E T x‖ ≤ (ε/2)*T := hET x hx
  have hp : 1 ≤ (Real.log T)^n := one_le_pow₀ hL
  rw [dist_eq_norm, zero_sub, norm_neg, norm_div, norm_mul, norm_pow]
  simp only [Complex.norm_real, Real.norm_of_nonneg hTp.le,
    Real.norm_of_nonneg hLp.le]
  calc
    _ ≤ ε/2 := (div_le_iff₀ (by positivity : 0 < T*(Real.log T)^n)).mpr (by
      have hd : T ≤ T*(Real.log T)^n := by nlinarith
      exact hn.trans (mul_le_mul_of_nonneg_left hd (by positivity)))
    _ < ε := by linarith

/-- The actual A03 discrepancy is negligible after the literal moment
normalization, uniformly on every compact shift set with a fixed root gap.
There is no additional asymptotic or reconstruction hypothesis. -/
theorem a03SourceOnly_normalized_discrepancy_uniform_zero
    (hAFE : BBLRv1FixedApproximateFEInput) (hSource : SeparatedQuadraticInput)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hlen : 3*a+5*b < 2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0 < κ)
    (hroot : ∀ σ ∈ K, ∀ k : PurePolarIndex, κ ≤ ‖normalizedPurePolarRoot σ k‖)
    (f g Φ : ℝ → ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) :
    TendstoUniformlyOn
      (fun T : ℝ => fun σ : MomentShifts =>
        bblrMomentDiscrepancy T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ /
          ((T:ℂ)*(Real.log T:ℂ)^9))
      (fun _ => (0:ℂ)) atTop K :=
  uniform_oT_div_time_log_pow_tendsto_zero
    (fun T σ => bblrMomentDiscrepancy T a b (rawMomentShifts T σ)
      (polarPoleKiller T σ) f g Φ) K 9
    (a03SourceOnly_uniform_oT hAFE hSource ha hab hlen K hK hκ hroot f g Φ hf hg hΦ)

/-- The literal normalized twisted fourth moment converges uniformly on
the fixed distinguished boundary of radii `1,2,4,8`. Its limit is the actual
six-term polar-profile limit, with the existing contour parameter `33`.
Only the original fixed-AFE and oriented BBLR paper inputs are assumed. -/
theorem twistedFourthMoment_normalized_uniform_on_dpCauchyBoundary
    (hAFE : BBLRv1FixedApproximateFEInput) (hSource : SeparatedQuadraticInput)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hlen : 3*a+5*b < 2)
    (f g Φ : ℝ → ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) :
    TendstoUniformlyOn
      (fun T : ℝ => fun σ : MomentShifts =>
        twistedFourthMoment T (rawMomentShifts T σ) f g Φ /
          ((T:ℂ)*(Real.log T:ℂ)^9))
      (fun σ => actualSixPrincipalPolarLimit σ (fun x => (f x:ℂ))
        (fun x => (g x:ℂ)) Φ 33) atTop
      (rectangularDistinguishedBoundary dpCauchyRadii) := by
  have hsum : a+b < 1 := by linarith
  have hmain := bblrSixMainTerms_polar_uniform_on_dpCauchyBoundary
    hsum f g Φ hf hg hΦ
  have herr := a03SourceOnly_normalized_discrepancy_uniform_zero
    hAFE hSource ha hab hlen (rectangularDistinguishedBoundary dpCauchyRadii)
    dpCauchyBoundary_isCompact (κ := 1/2) (by norm_num)
    dpCauchyBoundary_pure_root_gap f g Φ hf hg hΦ
  rw [Metric.tendstoUniformlyOn_iff] at hmain herr ⊢
  intro ε hε
  filter_upwards [hmain (ε/2) (by positivity), herr (ε/2) (by positivity)]
    with T hM hE σ hσ
  have hMσ := hM σ hσ
  have hEσ := hE σ hσ
  rw [dist_eq_norm] at hMσ ⊢
  rw [dist_eq_norm, zero_sub, norm_neg] at hEσ
  calc
    _ = ‖(actualSixPrincipalPolarLimit σ (fun x => (f x:ℂ))
          (fun x => (g x:ℂ)) Φ 33 -
          bblrSixMainTerms T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ /
            ((T:ℂ)*(Real.log T:ℂ)^9)) -
        bblrMomentDiscrepancy T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ /
          ((T:ℂ)*(Real.log T:ℂ)^9)‖ := by
      congr 1
      unfold bblrMomentDiscrepancy
      ring
    _ ≤ ‖actualSixPrincipalPolarLimit σ (fun x => (f x:ℂ))
          (fun x => (g x:ℂ)) Φ 33 -
          bblrSixMainTerms T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ /
            ((T:ℂ)*(Real.log T:ℂ)^9)‖ +
        ‖bblrMomentDiscrepancy T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ /
          ((T:ℂ)*(Real.log T:ℂ)^9)‖ := norm_sub_le _ _
    _ < ε := by linarith

end
end Sechstmoment
