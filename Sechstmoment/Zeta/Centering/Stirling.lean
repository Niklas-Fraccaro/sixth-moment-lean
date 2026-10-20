import Mathlib.Tactic.FieldSimp
import Sechstmoment.Zeta.Centering.GammaRatio


namespace Sechstmoment
open Complex Filter
open scoped BigOperators Topology
noncomputable section

def normalizedGammaRatio (s u : ℂ) : ℂ :=
  (Gamma (s+u)/Gamma s)/s^u

def centeringFactorAt (T : ℝ) (s z : ℂ) : ℂ :=
  Complex.exp z * zetaChi (s+z/(Real.log T : ℂ))/zetaChi s

@[simp] theorem centeringFactorAt_criticalLinePoint (T t : ℝ) (z : ℂ) :
    centeringFactorAt T (criticalLinePoint t) z = centeringFactor T t z := rfl

def gammaChiMainPhase (s u z : ℂ) : ℂ :=
  Complex.exp z * (Real.pi : ℂ)^u *
    ((1-s)/2)^(-u/2) * (s/2)^(-u/2)

private theorem gamma_ne_zero_nonreal {s : ℂ} (hs : s.im ≠ 0) : Gamma s ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro n h
  apply hs
  simpa only [Complex.neg_im, Complex.natCast_im, neg_zero] using congrArg Complex.im h

private theorem point_ne_zero_nonreal {s : ℂ} (hs : s.im ≠ 0) : s ≠ 0 := by
  intro h
  exact hs (by simp [h])

theorem centeringFactorAt_eq_gamma_ratios (T : ℝ) (s z : ℂ)
    (hs : s.im ≠ 0) (hw : (s+z/(Real.log T : ℂ)).im ≠ 0) :
    centeringFactorAt T s z =
      gammaChiMainPhase s (z/(Real.log T : ℂ)) z *
        (normalizedGammaRatio ((1-s)/2) (-(z/(Real.log T : ℂ))/2) /
          normalizedGammaRatio (s/2) ((z/(Real.log T : ℂ))/2)) := by
  let u : ℂ := z/(Real.log T : ℂ)
  have ha : ((1-s)/2).im ≠ 0 := by simpa only [Complex.div_ofNat_im,
    Complex.sub_im, Complex.one_im, zero_sub, neg_div, ne_eq, neg_eq_zero, div_eq_zero_iff,
    OfNat.ofNat_ne_zero, or_false] using hs
  have hb : (s/2).im ≠ 0 := by simpa only [Complex.div_ofNat_im,
    ne_eq, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false] using hs
  have hbu : ((s+u)/2).im ≠ 0 := by
    simpa only [Complex.div_ofNat_im, ne_eq, div_eq_zero_iff,
      OfNat.ofNat_ne_zero, or_false] using hw
  have hpa : ((1-s)/2)^(-u/2) ≠ 0 := by
    simp [Complex.cpow_eq_zero_iff, point_ne_zero_nonreal ha]
  have hpa' : ((1-s)/2)^(u/2) ≠ 0 := by
    simp [Complex.cpow_eq_zero_iff, point_ne_zero_nonreal ha]
  have hpb : (s/2)^(u/2) ≠ 0 := by
    simp [Complex.cpow_eq_zero_iff, point_ne_zero_nonreal hb]
  have hga := gamma_ne_zero_nonreal ha
  have hgb := gamma_ne_zero_nonreal hb
  have hgbu := gamma_ne_zero_nonreal hbu
  have hae : (1-s)/2+(-u)/2 = (1-s-u)/2 := by ring
  have hbe : s/2+u/2 = (s+u)/2 := by ring
  change Complex.exp z*zetaChi (s+u)/zetaChi s = _
  rw [mul_div_assoc, zetaChi_shift_ratio]
  unfold gammaChiMainPhase normalizedGammaRatio
  change _ = Complex.exp z*(Real.pi : ℂ)^u*((1-s)/2)^(-u/2)*(s/2)^(-u/2) *
    ((Gamma ((1-s)/2+(-u)/2)/Gamma ((1-s)/2))/((1-s)/2)^(-u/2) /
      ((Gamma (s/2+u/2)/Gamma (s/2))/(s/2)^(u/2)))
  rw [hae, hbe, show -u/2 = -(u/2) by ring]
  simp only [Complex.cpow_neg]
  field_simp

theorem norm_div_sub_one_le_four {a b : ℂ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hsmall : δ ≤ 1/2)
    (ha : ‖a-1‖ ≤ δ) (hb : ‖b-1‖ ≤ δ) :
    ‖a/b-1‖ ≤ 4*δ := by
  have hbn : 1-δ ≤ ‖b‖ := by
    have h := norm_sub_norm_le (1 : ℂ) b
    rw [norm_one, norm_sub_rev] at h
    linarith
  have hpos : 0 < ‖b‖ := by linarith
  have hb0 : b ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hpos)
  rw [div_sub_one hb0, norm_div, div_le_iff₀ hpos]
  have hnum : ‖a-b‖ ≤ 2*δ := by
    have he : a-b = (a-1)-(b-1) := by ring
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith)
  have hm := mul_le_mul_of_nonneg_left hbn (by positivity : 0 ≤ 4*δ)
  nlinarith

theorem centeringFactorAt_error_bound (T : ℝ) (s z : ℂ)
    (hs : s.im ≠ 0) (hw : (s+z/(Real.log T : ℂ)).im ≠ 0)
    {δ E : ℝ} (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1/2) (hE : E ≤ 1)
    (ha : ‖normalizedGammaRatio ((1-s)/2) (-(z/(Real.log T : ℂ))/2)-1‖ ≤ δ)
    (hb : ‖normalizedGammaRatio (s/2) ((z/(Real.log T : ℂ))/2)-1‖ ≤ δ)
    (hp : ‖gammaChiMainPhase s (z/(Real.log T : ℂ)) z-1‖ ≤ E) :
    ‖centeringFactorAt T s z-1‖ ≤ 8*δ+E := by
  rw [centeringFactorAt_eq_gamma_ratios T s z hs hw]
  let p := gammaChiMainPhase s (z/(Real.log T : ℂ)) z
  let r := normalizedGammaRatio ((1-s)/2) (-(z/(Real.log T : ℂ))/2) /
    normalizedGammaRatio (s/2) ((z/(Real.log T : ℂ))/2)
  have hr : ‖r-1‖ ≤ 4*δ := norm_div_sub_one_le_four hδ hδsmall ha hb
  have hpn : ‖p‖ ≤ 2 := by
    have he : p = (p-1)+1 := by ring
    have hn : ‖p‖ ≤ ‖p-1‖+1 := by
      nth_rw 1 [he]
      simpa only [norm_one] using norm_add_le (p-1) (1 : ℂ)
    linarith
  change ‖p*r-1‖ ≤ _
  have he : p*r-1 = p*(r-1)+(p-1) := by ring
  rw [he]
  calc
    _ ≤ ‖p*(r-1)‖+‖p-1‖ := norm_add_le _ _
    _ = ‖p‖*‖r-1‖+‖p-1‖ := by rw [norm_mul]
    _ ≤ 2*(4*δ)+E := add_le_add
      (mul_le_mul hpn hr (norm_nonneg _) (by norm_num)) hp
    _ = _ := by ring

end
end Sechstmoment
