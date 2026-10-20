import SixthMoment.Analysis.Complex.SimplePole
import SixthMoment.Analysis.Gaussian.Decay
import SixthMoment.Zeta.CompletedBounds


namespace SixthMoment
open Complex Real MeasureTheory Filter Set
open scoped Topology
noncomputable section

def d02CompletedPoleRemoved (s : ℂ) : ℂ :=
  s * (1-s) * completedRiemannZeta₀ s - 1

@[fun_prop] theorem d02CompletedPoleRemoved_differentiable :
    Differentiable ℂ d02CompletedPoleRemoved := by
  unfold d02CompletedPoleRemoved
  have hp : Differentiable ℂ (fun s : ℂ => s*(1-s)) := by fun_prop
  exact (hp.mul differentiable_completedZeta₀).sub_const 1

theorem d02CompletedPoleRemoved_eq {s : ℂ} (hs : s ≠ 0) (hs1 : s ≠ 1) :
    d02CompletedPoleRemoved s = s * (1-s) * completedRiemannZeta s := by
  have h1 : 1-s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  rw [d02CompletedPoleRemoved, completedRiemannZeta_eq]
  field_simp
  ring

theorem d02CompletedPoleRemoved_one_sub (s : ℂ) :
    d02CompletedPoleRemoved (1-s) = d02CompletedPoleRemoved s := by
  simp only [d02CompletedPoleRemoved, completedRiemannZeta₀_one_sub]
  ring

def d02SecondAFEContour (s r z : ℂ) : ℂ :=
  Complex.exp (z^2) * (s-z) * (1-s+z) * (r-z) * (1-r+z) *
    d02CompletedPoleRemoved (s+z) * d02CompletedPoleRemoved (r+z)

def d02SecondAFENormalization (s r : ℂ) : ℂ :=
  (s * (1-s) * r * (1-r))^2

def d02SecondAFEPoleKiller (s r z : ℂ) : ℂ :=
  Complex.exp (z^2) *
    ((s+z) * (1-s-z) * (s-z) * (1-s+z) *
      (r+z) * (1-r-z) * (r-z) * (1-r+z)) /
    d02SecondAFENormalization s r

@[fun_prop] theorem d02SecondAFEContour_differentiable (s r : ℂ) :
    Differentiable ℂ (d02SecondAFEContour s r) := by
  unfold d02SecondAFEContour
  fun_prop (disch := exact d02CompletedPoleRemoved_differentiable)

theorem d02SecondAFEContour_reflection (s r z : ℂ) :
    d02SecondAFEContour s r (-z) = d02SecondAFEContour (1-s) (1-r) z := by
  simp only [d02SecondAFEContour, neg_sq, sub_neg_eq_add]
  rw [show s + -z = 1-(1-s+z) by ring,
    show r + -z = 1-(1-r+z) by ring,
    d02CompletedPoleRemoved_one_sub,d02CompletedPoleRemoved_one_sub]
  ring

theorem d02SecondAFEPoleKiller_even (s r z : ℂ) :
    d02SecondAFEPoleKiller s r (-z) = d02SecondAFEPoleKiller s r z := by
  unfold d02SecondAFEPoleKiller
  simp only [neg_sq]
  ring

theorem d02SecondAFENormalization_ne_zero {s r : ℂ}
    (hs : s ≠ 0) (hs1 : s ≠ 1) (hr : r ≠ 0) (hr1 : r ≠ 1) :
    d02SecondAFENormalization s r ≠ 0 := by
  unfold d02SecondAFENormalization
  exact pow_ne_zero _ (mul_ne_zero
    (mul_ne_zero (mul_ne_zero hs (sub_ne_zero.mpr (Ne.symm hs1))) hr)
    (sub_ne_zero.mpr (Ne.symm hr1)))

theorem d02SecondAFEPoleKiller_zero {s r : ℂ}
    (hs : s ≠ 0) (hs1 : s ≠ 1) (hr : r ≠ 0) (hr1 : r ≠ 1) :
    d02SecondAFEPoleKiller s r 0 = 1 := by
  have h := d02SecondAFENormalization_ne_zero hs hs1 hr hr1
  simp only [d02SecondAFEPoleKiller, zero_pow (by norm_num : (2:ℕ) ≠ 0),
    Complex.exp_zero, add_zero, sub_zero, one_mul]
  apply (div_eq_one_iff_eq h).mpr
  unfold d02SecondAFENormalization
  ring

theorem d02SecondAFEContour_eq {s r z : ℂ}
    (hs0 : s ≠ 0) (hs01 : s ≠ 1) (hr0 : r ≠ 0) (hr01 : r ≠ 1)
    (hs : s+z ≠ 0) (hs1 : s+z ≠ 1) (hr : r+z ≠ 0) (hr1 : r+z ≠ 1) :
    d02SecondAFEContour s r z =
      d02SecondAFEPoleKiller s r z * d02SecondAFENormalization s r *
        completedRiemannZeta (s+z) * completedRiemannZeta (r+z) := by
  have hn := d02SecondAFENormalization_ne_zero hs0 hs01 hr0 hr01
  rw [d02SecondAFEContour, d02CompletedPoleRemoved_eq hs hs1,
    d02CompletedPoleRemoved_eq hr hr1, d02SecondAFEPoleKiller]
  field_simp
  ring

theorem d02CompletedPoleRemoved_strip_bound (s : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |z.re| ≤ 1 →
      ‖d02CompletedPoleRemoved (s+z)‖ ≤ C * (1+|z.im|)^2 := by
  obtain ⟨B, hB, hbound⟩ := completedRiemannZeta₀_norm_bounded_on_strip
    (s.re-1) (s.re+1)
  let A : ℝ := 2+‖s‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A^2*B+1, by positivity, ?_⟩
  intro z hz
  let W : ℝ := 1+|z.im|
  have hW : 1 ≤ W := by dsimp [W]; linarith [abs_nonneg z.im]
  have hzn : ‖z‖ ≤ 1+|z.im| :=
    (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)
  have hs : ‖s+z‖ ≤ A*W := by
    have hn := norm_add_le s z
    dsimp [A, W] at *
    nlinarith [norm_nonneg s, abs_nonneg z.im]
  have hs1 : ‖1-(s+z)‖ ≤ A*W := by
    have hn := norm_sub_le (1:ℂ) (s+z)
    have hp := norm_add_le s z
    rw [norm_one] at hn
    dsimp [A, W] at *
    nlinarith [norm_nonneg s, abs_nonneg z.im]
  have hb : ‖completedRiemannZeta₀ (s+z)‖ ≤ B :=
    hbound (s+z) (by simp only [add_re]; linarith [(abs_le.mp hz).1])
      (by simp only [add_re]; linarith [(abs_le.mp hz).2])
  calc
    _ ≤ ‖s+z‖ * ‖1-(s+z)‖ * ‖completedRiemannZeta₀ (s+z)‖ + 1 := by
      simpa only [d02CompletedPoleRemoved, norm_mul, norm_one] using
        norm_sub_le ((s+z)*(1-(s+z))*completedRiemannZeta₀ (s+z)) (1:ℂ)
    _ ≤ (A*W)*(A*W)*B+1 := by gcongr
    _ ≤ (A^2*B+1)*W^2 := by nlinarith [sq_nonneg W, one_le_pow₀ hW (n := 2)]

theorem d02SecondAFEContour_strip_bound (s r : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |z.re| ≤ 1 →
      ‖d02SecondAFEContour s r z‖ ≤
        C * (1+|z.im|)^8 * Real.exp (-z.im^2) := by
  obtain ⟨B, hB, hb⟩ := d02CompletedPoleRemoved_strip_bound s
  obtain ⟨D, hD, hd⟩ := d02CompletedPoleRemoved_strip_bound r
  let A : ℝ := 2+‖s‖+‖r‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨Real.exp 1*A^4*B*D, by positivity, ?_⟩
  intro z hz
  let W : ℝ := 1+|z.im|
  have hW : 1 ≤ W := by dsimp [W]; linarith [abs_nonneg z.im]
  have hzn : ‖z‖ ≤ 1+|z.im| :=
    (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)
  have hfactor (u : ℂ) (hu : ‖u‖ ≤ ‖s‖+‖r‖) :
      ‖u-z‖ ≤ A*W ∧ ‖1-u+z‖ ≤ A*W := by
    have h0 := norm_sub_le u z
    have h1 := norm_add_le (1-u) z
    have h2 := norm_sub_le (1:ℂ) u
    rw [norm_one] at h2
    dsimp [A, W] at *
    constructor <;> nlinarith [abs_nonneg z.im, norm_nonneg s, norm_nonneg r]
  have hs := hfactor s (by linarith [norm_nonneg r])
  have hr := hfactor r (by linarith [norm_nonneg s])
  have he : ‖Complex.exp (z^2)‖ ≤ Real.exp 1*Real.exp (-z.im^2) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hzsq : z.re^2≤1 := by nlinarith [(abs_le.mp hz).1,(abs_le.mp hz).2]
    simp only [pow_two, mul_re]
    nlinarith
  unfold d02SecondAFEContour
  simp only [norm_mul]
  calc
    _ ≤ (Real.exp 1*Real.exp (-z.im^2)) * (A*W) * (A*W) *
        (A*W) * (A*W) * (B*W^2) * (D*W^2) := by
      gcongr
      · exact hs.1
      · exact hs.2
      · exact hr.1
      · exact hr.2
      · exact hb z hz
      · exact hd z hz
    _ = _ := by dsimp [W]; ring

theorem d02SecondAFEContour_vertical_integrable (s r : ℂ) (c : ℝ)
    (hc : |c| ≤ 1) (hc0 : c ≠ 0) :
    Integrable (fun v : ℝ =>
      d02SecondAFEContour s r ((c:ℂ)+(v:ℂ)*I) / ((c:ℂ)+(v:ℂ)*I)) := by
  obtain ⟨C, hC, hb⟩ := d02SecondAFEContour_strip_bound s r
  apply ((gaussianPolynomialExponential_integrable 8 0).const_mul (C/|c|)).mono'
  · have hden : ∀ v : ℝ,((c:ℂ)+(v:ℂ)*I)≠0 := by
      intro v hv
      have h : c=0 := by simpa using congrArg Complex.re hv
      exact hc0 h
    exact (((d02SecondAFEContour_differentiable s r).continuous.comp
      (by fun_prop)).div (by fun_prop) hden).aestronglyMeasurable
  · apply Eventually.of_forall
    intro v
    have hp : 0 < |c| := abs_pos.mpr hc0
    have hn : |c| ≤ ‖((c:ℂ)+(v:ℂ)*I)‖ := by
      simpa using Complex.abs_re_le_norm ((c:ℂ)+(v:ℂ)*I)
    rw [norm_div]
    have h := hb ((c:ℂ)+(v:ℂ)*I) (by simpa using hc)
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re,
      mul_zero, add_zero, zero_add] at h
    calc
      _ ≤ (C*(1+|v|)^8*Real.exp (-v^2))/|c| := div_le_div₀ (by positivity) h hp hn
      _ = _ := by simp only [zero_mul, zero_sub]; ring

theorem d02SecondAFEContour_horizontal_tendsto_zero (s r : ℂ) :
    Tendsto (fun v : ℝ => ∫ c in (-1:ℝ)..1,
      d02SecondAFEContour s r ((c:ℂ)+(v:ℂ)*I) / ((c:ℂ)+(v:ℂ)*I))
      (cocompact ℝ) (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := d02SecondAFEContour_strip_bound s r
  have habs : Tendsto (fun v : ℝ => |v|) (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop]
    exact tendsto_abs_atBot_atTop.sup tendsto_abs_atTop_atTop
  have hlim : Tendsto (fun v : ℝ => 2*C*(1+|v|)^8*Real.exp (-v^2))
      (cocompact ℝ) (𝓝 0) := by
    simpa only [zero_mul, zero_sub, mul_zero, mul_assoc] using
      (gaussianPolynomialExponential_tendsto_zero 8 0).const_mul (2*C)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [habs.eventually (eventually_ge_atTop (1:ℝ))] with v hv
  have hpoint (c : ℝ) (hc : c ∈ uIoc (-1:ℝ) 1) :
      ‖d02SecondAFEContour s r ((c:ℂ)+(v:ℂ)*I) / ((c:ℂ)+(v:ℂ)*I)‖ ≤
        C*(1+|v|)^8*Real.exp (-v^2) := by
    rw [uIoc_of_le (by norm_num)] at hc
    have hn : 1 ≤ ‖((c:ℂ)+(v:ℂ)*I)‖ :=
      hv.trans (by simpa using Complex.abs_im_le_norm ((c:ℂ)+(v:ℂ)*I))
    rw [norm_div]
    apply (div_le_self (norm_nonneg _) hn).trans
    simpa using hb ((c:ℂ)+(v:ℂ)*I) (by simp; exact abs_le.mpr ⟨hc.1.le, hc.2⟩)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  convert h using 1
  ring_nf

theorem d02SecondAFEContour_split (s r : ℂ) :
    (∫ v : ℝ, d02SecondAFEContour s r (1+(v:ℂ)*I)/(1+(v:ℂ)*I)) +
      (∫ v : ℝ, d02SecondAFEContour (1-s) (1-r) (1+(v:ℂ)*I)/(1+(v:ℂ)*I)) =
        (2*Real.pi:ℂ) * d02SecondAFEContour s r 0 := by
  have h := mellinRectangle_simplePole_shift (d02SecondAFEContour s r)
    isOpen_univ (d02SecondAFEContour_differentiable s r).differentiableOn
    (a := -1) (b := 1) (by norm_num) (by norm_num)
    (fun _ _ _ => mem_univ _)
    (d02SecondAFEContour_vertical_integrable s r (-1) (by norm_num) (by norm_num))
    (d02SecondAFEContour_vertical_integrable s r 1 (by norm_num) (by norm_num))
    (d02SecondAFEContour_horizontal_tendsto_zero s r)
  have hleft : (∫ v : ℝ, d02SecondAFEContour s r (-1+(v:ℂ)*I)/(-1+(v:ℂ)*I)) =
      -(∫ v : ℝ, d02SecondAFEContour (1-s) (1-r) (1+(v:ℂ)*I)/(1+(v:ℂ)*I)) := by
    rw [← integral_neg]
    have hneg : (∫ v : ℝ, d02SecondAFEContour s r (-1+((-v:ℝ):ℂ)*I)/
        (-1+((-v:ℝ):ℂ)*I)) =
        ∫ v : ℝ, d02SecondAFEContour s r (-1+(v:ℂ)*I)/(-1+(v:ℂ)*I) := by
      simpa only [neg_one_mul,inv_neg,abs_neg,abs_one,inv_one,one_smul] using
        Measure.integral_comp_mul_left (fun v : ℝ =>
          d02SecondAFEContour s r (-1+(v:ℂ)*I)/(-1+(v:ℂ)*I)) (-1)
    rw [←hneg]
    apply integral_congr_ae
    exact Eventually.of_forall fun v => by
      dsimp only
      have he : (-1:ℂ)+((-v:ℝ):ℂ)*I = -(1+(v:ℂ)*I) := by push_cast; ring
      rw [he, d02SecondAFEContour_reflection, div_neg]
  norm_num only [Complex.ofReal_one,Complex.ofReal_neg] at h
  rw [hleft] at h
  linear_combination h

theorem d02SecondAFEContour_zero {s r : ℂ}
    (hs : s ≠ 0) (hs1 : s ≠ 1) (hr : r ≠ 0) (hr1 : r ≠ 1) :
    d02SecondAFEContour s r 0 = d02SecondAFENormalization s r *
      completedRiemannZeta s * completedRiemannZeta r := by
  simp only [d02SecondAFEContour, zero_pow (by norm_num : (2:ℕ) ≠ 0),
    Complex.exp_zero, sub_zero, add_zero, one_mul]
  rw [d02CompletedPoleRemoved_eq hs hs1, d02CompletedPoleRemoved_eq hr hr1]
  unfold d02SecondAFENormalization
  ring

theorem d02SecondAFENormalization_reflection (s r : ℂ) :
    d02SecondAFENormalization (1-s) (1-r) = d02SecondAFENormalization s r := by
  unfold d02SecondAFENormalization
  ring

def d02SecondAFECompletedIntegral (s r : ℂ) : ℂ :=
  (∫ v : ℝ, d02SecondAFEContour s r (1+(v:ℂ)*I)/(1+(v:ℂ)*I)) /
    ((2*Real.pi:ℂ) * d02SecondAFENormalization s r)

theorem d02CompletedPair_secondAFE {s r : ℂ}
    (hs : s ≠ 0) (hs1 : s ≠ 1) (hr : r ≠ 0) (hr1 : r ≠ 1) :
    completedRiemannZeta s * completedRiemannZeta r =
      d02SecondAFECompletedIntegral s r +
        d02SecondAFECompletedIntegral (1-s) (1-r) := by
  have hn := d02SecondAFENormalization_ne_zero hs hs1 hr hr1
  have hp : (2*Real.pi:ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have h := d02SecondAFEContour_split s r
  rw [d02SecondAFEContour_zero hs hs1 hr hr1] at h
  unfold d02SecondAFECompletedIntegral
  rw [d02SecondAFENormalization_reflection, ← add_div, h]
  field_simp

def d02SecondAFEIntegral (s r : ℂ) : ℂ :=
  d02SecondAFECompletedIntegral s r / (Gammaℝ s * Gammaℝ r)

def d02SecondAFEDualMultiplier (s r : ℂ) : ℂ :=
  (Gammaℝ (1-s) * Gammaℝ (1-r)) / (Gammaℝ s * Gammaℝ r)

theorem d02ZetaPair_secondAFE {s r : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1) (hr : 0 < r.re) (hr1 : r.re < 1) :
    riemannZeta s * riemannZeta r =
      d02SecondAFEIntegral s r + d02SecondAFEDualMultiplier s r *
        d02SecondAFEIntegral (1-s) (1-r) := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hr0 : r ≠ 0 := by intro h; simp [h] at hr
  have hsne : s ≠ 1 := by intro h; simp [h] at hs1
  have hrne : r ≠ 1 := by intro h; simp [h] at hr1
  have hgs := Gammaℝ_ne_zero_of_re_pos hs
  have hgr := Gammaℝ_ne_zero_of_re_pos hr
  have hgs1 := Gammaℝ_ne_zero_of_re_pos (s := 1-s) (by simp; linarith)
  have hgr1 := Gammaℝ_ne_zero_of_re_pos (s := 1-r) (by simp; linarith)
  rw [riemannZeta_def_of_ne_zero hs0, riemannZeta_def_of_ne_zero hr0,
    ← mul_div_mul_comm, d02CompletedPair_secondAFE hs0 hsne hr0 hrne]
  unfold d02SecondAFEIntegral d02SecondAFEDualMultiplier
  field_simp

end
end SixthMoment
