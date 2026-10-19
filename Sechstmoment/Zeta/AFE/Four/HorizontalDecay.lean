import Sechstmoment.Zeta.Bounds.UniformStrip

/-!
# Uniform bounds on the finite fourfold AFE rectangle

The exponential Gamma factors cancel exactly, because the four original
heights have two positive and two negative signs.  This module proves the
cancellation, including the global inequality outside the finite rectangle.
It does not assume an approximate functional equation.
-/

namespace Sechstmoment.Source

open Complex Filter Set
open scoped BigOperators Topology

noncomputable section

/-- A balanced collection of two positive and two negative heights minimizes
its sum of absolute values under a common translation at translation zero. -/
theorem four_heights_abs_sum_le (x : Fin 4 → ℝ) (v : ℝ)
    (h0 : 0 ≤ x 0) (h1 : 0 ≤ x 1) (h2 : x 2 ≤ 0) (h3 : x 3 ≤ 0) :
    (∑ j : Fin 4, |x j|) ≤ ∑ j : Fin 4, |x j + v| := by
  simp only [Fin.sum_univ_succ, Fin.isValue, Fin.reduceSucc, Fin.sum_univ_zero, add_zero]
  rw [abs_of_nonneg h0, abs_of_nonneg h1, abs_of_nonpos h2, abs_of_nonpos h3]
  linarith [le_abs_self (x 0+v), le_abs_self (x 1+v),
    neg_le_abs (x 2+v), neg_le_abs (x 3+v)]

/-- On an interval where the four signs remain unchanged, the preceding
inequality is an exact equality. -/
theorem four_heights_abs_sum_eq (x : Fin 4 → ℝ) (v : ℝ)
    (h0 : 0 ≤ x 0) (h1 : 0 ≤ x 1) (h2 : x 2 ≤ 0) (h3 : x 3 ≤ 0)
    (hv0 : 0 ≤ x 0+v) (hv1 : 0 ≤ x 1+v)
    (hv2 : x 2+v ≤ 0) (hv3 : x 3+v ≤ 0) :
    (∑ j : Fin 4, |x j+v|) = ∑ j : Fin 4, |x j| := by
  simp only [Fin.sum_univ_succ, Fin.isValue, Fin.reduceSucc, Fin.sum_univ_zero, add_zero]
  rw [abs_of_nonneg h0, abs_of_nonneg h1, abs_of_nonpos h2, abs_of_nonpos h3,
    abs_of_nonneg hv0, abs_of_nonneg hv1, abs_of_nonpos hv2, abs_of_nonpos hv3]
  ring

private theorem bblr_shifted_height_signs (t v : ℝ) (ht : 1 ≤ t)
    (hv : |v| ≤ t/2) (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    0 ≤ (sourceZetaPoints t 0+α 0).im+v ∧
    0 ≤ (sourceZetaPoints t 1+α 1).im+v ∧
    (sourceZetaPoints t 2+α 2).im+v ≤ 0 ∧
    (sourceZetaPoints t 3+α 3).im+v ≤ 0 := by
  have ha (j : Fin 4) := abs_le.mp ((Complex.abs_im_le_norm (α j)).trans (hα j))
  have ha0 := ha 0
  have ha1 := ha 1
  have ha2 := ha 2
  have ha3 := ha 3
  have hv' := abs_le.mp hv
  simp [sourceZetaPoints, criticalLinePoint]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The global Gamma exponential factor is at most one; there is no
exponential loss even on the two infinite tails. -/
theorem bblr_gamma_imaginary_abs_sum_le (t v : ℝ) (ht : 1 ≤ t)
    (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ 1/4) (c : ℝ) :
    (∑ j : Fin 4, |((sourceZetaPoints t j+α j)/2).im|) ≤
      ∑ j : Fin 4, |((sourceZetaPoints t j+α j+((c : ℂ)+(v : ℂ)*I))/2).im| := by
  have hs := bblr_shifted_height_signs t 0 ht (by rw [abs_zero]; linarith) α hα
  simp only [add_zero] at hs
  have h := four_heights_abs_sum_le
    (fun j => (sourceZetaPoints t j+α j).im) v hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  simp only [Complex.div_ofNat_im, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
    mul_one, mul_zero, add_zero, zero_add, abs_div, abs_of_pos (by norm_num : (0 : ℝ)<2)]
  simpa only [← Finset.sum_div, Complex.add_im] using
    (div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 2))

/-- Exact cancellation throughout the finite AFE rectangle. -/
theorem bblr_gamma_imaginary_abs_sum_eq (t v : ℝ) (ht : 1 ≤ t)
    (hv : |v| ≤ t/2) (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ 1/4) (c : ℝ) :
    (∑ j : Fin 4, |((sourceZetaPoints t j+α j+((c : ℂ)+(v : ℂ)*I))/2).im|) =
      ∑ j : Fin 4, |((sourceZetaPoints t j+α j)/2).im| := by
  have hs := bblr_shifted_height_signs t 0 ht (by rw [abs_zero]; linarith) α hα
  simp only [add_zero] at hs
  have hs' := bblr_shifted_height_signs t v ht hv α hα
  have h := four_heights_abs_sum_eq
    (fun j => (sourceZetaPoints t j+α j).im) v hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
      hs'.1 hs'.2.1 hs'.2.2.1 hs'.2.2.2
  simp only [Complex.div_ofNat_im, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
    mul_one, mul_zero, add_zero, zero_add, abs_div, abs_of_pos (by norm_num : (0 : ℝ)<2)]
  simpa only [← Finset.sum_div, Complex.add_im] using congrArg (fun x : ℝ => x/2) h

/-- A coarse bound on the actual fourfold Gamma quotient, uniform on the
whole finite rectangle.  In particular it applies on both horizontal edges.
The degree 24 is four numerator degrees five plus four denominator degrees one. -/
theorem bblrGammaQuotient_polynomial_rectangle_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t c v : ℝ, 16 ≤ t → |c| ≤ 1 → |v| ≤ t/2 →
      ∀ α : MomentShifts, (∀ j, ‖α j‖ ≤ 1/4) →
      ‖bblrGammaQuotient t α ((c : ℂ)+(v : ℂ)*I)‖ ≤ C*(1+t)^24 := by
  obtain ⟨D,hD,hΓ⟩ := Sechstmoment.d04Gamma_vertical_strip_norm_le
  obtain ⟨E,hE,hΓinv⟩ := gamma_positive_strip_envelopes
  refine ⟨(D*E)^4, by positivity, ?_⟩
  intro t c v ht hc hv α hα
  let a : Fin 4 → ℂ := fun j =>
    (sourceZetaPoints t j+α j+((c : ℂ)+(v : ℂ)*I))/2
  let b : Fin 4 → ℂ := fun j => (sourceZetaPoints t j+α j)/2
  let P : ℝ := 1+t
  have hP : 0 < P := by dsimp [P]; linarith
  have hRe (j : Fin 4) : -1 ≤ (a j).re ∧ (a j).re ≤ 2 ∧
      (b j).re ∈ Icc (1/8 : ℝ) (7/8) := by
    have ha := abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))
    have hc' := abs_le.mp hc
    dsimp [a,b]
    simp only [Complex.div_ofNat_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_self, sourceZetaPoints_re, add_zero]
    exact ⟨by linarith, by linarith, by constructor <;> linarith⟩
  have hbase (j : Fin 4) : |(sourceZetaPoints t j).im| = t := by
    fin_cases j <;> simp [sourceZetaPoints, criticalLinePoint,
      abs_of_nonneg (by linarith : 0 ≤ t)]
  have hIm (j : Fin 4) : 1+|(a j).im| ≤ P ∧ 1+|(b j).im| ≤ P := by
    have ha := (Complex.abs_im_le_norm (α j)).trans (hα j)
    have hba := abs_add_le (sourceZetaPoints t j).im (α j).im
    rw [hbase j] at hba
    have haa := abs_add_le ((sourceZetaPoints t j).im+(α j).im) v
    dsimp [a,b,P]
    simp only [Complex.div_ofNat_im, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
      mul_one, mul_zero, add_zero, zero_add, abs_div,
      show |(2 : ℝ)| = 2 by norm_num]
    constructor <;> linarith [abs_nonneg v]
  have hImLow (j : Fin 4) : 1 ≤ |(a j).im| := by
    have ha := abs_le.mp ((Complex.abs_im_le_norm (α j)).trans (hα j))
    have hv' := abs_le.mp hv
    have hpos := le_abs_self ((sourceZetaPoints t j).im+(α j).im+v)
    have hneg := neg_le_abs ((sourceZetaPoints t j).im+(α j).im+v)
    dsimp [a]
    simp only [Complex.div_ofNat_im, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
      mul_one, mul_zero, add_zero, zero_add, abs_div,
      show |(2 : ℝ)| = 2 by norm_num]
    fin_cases j <;>
      simp [sourceZetaPoints, criticalLinePoint] at ha hpos hneg ⊢ <;> linarith
  have hFactor (j : Fin 4) : ‖Gamma (a j)/Gamma (b j)‖ ≤
      (D*E*P^6)*Real.exp (Real.pi*(|(b j).im|-|(a j).im|)/2) := by
    have hn := hΓ (a j) (hRe j).1 (hRe j).2.1 (hImLow j)
    have hd := (hΓinv (b j) (hRe j).2.2).2
    rw [norm_div, div_eq_mul_inv]
    calc
      _ ≤ (D*(1+|(a j).im|)^5*Real.exp (-(Real.pi*|(a j).im|/2)))*
          (E*(1+|(b j).im|)*Real.exp (Real.pi*|(b j).im|/2)) := by gcongr
      _ ≤ (D*P^5*Real.exp (-(Real.pi*|(a j).im|/2)))*
          (E*P*Real.exp (Real.pi*|(b j).im|/2)) := by
        gcongr
        · exact (hIm j).1
        · exact (hIm j).2
      _ = _ := by
        rw [show (D*P^5*Real.exp (-(Real.pi*|(a j).im|/2)))*
            (E*P*Real.exp (Real.pi*|(b j).im|/2)) =
            (D*E*P^6)*(Real.exp (-(Real.pi*|(a j).im|/2))*
              Real.exp (Real.pi*|(b j).im|/2)) by ring, ← Real.exp_add]
        congr 2
        ring
  have hsum : (∑ j : Fin 4, Real.pi*(|(b j).im|-|(a j).im|)/2) = 0 := by
    have hs := bblr_gamma_imaginary_abs_sum_eq t v (by linarith) hv α hα c
    change (∑ j : Fin 4, |(a j).im|) = ∑ j : Fin 4, |(b j).im| at hs
    calc
      _ = (Real.pi/2)*((∑ j : Fin 4, |(b j).im|)-
          (∑ j : Fin 4, |(a j).im|)) := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by rw [hs]; ring
  change ‖∏ j : Fin 4, Gamma (a j)/Gamma (b j)‖ ≤ _
  rw [norm_prod]
  calc
    _ ≤ ∏ j : Fin 4, (D*E*P^6)*Real.exp (Real.pi*(|(b j).im|-|(a j).im|)/2) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hFactor j)
    _ = (D*E*P^6)^4*Real.exp
        (∑ j : Fin 4, Real.pi*(|(b j).im|-|(a j).im|)/2) := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      simp
    _ = (D*E)^4*(1+t)^24 := by rw [hsum, Real.exp_zero]; dsimp [P]; ring

/-- Uniform polynomial control of the product of the four zeta factors on
the finite rectangle.  All four points stay a fixed distance from the pole. -/
theorem bblrZetaProduct_polynomial_rectangle_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t c v : ℝ, 16 ≤ t → |c| ≤ 1 → |v| ≤ t/2 →
      ∀ α : MomentShifts, (∀ j, ‖α j‖ ≤ 1/4) →
      ‖∏ j : Fin 4, riemannZeta
        (sourceZetaPoints t j+α j+((c : ℂ)+(v : ℂ)*I))‖ ≤ C*(1+t)^24 := by
  obtain ⟨D,hD,hζ⟩ :=
    Sechstmoment.d04RiemannZeta_polynomial_strip_away_pole
      (a := -1) (b := 2) (r := 1) (by norm_num) (by norm_num)
  refine ⟨(D*2^6)^4, by positivity, ?_⟩
  intro t c v ht hc hv α hα
  let s : Fin 4 → ℂ := fun j =>
    sourceZetaPoints t j+α j+((c : ℂ)+(v : ℂ)*I)
  have hRe (j : Fin 4) : -1 ≤ (s j).re ∧ (s j).re ≤ 2 := by
    have ha := abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))
    have hc' := abs_le.mp hc
    dsimp [s]
    simp only [Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_self, sourceZetaPoints_re, add_zero]
    constructor <;> linarith
  have hImLow (j : Fin 4) : 1 ≤ |(s j).im| := by
    have ha := abs_le.mp ((Complex.abs_im_le_norm (α j)).trans (hα j))
    have hv' := abs_le.mp hv
    have hpos := le_abs_self ((sourceZetaPoints t j).im+(α j).im+v)
    have hneg := neg_le_abs ((sourceZetaPoints t j).im+(α j).im+v)
    dsimp [s]
    simp only [Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
      add_zero, zero_add]
    fin_cases j <;>
      simp [sourceZetaPoints, criticalLinePoint] at ha hpos hneg ⊢ <;> linarith
  have hImHigh (j : Fin 4) : 1+|(s j).im| ≤ 2*(1+t) := by
    have ha := (Complex.abs_im_le_norm (α j)).trans (hα j)
    have hp : |(sourceZetaPoints t j).im| = t := by
      fin_cases j <;> simp [sourceZetaPoints, criticalLinePoint,
        abs_of_nonneg (by linarith : 0 ≤ t)]
    have hba := abs_add_le (sourceZetaPoints t j).im (α j).im
    rw [hp] at hba
    have haa := abs_add_le ((sourceZetaPoints t j).im+(α j).im) v
    dsimp [s]
    simp only [Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
      add_zero, zero_add]
    linarith
  have hFactor (j : Fin 4) : ‖riemannZeta (s j)‖ ≤ (D*2^6)*(1+t)^6 := by
    have hsep : 1 ≤ ‖s j-1‖ := by
      have hh := Complex.abs_im_le_norm (s j-1)
      exact (hImLow j).trans (by simpa using hh)
    calc
      _ ≤ D*(1+|(s j).im|)^6 := hζ (s j) (hRe j).1 (hRe j).2 hsep
      _ ≤ D*(2*(1+t))^6 := by gcongr; exact hImHigh j
      _ = _ := by ring
  change ‖∏ j : Fin 4, riemannZeta (s j)‖ ≤ _
  rw [norm_prod]
  calc
    _ ≤ ∏ j : Fin 4, (D*2^6)*(1+t)^6 :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hFactor j)
    _ = (D*2^6)^4*(1+t)^24 := by simp; ring

/-- The polynomial degree budget before inserting the rapidly decreasing
weight: 24 from zeta and 24 from the Gamma quotient. -/
theorem bblrGammaZetaProduct_polynomial_rectangle_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t c v : ℝ, 16 ≤ t → |c| ≤ 1 → |v| ≤ t/2 →
      ∀ α : MomentShifts, (∀ j, ‖α j‖ ≤ 1/4) →
      ‖bblrGammaQuotient t α ((c : ℂ)+(v : ℂ)*I) *
        ∏ j : Fin 4, riemannZeta
          (sourceZetaPoints t j+α j+((c : ℂ)+(v : ℂ)*I))‖ ≤ C*(1+t)^48 := by
  obtain ⟨CΓ,hCΓ,hΓ⟩ := bblrGammaQuotient_polynomial_rectangle_bound
  obtain ⟨Cζ,hCζ,hζ⟩ := bblrZetaProduct_polynomial_rectangle_bound
  refine ⟨CΓ*Cζ, mul_nonneg hCΓ.le hCζ, ?_⟩
  intro t c v ht hc hv α hα
  rw [norm_mul]
  calc
    _ ≤ (CΓ*(1+t)^24)*(Cζ*(1+t)^24) := by
      exact mul_le_mul (hΓ t c v ht hc hv α hα) (hζ t c v ht hc hv α hα)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The explicit Gamma/zeta form of the Mellin integrand, including its
simple pole at zero.  Its identification with the completed kernel is a
separate algebraic functional-equation step. -/
def bblrExplicitAFEIntegrand (G : ℂ → ℂ) (α : MomentShifts) (t : ℝ) (z : ℂ) : ℂ :=
  G z/z * (bblrGammaQuotient t α z *
    ∏ j : Fin 4, riemannZeta (sourceZetaPoints t j+α j+z)) *
      (Real.pi : ℂ)^(-2*z)

/-- A weighted horizontal estimate that retains natural powers only.
Taking `N = A+47` yields an error of arbitrary inverse-polynomial
order.  Both horizontal edges are covered by the single condition `|v|=t/2`. -/
theorem bblrExplicitAFEIntegrand_horizontal_weighted_bound
    (G : ℂ → ℂ) (hG : BBLREntireWeight G (fun _ => 0)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t c v : ℝ, 16 ≤ t → |c| ≤ 1 → |v| = t/2 →
      ∀ α : MomentShifts, (∀ j, ‖α j‖ ≤ 1/4) →
      ‖bblrExplicitAFEIntegrand G α t ((c : ℂ)+(v : ℂ)*I)‖ *
        (1+t/2)^N ≤ C*(1+t)^48/t := by
  obtain ⟨D,hD,hbound⟩ := bblrGammaZetaProduct_polynomial_rectangle_bound
  obtain ⟨E,hE,hweight⟩ := hG.2.2.2 1 (by norm_num) N
  refine ⟨2*E*D*Real.pi^2, by positivity, ?_⟩
  intro t c v ht hc hv α hα
  have ht0 : 0 < t := by linarith
  let z : ℂ := (c : ℂ)+(v : ℂ)*I
  have hz : t/2 ≤ ‖z‖ := by
    have hh := Complex.abs_im_le_norm z
    simpa only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
      add_zero, zero_add, hv] using hh
  have hdiv : ‖G z/z‖ ≤ 2*‖G z‖/t := by
    rw [norm_div]
    calc
      _ ≤ ‖G z‖/(t/2) := div_le_div_of_nonneg_left (norm_nonneg _)
        (by linarith) hz
      _ = _ := by ring
  have hπ : ‖(Real.pi : ℂ)^(-2*z)‖ ≤ Real.pi^2 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have he : (-2*z).re = -2*c := by simp [z]
    rw [he]
    have hh := Real.rpow_le_rpow_of_exponent_le
      (by linarith [Real.two_le_pi] : 1 ≤ Real.pi)
      (show -2*c ≤ (2 : ℝ) by linarith [(abs_le.mp hc).1])
    simpa using hh
  have hpol := hbound t c v ht hc hv.le α hα
  have hwt : ‖G z‖*(1+t/2)^N ≤ E := by
    have hh := hweight z (by simpa [z] using hc)
    simpa [z, hv] using hh
  change ‖G z/z * (bblrGammaQuotient t α z *
    ∏ j : Fin 4, riemannZeta (sourceZetaPoints t j+α j+z)) *
      (Real.pi : ℂ)^(-2*z)‖ * (1+t/2)^N ≤ _
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (2*‖G z‖/t)*(D*(1+t)^48)*Real.pi^2*(1+t/2)^N := by
      gcongr
    _ = (2*D*Real.pi^2*(1+t)^48/t)*(‖G z‖*(1+t/2)^N) := by ring
    _ ≤ (2*D*Real.pi^2*(1+t)^48/t)*E := by gcongr
    _ = _ := by ring

/-- Elementary conversion of the horizontal polynomial budget to an
arbitrary inverse power; the weight order `A+47` absorbs degree 48 and `1/t`. -/
theorem horizontal_weighted_budget_to_inverse_power
    (A : ℕ) (q D t : ℝ) (hq : 0 ≤ q) (hD : 0 ≤ D) (ht : 1 ≤ t)
    (h : q*(1+t/2)^(A+47) ≤ D*(1+t)^48/t) :
    q ≤ (D*2^(A+95))*t^(-(A : ℝ)) := by
  have ht0 : 0 < t := by linarith
  have hstart : q*(t/2)^(A+47) ≤ D*(2*t)^48/t := by
    calc
      _ ≤ q*(1+t/2)^(A+47) := by gcongr; linarith
      _ ≤ D*(1+t)^48/t := h
      _ ≤ D*(2*t)^48/t := by gcongr; linarith
  have hp : q*t^(A+47)/2^(A+47) ≤ D*2^48*t^47 := by
    calc
      _ = q*(t/2)^(A+47) := by rw [div_pow]; ring
      _ ≤ D*(2*t)^48/t := hstart
      _ = _ := by field_simp
  have hm := (div_le_iff₀ (by positivity : (0 : ℝ)<2^(A+47))).mp hp
  have hm' : (q*t^A)*t^47 ≤ (D*2^(A+95))*t^47 := by
    calc
      _ = q*t^(A+47) := by rw [pow_add]; ring
      _ ≤ (D*2^48*t^47)*2^(A+47) := hm
      _ = _ := by
        rw [show A+95=(A+47)+48 by omega]
        simp only [pow_add]
        ring
  have hcancel := (mul_le_mul_iff_left₀ (pow_pos ht0 47)).mp hm'
  have hfinal := (le_div_iff₀ (pow_pos ht0 A)).mpr hcancel
  simpa [Real.rpow_neg ht0.le, Real.rpow_natCast, div_eq_mul_inv] using hfinal

/-- Uniform arbitrary-order decay on both horizontal edges of the finite
AFE rectangle, obtained directly from the admissible weight condition. -/
theorem bblrExplicitAFEIntegrand_horizontal_inverse_power_bound
    (G : ℂ → ℂ) (hG : BBLREntireWeight G (fun _ => 0)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t c v : ℝ, 16 ≤ t → |c| ≤ 1 → |v| = t/2 →
      ∀ α : MomentShifts, (∀ j, ‖α j‖ ≤ 1/4) →
      ‖bblrExplicitAFEIntegrand G α t ((c : ℂ)+(v : ℂ)*I)‖ ≤ C*t^(-(A : ℝ)) := by
  obtain ⟨D,hD,hbound⟩ := bblrExplicitAFEIntegrand_horizontal_weighted_bound G hG (A+47)
  refine ⟨D*2^(A+95), by positivity, ?_⟩
  intro t c v ht hc hv α hα
  exact horizontal_weighted_budget_to_inverse_power A _ D t
    (norm_nonneg _) hD (by linarith) (hbound t c v ht hc hv α hα)

/-- A polynomial envelope for the archimedean functional-equation factor,
uniform in the central closed substrip.  The Gamma exponential factors
cancel already for this single quotient. -/
theorem zetaChi_central_strip_polynomial_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Icc (1/4 : ℝ) (3/4) →
      ‖zetaChi s‖ ≤ C*(1+|s.im|/2)^2 := by
  obtain ⟨D,hD,hΓ⟩ := gamma_positive_strip_envelopes
  refine ⟨Real.pi*D^2, by positivity, ?_⟩
  intro s hs
  let a : ℂ := (1-s)/2
  let b : ℂ := s/2
  have ha : a.re ∈ Icc (1/8 : ℝ) (7/8) := by
    dsimp [a]
    simp only [Complex.div_ofNat_re, Complex.sub_re, Complex.one_re]
    constructor <;> linarith [hs.1, hs.2]
  have hb : b.re ∈ Icc (1/8 : ℝ) (7/8) := by
    dsimp [b]
    simp only [Complex.div_ofNat_re]
    constructor <;> linarith [hs.1, hs.2]
  have hab : |a.im| = |b.im| := by simp [a,b,abs_div]
  have hbi : |b.im| = |s.im|/2 := by simp [b,abs_div]
  have hratio : ‖Gamma a/Gamma b‖ ≤ D^2*(1+|s.im|/2)^2 := by
    have hn := (hΓ a ha).1
    have hd := (hΓ b hb).2
    rw [hab] at hn
    rw [norm_div, div_eq_mul_inv]
    calc
      _ ≤ (D*(1+|b.im|)*Real.exp (-(Real.pi*|b.im|/2)))*
          (D*(1+|b.im|)*Real.exp (Real.pi*|b.im|/2)) := by gcongr
      _ = D^2*(1+|s.im|/2)^2 := by
        rw [show (D*(1+|b.im|)*Real.exp (-(Real.pi*|b.im|/2)))*
            (D*(1+|b.im|)*Real.exp (Real.pi*|b.im|/2)) =
            D^2*(1+|b.im|)^2*(Real.exp (-(Real.pi*|b.im|/2))*
              Real.exp (Real.pi*|b.im|/2)) by ring,
          ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one, hbi]
  have hπ : ‖(Real.pi : ℂ)^(-(1-2*s)/2)‖ ≤ Real.pi := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have he : (-(1-2*s)/2).re = s.re-1/2 := by simp; ring
    rw [he]
    simpa using Real.rpow_le_rpow_of_exponent_le
      (by linarith [Real.two_le_pi] : 1 ≤ Real.pi)
      (show s.re-1/2 ≤ (1 : ℝ) by linarith [hs.2])
  have he : zetaChi s = (Real.pi : ℂ)^(-(1-2*s)/2)*(Gamma a/Gamma b) := by
    have hh := gammaReal_shift_ratio s (1-2*s)
    have harg : s+(1-2*s) = 1-s := by ring
    rw [harg] at hh
    exact hh
  rw [he, norm_mul]
  calc
    _ ≤ Real.pi*(D^2*(1+|s.im|/2)^2) :=
      mul_le_mul hπ hratio (norm_nonneg _) Real.pi_pos.le
    _ = _ := by ring

/-- The actual fourfold dual multiplier has fixed polynomial growth,
uniform in all four shifts in the quarter-unit box. -/
theorem bblrDualMultiplier_polynomial_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 16 ≤ t → ∀ α : MomentShifts,
      (∀ j, ‖α j‖ ≤ 1/4) →
      ‖bblrDualMultiplier t α‖ ≤ C*(1+t)^8 := by
  obtain ⟨D,hD,hχ⟩ := zetaChi_central_strip_polynomial_bound
  refine ⟨D^4, by positivity, ?_⟩
  intro t ht α hα
  have hFactor (j : Fin 4) : ‖zetaChi (sourceZetaPoints t j+α j)‖ ≤ D*(1+t)^2 := by
    have hre : (sourceZetaPoints t j+α j).re ∈ Icc (1/4 : ℝ) (3/4) := by
      have ha := abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))
      simp only [Complex.add_re, sourceZetaPoints_re]
      constructor <;> linarith
    have him : 1+|(sourceZetaPoints t j+α j).im|/2 ≤ 1+t := by
      have ha := (Complex.abs_im_le_norm (α j)).trans (hα j)
      have hp : |(sourceZetaPoints t j).im| = t := by
        fin_cases j <;> simp [sourceZetaPoints, criticalLinePoint,
          abs_of_nonneg (by linarith : 0 ≤ t)]
      have hh := abs_add_le (sourceZetaPoints t j).im (α j).im
      rw [hp] at hh
      simp only [Complex.add_im]
      linarith
    exact (hχ _ hre).trans (by gcongr)
  unfold bblrDualMultiplier
  rw [norm_prod]
  calc
    _ ≤ ∏ j : Fin 4, D*(1+t)^2 :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hFactor j)
    _ = D^4*(1+t)^8 := by simp; ring

end
end Sechstmoment.Source
