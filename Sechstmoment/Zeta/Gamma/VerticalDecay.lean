import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Sechstmoment.Zeta.AFE.Four.LargeGammaStrip

/-!
# Absolute vertical Gamma decay for the one-sided Mellin contour

The existing Euler-product Gamma comparison and the reflection formula give
exponential decay on a positive strip. Two actual Gamma recurrences extend
that estimate across the D04 strip. Nonzero imaginary part excludes all poles.
-/

namespace Sechstmoment
open Complex Real MeasureTheory Filter Set
open scoped Topology
noncomputable section

private theorem d04Gamma_point_ne_zero {z : ℂ} (hz : 1 ≤ |z.im|) : z ≠ 0 := by
  intro he
  norm_num [he] at hz

private theorem d04Gamma_add_one_ne_zero {z : ℂ} (hz : 1 ≤ |z.im|) : z+1 ≠ 0 := by
  apply d04Gamma_point_ne_zero
  simpa using hz

/-- A fixed polynomial envelope, uniform across the entire one-sided strip.
The bound includes both horizontal sides of every Mellin rectangle. -/
theorem d04Gamma_vertical_strip_norm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → 1 ≤ |z.im| →
      ‖Complex.Gamma z‖ ≤
        C*(1+|z.im|)^5*Real.exp (-(Real.pi*|z.im|/2)) := by
  obtain ⟨C,hC,hΓ⟩ := Source.gamma_large_positive_strip_envelope 4
  refine ⟨C,hC,?_⟩
  intro z hz0 hz2 hzi
  have hzrec : Complex.Gamma (z+2) = (z+1)*z*Complex.Gamma z := by
    rw [show z+2=(z+1)+1 by ring,
      Complex.Gamma_add_one _ (d04Gamma_add_one_ne_zero hzi),
      Complex.Gamma_add_one _ (d04Gamma_point_ne_zero hzi)]
    ring
  have hn0 : 1 ≤ ‖z‖ := hzi.trans (Complex.abs_im_le_norm z)
  have hn1 : 1 ≤ ‖z+1‖ := by
    exact hzi.trans (by simpa using Complex.abs_im_le_norm (z+1))
  have hn : ‖Complex.Gamma z‖ ≤ ‖Complex.Gamma (z+2)‖ := by
    rw [hzrec,norm_mul,norm_mul]
    calc
      _ ≤ ‖z‖*‖Complex.Gamma z‖ :=
        le_mul_of_one_le_left (norm_nonneg _) hn0
      _ ≤ ‖z+1‖*(‖z‖*‖Complex.Gamma z‖) :=
        le_mul_of_one_le_left (by positivity) hn1
      _ = _ := by ring
  apply hn.trans
  have hs : (z+2).re ∈ Icc (1/8 : ℝ) ((4 : ℕ)+7/8) := by
    have hre : (z+2).re = z.re+2 := by simp
    rw [hre]
    constructor <;> norm_num <;> linarith
  simpa using hΓ (z+2) hs

/-- The strip estimate in explicit real coordinates, retaining the full
exponential factor. -/
theorem d04Gamma_vertical_strip_coordinates :
    ∃ C : ℝ, 0 < C ∧ ∀ c v : ℝ, -1 ≤ c → c ≤ 2 → 1 ≤ |v| →
      ‖Complex.Gamma ((c : ℂ)+(v : ℂ)*I)‖ ≤
        C*(1+|v|)^5*Real.exp (-(Real.pi*|v|/2)) := by
  obtain ⟨C,hC,hΓ⟩ := d04Gamma_vertical_strip_norm_le
  refine ⟨C,hC,?_⟩
  intro c v hc0 hc2 hv
  simpa using hΓ ((c : ℂ)+(v : ℂ)*I) (by simpa using hc0)
    (by simpa using hc2) (by simpa using hv)

/-- Multiplication by an arbitrary fixed polynomial preserves uniform
horizontal decay of Gamma across the whole Mellin strip. -/
theorem d04Gamma_horizontal_polynomial_decay (k : ℕ) :
    ∀ η : ℝ, 0 < η → ∃ V : ℝ, 0 < V ∧ ∀ c v : ℝ,
      -1 ≤ c → c ≤ 2 → V ≤ |v| →
      (1+|v|)^k*‖Complex.Gamma ((c : ℂ)+(v : ℂ)*I)‖ < η := by
  obtain ⟨C,hC,hΓ⟩ := d04Gamma_vertical_strip_coordinates
  let b : ℝ := Real.pi/2
  have hb : 0 < b := by dsimp [b]; positivity
  have hmajor : Tendsto
      (fun v : ℝ => C*(1+v)^(k+5)*Real.exp (-(Real.pi*v/2))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      ((k+5 : ℕ) : ℝ) b hb).comp
        (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
    have h' := h.const_mul (C*Real.exp b)
    simp only [mul_zero, Real.rpow_natCast] at h'
    apply h'.congr'
    filter_upwards with v
    change (C*Real.exp b)*((1+v)^(k+5)*Real.exp (-b*(1+v))) = _
    rw [show (C*Real.exp b)*((1+v)^(k+5)*Real.exp (-b*(1+v))) =
      C*(1+v)^(k+5)*(Real.exp b*Real.exp (-b*(1+v))) by ring,
      ← Real.exp_add]
    congr 2
    dsimp [b]
    ring
  intro η hη
  obtain ⟨V,hV⟩ := eventually_atTop.mp (hmajor.eventually (gt_mem_nhds hη))
  refine ⟨max 1 V,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro c v hc0 hc2 hv
  have hv1 : 1 ≤ |v| := (le_max_left _ _).trans hv
  have hvV : V ≤ |v| := (le_max_right _ _).trans hv
  calc
    _ ≤ (1+|v|)^k*(C*(1+|v|)^5*Real.exp (-(Real.pi*|v|/2))) :=
      mul_le_mul_of_nonneg_left (hΓ c v hc0 hc2 hv1) (by positivity)
    _ = C*(1+|v|)^(k+5)*Real.exp (-(Real.pi*|v|/2)) := by rw [pow_add]; ring
    _ < η := hV |v| hvV

end
end Sechstmoment
