import Sechstmoment.Arithmetic.Watt.Complex
import Sechstmoment.Arithmetic.Watt.MixedDerivatives

/-! Uniform data for the p-weights created by Poisson completion.
All constants below are fixed before the scales, slope and arithmetic indices. -/

namespace DivisorProof
namespace Watt41
open Real MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 2000000

structure ComplexPWeightData (b : ℕ → ℝ) (P : ℝ) (f : ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ f
  support : tsupport f ⊆ Icc (P/2) P
  derivatives : ∀ j x, 0 < x → ‖iteratedDeriv j f x‖ ≤ b j*x^(-(j : ℝ))

structure InnerWeightData (b : ℕ → ℝ) (q : Scales) (δ : ℝ)
    (α β w : ℝ → ℂ) : Prop where
  alpha_smooth : ContDiff ℝ ∞ α
  beta_smooth : ContDiff ℝ ∞ β
  omega_smooth : ContDiff ℝ ∞ w
  alpha_support : tsupport α ⊆ Icc (q.H/2) q.H
  beta_support : tsupport β ⊆ Icc (q.K/2) q.K
  omega_support : tsupport w ⊆ Icc (q.L/2) q.L
  alpha_derivatives : ∀ j x, 0 < x →
    ‖iteratedDeriv j α x‖ ≤ b j*(δ*x)^(-(j : ℝ))
  beta_derivatives : ∀ j x, 0 < x →
    ‖iteratedDeriv j β x‖ ≤ b j*(δ*x)^(-(j : ℝ))
  omega_derivatives : ∀ j x, 0 < x →
    ‖iteratedDeriv j w x‖ ≤ b j*(δ*x)^(-(j : ℝ))

structure ComplexWeightData (b fbound : ℕ → ℝ) (q : Scales) (δ : ℝ)
    (α β w : ℝ → ℂ) (f : ℕ → ℕ → ℝ → ℂ) : Prop extends InnerWeightData b q δ α β w where
  p_data : ∀ rs ∈ pairRange q, ComplexPWeightData fbound q.P (f rs.1 rs.2)

theorem ComplexPWeightData.re_smooth {b : ℕ → ℝ} {P : ℝ} {f : ℝ → ℂ}
    (h : ComplexPWeightData b P f) : ContDiff ℝ ∞ (fun x => (f x).re) :=
  Complex.reCLM.contDiff.comp h.smooth

theorem ComplexPWeightData.im_smooth {b : ℕ → ℝ} {P : ℝ} {f : ℝ → ℂ}
    (h : ComplexPWeightData b P f) : ContDiff ℝ ∞ (fun x => (f x).im) :=
  Complex.imCLM.contDiff.comp h.smooth

theorem ComplexPWeightData.re_support {b : ℕ → ℝ} {P : ℝ} {f : ℝ → ℂ}
    (h : ComplexPWeightData b P f) : tsupport (fun x => (f x).re) ⊆ Icc (P/2) P := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  apply h.support
  apply subset_tsupport
  intro hz
  exact hx (by simp [hz])

theorem ComplexPWeightData.im_support {b : ℕ → ℝ} {P : ℝ} {f : ℝ → ℂ}
    (h : ComplexPWeightData b P f) : tsupport (fun x => (f x).im) ⊆ Icc (P/2) P := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  apply h.support
  apply subset_tsupport
  intro hz
  exact hx (by simp [hz])

theorem ComplexPWeightData.re_derivatives {b : ℕ → ℝ} {P : ℝ} {f : ℝ → ℂ}
    (h : ComplexPWeightData b P f) (j : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖iteratedDeriv j (fun x => (f x).re) x‖ ≤ b j*x^(-(j : ℝ)) := by
  rw [iteratedDeriv_re h.smooth]
  exact (Complex.abs_re_le_norm _).trans (h.derivatives j x hx)

theorem ComplexPWeightData.im_derivatives {b : ℕ → ℝ} {P : ℝ} {f : ℝ → ℂ}
    (h : ComplexPWeightData b P f) (j : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖iteratedDeriv j (fun x => (f x).im) x‖ ≤ b j*x^(-(j : ℝ)) := by
  rw [iteratedDeriv_im h.smooth]
  exact (Complex.abs_im_le_norm _).trans (h.derivatives j x hx)

theorem ComplexWeightData.re_data {b fbound : ℕ → ℝ} {q : Scales} {δ : ℝ}
    {α β w : ℝ → ℂ} {f : ℕ → ℕ → ℝ → ℂ}
    (h : ComplexWeightData b fbound q δ α β w f) :
    WeightData b fbound q δ α β w (fun r s x => (f r s x).re) := by
  refine ⟨h.alpha_smooth,h.beta_smooth,h.omega_smooth,h.alpha_support,h.beta_support,
    h.omega_support,h.alpha_derivatives,h.beta_derivatives,h.omega_derivatives,?_,?_,?_⟩
  · intro rs hrs
    exact (h.p_data rs hrs).re_smooth
  · intro rs hrs
    exact (h.p_data rs hrs).re_support
  · intro rs hrs j x hx
    exact (h.p_data rs hrs).re_derivatives j hx

theorem ComplexWeightData.im_data {b fbound : ℕ → ℝ} {q : Scales} {δ : ℝ}
    {α β w : ℝ → ℂ} {f : ℕ → ℕ → ℝ → ℂ}
    (h : ComplexWeightData b fbound q δ α β w f) :
    WeightData b fbound q δ α β w (fun r s x => (f r s x).im) := by
  refine ⟨h.alpha_smooth,h.beta_smooth,h.omega_smooth,h.alpha_support,h.beta_support,
    h.omega_support,h.alpha_derivatives,h.beta_derivatives,h.omega_derivatives,?_,?_,?_⟩
  · intro rs hrs
    exact (h.p_data rs hrs).im_smooth
  · intro rs hrs
    exact (h.p_data rs hrs).im_support
  · intro rs hrs j x hx
    exact (h.p_data rs hrs).im_derivatives j hx

def curveWeight (γ : ℕ → ℕ → ℝ → ℝ → ℂ) (y : ℝ) (r s : ℕ) (t : ℝ) : ℂ :=
  γ r s ((s : ℝ)*y*t) t

theorem gamma_curve_smooth {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (y : ℝ) (r s : ℕ) : ContDiff ℝ ∞ (curveWeight γ y r s) :=
  (hw.gamma_smooth r s).comp ((contDiff_const.mul contDiff_id).prodMk contDiff_id)

theorem gamma_curve_support {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (y : ℝ) (r s : ℕ) : tsupport (curveWeight γ y r s) ⊆ Icc (p.P/2) p.P := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  have hn : (fun z : ℝ × ℝ => γ r s z.1 z.2) ((s : ℝ)*y*t,t) ≠ 0 := ht
  exact (hw.gamma_support r s (subset_tsupport _ hn)).2

/-- No new p-weight derivative assumption is introduced: it follows from hw. -/
theorem gamma_curve_weight_data {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    {y : ℝ} (hy : 0 < y) (r : ℕ) {s : ℕ} (hs : 0 < s) :
    ComplexPWeightData (fun j => rayDerivativeBound g j 0 0) p.P (curveWeight γ y r s) := by
  refine ⟨gamma_curve_smooth hw y r s,gamma_curve_support hw y r s,?_⟩
  intro j t ht
  exact gamma_ray_derivative_bound hw r s (mul_pos (by exact_mod_cast hs) hy) j ht

/-- Uniform quantifier order: the derivative sequence precedes every scale
and weight, and in particular precedes the integration variable y. -/
theorem gamma_curve_uniform_data (g : ℕ → ℕ → ℝ) (hg : ∀ i j, 0 ≤ g i j) :
    ∃ fbound : ℕ → ℝ, (∀ j, 0 ≤ fbound j) ∧
      ∀ (b : ℕ → ℝ) (p : WattScales) (Δ : ℝ) (a bc : ℕ → ℂ)
        (u₀ u₁ : ℝ → ℂ) (γ : ℕ → ℕ → ℝ → ℝ → ℂ),
        WattWeightData b g p Δ a bc u₀ u₁ γ →
        ∀ y : ℝ, 0 < y → ∀ r s : ℕ, 0 < s →
          ComplexPWeightData fbound p.P (curveWeight γ y r s) := by
  exact ⟨fun j => rayDerivativeBound g j 0 0,
    fun j => rayDerivativeBound_nonneg hg j 0 0,
    fun _ _ _ _ _ _ _ _ hw _ hy r _ hs => gamma_curve_weight_data hw hy r hs⟩

/-- A complete complex-weight input for Watt, derived from the original
gamma data and the three dyadic inner weights. -/
theorem gamma_curve_complexWeightData {b b' : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    {q : Scales} {δ : ℝ} {α β w : ℝ → ℂ}
    (hi : InnerWeightData b' q δ α β w) (hP : q.P = p.P) {y : ℝ} (hy : 0 < y) :
    ComplexWeightData b' (fun j => rayDerivativeBound g j 0 0) q δ α β w (curveWeight γ y) := by
  refine ⟨hi,?_⟩
  intro rs hrs
  have hs : 0 < rs.2 :=
    (Finset.mem_Icc.mp (mem_filter.mp (mem_product.mp (mem_filter.mp hrs).1).2).1).1
  rw [hP]
  exact gamma_curve_weight_data hw hy rs.1 hs

/-- The y-support is common to all active arithmetic indices and p-values. -/
theorem gamma_curve_y_support {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hV : 0 < p.V) (hP : 0 < p.P) (hS : 0 < p.S) (r : ℕ) {s : ℕ}
    (hs : s ∈ dyadicRange p.S) (t : ℝ) :
    tsupport (fun y => curveWeight γ y r s t) ⊆
      Icc (p.V/(2*p.S*p.P)) (4*p.V/(p.S*p.P)) := by
  apply closure_minimal _ isClosed_Icc
  intro y hy
  have hn : (fun z : ℝ × ℝ => γ r s z.1 z.2) ((s : ℝ)*y*t,t) ≠ 0 := hy
  have hγ := hw.gamma_support r s (subset_tsupport _ hn)
  have hsb := mem_dyadicRange.mp hs
  have hsp : (0 : ℝ) < s := by exact_mod_cast hsb.1
  have htp : 0 < t := by linarith [hγ.2.1]
  have hmul : (s : ℝ)*t*y = (s : ℝ)*y*t := by ring
  have hvl : p.V/2 ≤ (s : ℝ)*t*y := by simpa only [curveWeight,← hmul] using hγ.1.1
  have hvu : (s : ℝ)*t*y ≤ p.V := by simpa only [curveWeight,← hmul] using hγ.1.2
  have hyp : 0 < y := by nlinarith [mul_pos hsp htp]
  have hcUpper : (s : ℝ)*t ≤ p.S*p.P :=
    mul_le_mul hsb.2.2 hγ.2.2 htp.le hS.le
  have hcLower : p.S*p.P/4 ≤ (s : ℝ)*t := by
    have hb := mul_le_mul hsb.2.1 hγ.2.1 (by positivity : 0 ≤ p.P/2) (by positivity : 0 ≤ (s : ℝ))
    nlinarith
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < 2*p.S*p.P)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hcUpper hyp.le]
  · apply (le_div_iff₀ (mul_pos hS hP)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hcLower hyp.le]

end
end Watt41

noncomputable section

/-- Watt 4.1 applies to the composed p-weights with constants fixed before y.
No regularity or derivative condition on the composed weight is assumed. -/
theorem Watt41.complexWeightedCurve (hWatt : Watt41) {ε : ℝ} (hε : 0 < ε)
    (b : ℕ → ℝ) (g : ℕ → ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (hg : ∀ i j, 0 ≤ g i j) :
    ∃ C X₀ : ℝ, 0 ≤ C ∧ 1 ≤ X₀ ∧
      ∀ (q : Watt41.Scales) (δ : ℝ) (σ : ℤ) (a bc : ℕ → ℂ) (α β w : ℝ → ℂ)
        (b₀ : ℕ → ℝ) (p : WattScales) (Δ : ℝ) (a₀ bc₀ : ℕ → ℂ)
        (u₀ u₁ : ℝ → ℂ) (γ : ℕ → ℕ → ℝ → ℝ → ℂ),
        (∀ i, 1 ≤ q.size i) → 0 < δ → (σ = -1 ∨ σ = 1) →
        WattWeightData b₀ g p Δ a₀ bc₀ u₀ u₁ γ →
        Watt41.InnerWeightData b q δ α β w → q.P = p.P →
        (∀ r, ‖a r‖ ≤ 1) → (∀ s, ‖bc s‖ ≤ 1) →
        max (q.H^2*q.K) q.L ≤ q.Q^2 → X₀ ≤ q.X →
        ∀ y : ℝ, 0 < y →
          ‖Watt41.complexWeightedSum q σ a bc α β w (Watt41.curveWeight γ y)‖ ≤
            C*Watt41.majorant q δ ε := by
  obtain ⟨C,X₀,hC,hX₀,hbound⟩ := hWatt.complexWeighted hε b
    (fun j => Watt41.rayDerivativeBound g j 0 0) hb (fun j => Watt41.rayDerivativeBound_nonneg hg j 0 0)
  refine ⟨C,X₀,hC,hX₀,?_⟩
  intro q δ σ a bc α β w b₀ p Δ a₀ bc₀ u₀ u₁ γ hsize hδ hσ hw hi hP ha hbc hnum hlarge y hy
  have hdata := Watt41.gamma_curve_complexWeightData hw hi hP hy
  exact hbound q δ σ a bc α β w (Watt41.curveWeight γ y)
    hsize hδ hσ hdata.re_data hdata.im_data ha hbc hnum hlarge

end
end DivisorProof
