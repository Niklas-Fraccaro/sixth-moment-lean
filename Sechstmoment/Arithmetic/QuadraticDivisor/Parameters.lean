import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace DivisorProof

noncomputable section

/-- Input exponent from Corollary 1.3; the output exponent is `ε`. -/
def inputExponent (ε δ : ℝ) : ℝ :=
  min (ε / 2000) (δ / (2000 * (1 + δ)))

theorem inputExponent_pos {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    0 < inputExponent ε δ := by
  unfold inputExponent
  exact lt_min (by positivity) (by positivity)

theorem inputExponent_valid {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    0 < inputExponent ε δ ∧
    inputExponent ε δ ≤ δ / (1000 * (1 + δ)) ∧
    1000 * inputExponent ε δ ≤ ε := by
  have h₁ := min_le_left (ε / 2000) (δ / (2000 * (1 + δ)))
  have h₂ := min_le_right (ε / 2000) (δ / (2000 * (1 + δ)))
  have hd : 0 < 1000 * (1 + δ) := by positivity
  refine ⟨inputExponent_pos hε hδ, ?_, ?_⟩
  · unfold inputExponent
    apply h₂.trans
    apply (div_le_div_iff₀ (by positivity) hd).2
    nlinarith
  · unfold inputExponent
    linarith

theorem rho_lt_half {ρ δ : ℝ} (hδ : 0 < δ)
    (hρ : ρ ≤ δ / (1000 * (1 + δ))) : ρ < 1 / 2 := by
  have h := (le_div_iff₀ (by positivity : 0 < 1000 * (1 + δ))).1 hρ
  by_contra hnot
  have hp := mul_le_mul_of_nonneg_right (le_of_not_gt hnot)
    (by positivity : 0 ≤ 1000 * (1 + δ))
  nlinarith

theorem rho_reserve {ρ δ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hbound : ρ ≤ δ / (1000 * (1 + δ))) :
    250 * ρ ≤ δ / (4 * (1 + δ)) ∧ 2 * ρ < δ := by
  have hd : 0 < 1 + δ := by linarith
  have h := (le_div_iff₀ (by positivity : 0 < 1000 * (1 + δ))).1 hbound
  constructor
  · apply (le_div_iff₀ (by positivity)).2
    nlinarith
  · have hδρ := mul_pos hδ hρ
    nlinarith

/-- Strict power reserve in the first Watt size condition, equation (27). -/
theorem watt_first_size_exponent {ρ δ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hbound : ρ ≤ δ / (1000 * (1 + δ))) :
    ρ < δ / (4 * (1 + δ)) - ρ / (2 * (1 + δ)) - 5 * ρ := by
  have hres := (rho_reserve hδ hρ hbound).1
  have hfrac : ρ / (2 * (1 + δ)) ≤ ρ / 2 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)).2
    nlinarith
  linarith

/-- Literal loss accounting in §6.4; the loss `20ρ` is retained. -/
theorem watt_loss_budget :
    (35 + 60 + 6 + 1 + 2 + 10 : ℕ) = 114 ∧ (114 : ℕ) < 200 := by
  norm_num

theorem final_loss_budget : (220 + 6 : ℕ) = 226 ∧ (226 : ℕ) ≤ 1000 := by
  norm_num

/-- The explicit positive margin in §8.3. -/
def sourceGap (a b : ℝ) : ℝ := min (1 / 2 - a - b) ((2 - 3*a - 5*b) / 8)

theorem sourceGap_pos {a b : ℝ} (_ha : 0 ≤ a) (hab : a ≤ b)
    (hrange : 3*a + 5*b < 2) : 0 < sourceGap a b := by
  unfold sourceGap
  apply lt_min <;> linarith

theorem sourceGap_le_quarter {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    sourceGap a b ≤ 1 / 4 := by
  unfold sourceGap
  have h := min_le_right (1 / 2 - a - b) ((2 - 3*a - 5*b) / 8)
  linarith

/-- Both source orientations use `AB`, with `max(A,B)` handled separately. -/
theorem source_exponents_with_margin {a b s u : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hrange : 3*a + 5*b < 2)
    (_hs : 0 ≤ s) (hs' : s ≤ sourceGap a b / 64)
    (_hu : 0 ≤ u) (hu' : u ≤ sourceGap a b / 64) :
    let γ := sourceGap a b
    let ε := γ / 64
    let ℓ := γ / 64
    (1/2 + a + b + 4*ε + s/2 + ℓ < 1 - γ/2) ∧
    (3/4 + (3*a+5*b)/8 + 4*ε + u/4 + 3*s/4 + ℓ < 1 - γ/2) ∧
    ((a+b)/2 + 4*ε + u/2 + 2*s + ℓ < 1 - γ/2) := by
  dsimp only
  have hγ := sourceGap_pos ha hab hrange
  have hγq := sourceGap_le_quarter ha hab
  have hγ₀ : sourceGap a b ≤ 1/2 - a - b := min_le_left _ _
  have hγ₁ : sourceGap a b ≤ (2-3*a-5*b)/8 := min_le_right _ _
  refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem source_loss_reserve {γ s u : ℝ} (hγ : 0 < γ)
    (hs : s ≤ γ/64) (hu : u ≤ γ/64) :
    4*(γ/64) + 2*s + u/2 + γ/64 ≤ 15*γ/128 ∧ 15*γ/128 < γ/2 := by
  constructor <;> linarith

/-- The fixed mass exponent `r = 4` is valid for the actual source scales. -/
theorem source_mass_exponents_lt_four {a b s u : ℝ}
    (_ha : 0 ≤ a) (hab : a ≤ b) (hrange : 3*a + 5*b < 2)
    (hs : s ≤ 1/8) (hu : u ≤ 1/8) :
    2+a+b+u < 4 ∧ 2+2*(a+b)+2*s+2*u < 4 := by
  constructor <;> linarith

end
end DivisorProof
