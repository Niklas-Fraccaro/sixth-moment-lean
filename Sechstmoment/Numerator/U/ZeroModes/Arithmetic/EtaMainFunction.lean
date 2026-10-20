import Sechstmoment.Numerator.U.ZeroModes.Arithmetic.EtaArithmetic
import Sechstmoment.Numerator.U.ZeroModes.Contour.Chambers


namespace Sechstmoment.Source
open Complex
open scoped BigOperators
open Classical

set_option maxHeartbeats 0

noncomputable def a03EtaMainArithmetic (N₁ N₂ : ℕ) (a b : ℕ → ℂ)
    (α β γ δ s : ℂ) : ℂ :=
  ∑ g ∈ Finset.Icc 1 (min N₁ N₂), ∑ m ∈ Finset.Icc 1 (N₁/g),
    ∑ n ∈ Finset.Icc 1 (N₂/g), if m.Coprime n then
      a (g*m)*b (g*n)/((g*m*n:ℕ):ℂ)*
        bblrNormalizedEtaArithmetic α β γ δ s m*
        bblrNormalizedEtaArithmetic γ δ α β s n else 0

noncomputable def a03EtaMainFunction (N₁ N₂ : ℕ) (a b : ℕ → ℂ)
    (α : MomentShifts) (s : ℂ) : ℂ :=
  riemannZeta (1+α 0+α 2+2*s)*riemannZeta (1-α 1-α 3-2*s)*
    a03EtaMainArithmetic N₁ N₂ a b (α 0) (α 1) (α 2) (α 3) s

theorem a03EtaMainArithmetic_reflection (N₁ N₂ : ℕ) (a b : ℕ → ℂ)
    (α β γ δ s : ℂ)
    (hden : ∀ p : ℕ, p.Prime → 1-(p:ℂ)^(-(2+(α-β+γ-δ))) ≠ 0) :
    a03EtaMainArithmetic N₁ N₂ a b α β γ δ s =
      a03EtaMainArithmetic N₁ N₂ a b (-δ) (-γ) (-β) (-α) (-s) := by
  have hden' : ∀ p : ℕ, p.Prime → 1-(p:ℂ)^(-(2+(γ-δ+α-β))) ≠ 0 := by
    intro p hp
    have he : γ-δ+α-β=α-β+γ-δ := by ring
    rw [he]
    exact hden p hp
  unfold a03EtaMainArithmetic
  simp_rw [bblrNormalizedEtaArithmetic_reflection α β γ δ s hden,
    bblrNormalizedEtaArithmetic_reflection γ δ α β s hden']

theorem a03EtaMainFunction_reflection (N₁ N₂ : ℕ) (a b : ℕ → ℂ)
    (α : MomentShifts) (s : ℂ)
    (hden : ∀ p : ℕ, p.Prime →
      1-(p:ℂ)^(-(2+(α 0-α 1+α 2-α 3))) ≠ 0) :
    a03EtaMainFunction N₁ N₂ a b α s =
      a03EtaMainFunction N₁ N₂ a b (a03ZeroModeReverseNegative α) (-s) := by
  unfold a03EtaMainFunction
  rw [a03EtaMainArithmetic_reflection N₁ N₂ a b (α 0) (α 1) (α 2) (α 3) s hden]
  change riemannZeta (1+α 0+α 2+2*s)*riemannZeta (1-α 1-α 3-2*s)*
      a03EtaMainArithmetic N₁ N₂ a b (-α 3) (-α 2) (-α 1) (-α 0) (-s) =
    riemannZeta (1 + -α 3 + -α 1 + 2*(-s))*
      riemannZeta (1 - -α 2 - -α 0 - 2*(-s))*
      a03EtaMainArithmetic N₁ N₂ a b (-α 3) (-α 2) (-α 1) (-α 0) (-s)
  have h₁ : 1 + -α 3 + -α 1 + 2*(-s)=1-α 1-α 3-2*s := by ring
  have h₂ : 1 - -α 2 - -α 0 - 2*(-s)=1+α 0+α 2+2*s := by ring
  rw [h₁,h₂]
  ring

theorem a03EtaMain_denominator_ne_zero {α : MomentShifts}
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ 1/8) (p : ℕ) (hp : p.Prime) :
    1-(p:ℂ)^(-(2+(α 0-α 1+α 2-α 3))) ≠ 0 := by
  apply Complex.one_sub_prime_cpow_ne_zero hp
  have hre (j : Fin 4) : |(α j).re| ≤ 1/8 :=
    (Complex.abs_re_le_norm _).trans (hα j)
  simp only [Complex.add_re, Complex.sub_re]
  norm_num
  linarith [(abs_le.mp (hre 0)).1, (abs_le.mp (hre 1)).2,
    (abs_le.mp (hre 2)).1, (abs_le.mp (hre 3)).2]

theorem a03EtaMainFunction_reflection_of_small_shifts (N₁ N₂ : ℕ) (a b : ℕ → ℂ)
    {α : MomentShifts} (hα : ∀ j : Fin 4, ‖α j‖ ≤ 1/8) (s : ℂ) :
    a03EtaMainFunction N₁ N₂ a b α s =
      a03EtaMainFunction N₁ N₂ a b (a03ZeroModeReverseNegative α) (-s) :=
  a03EtaMainFunction_reflection N₁ N₂ a b α s
    (fun p hp => a03EtaMain_denominator_ne_zero hα p hp)

end Sechstmoment.Source
