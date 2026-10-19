import Sechstmoment.Numerator.U.ZeroModes.Arithmetic.EtaBIdentity
import Sechstmoment.Numerator.U.ZeroModes.Arithmetic.EtaMainFunction

/-! Exact arithmetic identification of the crossed `s=0` residue in §2.4.
This does not assert the analytic contour shift or the `V*` tail estimate. -/

namespace Sechstmoment
open scoped BigOperators

noncomputable def bblrAArithmetic (α β γ δ : ℂ) : ℂ :=
  riemannZeta (1+α+γ)*riemannZeta (1+α+δ)*
    riemannZeta (1+β+γ)*riemannZeta (1+β+δ)/
      riemannZeta (2+α+β+γ+δ)

noncomputable def bblrZArithmetic (α β γ δ : ℂ) (a b : ℕ) : ℂ :=
  bblrAArithmetic α β γ δ*bblrBFactor α β γ δ a*bblrBFactor γ δ α β b

namespace Source
open Classical

set_option maxHeartbeats 0

noncomputable def a03CrossedArithmeticSum (N₁ N₂ : ℕ) (a b : ℕ → ℂ)
    (α : MomentShifts) : ℂ :=
  ∑ g ∈ Finset.Icc 1 (min N₁ N₂), ∑ m ∈ Finset.Icc 1 (N₁/g),
    ∑ n ∈ Finset.Icc 1 (N₂/g), if m.Coprime n then
      a (g*m)*b (g*n)/((g*m*n:ℕ):ℂ)*
        bblrZArithmetic (α 0) (-α 3) (α 2) (-α 1) m n else 0

theorem bblrCrossedAArithmetic_eq (α β γ δ : ℂ) :
    riemannZeta (1+α-β)*riemannZeta (1+γ-δ)/
        riemannZeta (2+α-β+γ-δ)*
      (riemannZeta (1+α+γ)*riemannZeta (1-β-δ)) =
    bblrAArithmetic α (-δ) γ (-β) := by
  unfold bblrAArithmetic
  have h₁ : 1+α+-β=1+α-β := by ring
  have h₂ : 1+-δ+γ=1+γ-δ := by ring
  have h₃ : 1+-δ+-β=1-β-δ := by ring
  have h₄ : 2+α+-δ+γ+-β=2+α-β+γ-δ := by ring
  rw [h₁,h₂,h₃,h₄]
  ring

/-- The complete finite amplifier residue identification, proved using (9)
with all original coefficient ranges retained. -/
theorem a03EtaMainFunction_zero_eq_crossedArithmetic (N₁ N₂ : ℕ) (a b : ℕ → ℂ)
    {α : MomentShifts} (hα : ∀ j : Fin 4, ‖α j‖ ≤ 1/8) :
    riemannZeta (1+α 0-α 1)*riemannZeta (1+α 2-α 3)/
      riemannZeta (2+α 0-α 1+α 2-α 3)*a03EtaMainFunction N₁ N₂ a b α 0 =
        a03CrossedArithmeticSum N₁ N₂ a b α := by
  unfold a03EtaMainFunction
  simp only [mul_zero, add_zero, sub_zero]
  rw [← mul_assoc, bblrCrossedAArithmetic_eq]
  unfold a03EtaMainArithmetic a03CrossedArithmeticSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hm0 : m ≠ 0 := by have := (Finset.mem_Icc.mp hm).1; omega
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  split_ifs with hcop
  · rw [bblrNormalizedEtaArithmetic_eq_B (α 0) (α 1) (α 2) (α 3)
      (hα 0) (hα 1) (hα 2) (hα 3) hm0,
      bblrNormalizedEtaArithmetic_eq_B (α 2) (α 3) (α 0) (α 1)
      (hα 2) (hα 3) (hα 0) (hα 1) hn0]
    unfold bblrZArithmetic
    ring
  · simp

end Source
end Sechstmoment
