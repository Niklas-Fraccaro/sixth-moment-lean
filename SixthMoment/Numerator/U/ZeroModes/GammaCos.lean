import Mathlib.NumberTheory.LSeries.RiemannZeta
import SixthMoment.Numerator.U.ZeroModes.Arithmetic.EtaMainFunction
import SixthMoment.Numerator.U.ZeroModes.VStarMellin

namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 0

def a03ZeroModeGammaCosFactor (s : ℂ) : ℂ :=
  2*(2*Real.pi:ℂ)^(-s)*Complex.Gamma s*Complex.cos ((Real.pi:ℂ)*s/2)*riemannZeta s

theorem a03ZeroModeGammaCosFactor_eq_zeta {s : ℂ} (hs : 0<s.re) (hs1 : s≠1) :
    a03ZeroModeGammaCosFactor s=riemannZeta (1-s) := by
  apply (riemannZeta_one_sub (fun n => ?_) hs1).symm
  intro he
  have hn : 0≤(n:ℝ) := Nat.cast_nonneg n
  have hr := congrArg Complex.re he
  simp only [Complex.neg_re,Complex.natCast_re] at hr
  linarith

def a03ZeroModeAfterXMellin (N₁ N₂ : ℕ) (a b : ℕ→ℂ)
    (α : MomentShifts) (G : ℂ→ℂ) (s : ℂ) : ℂ :=
  a03ZeroModeGammaCosFactor s*riemannZeta (1+α 0-α 1+α 2-α 3+s)*
    (G ((s-α 1-α 3)/2)/(s-α 1-α 3))*
      a03EtaMainArithmetic N₁ N₂ a b (α 0) (α 1) (α 2) (α 3) ((s-α 1-α 3)/2)

theorem a03ZeroModeAfterXMellin_affine_eq_M (N₁ N₂ : ℕ) (a b : ℕ→ℂ)
    (α : MomentShifts) (G : ℂ→ℂ) (z : ℂ)
    (hs : 0<(α 1+α 3+2*z).re) (hs1 : α 1+α 3+2*z≠1) :
    2*a03ZeroModeAfterXMellin N₁ N₂ a b α G (α 1+α 3+2*z)=
      G z/z*a03EtaMainFunction N₁ N₂ a b α z := by
  unfold a03ZeroModeAfterXMellin a03EtaMainFunction
  rw [a03ZeroModeGammaCosFactor_eq_zeta hs hs1]
  have harg : (α 1+α 3+2*z-α 1-α 3)/2=z := by ring
  have hden : α 1+α 3+2*z-α 1-α 3=2*z := by ring
  have hζ₁ : 1-(α 1+α 3+2*z)=1-α 1-α 3-2*z := by ring
  have hζ₂ : 1+α 0-α 1+α 2-α 3+(α 1+α 3+2*z)=1+α 0+α 2+2*z := by ring
  rw [harg,hden,hζ₁,hζ₂]
  ring

end
end SixthMoment.Source
