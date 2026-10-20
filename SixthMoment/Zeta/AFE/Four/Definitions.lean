import SixthMoment.Zeta.AFE.Four.Terms


namespace SixthMoment.Source
open Complex MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
open Classical

noncomputable section

def sourceZetaPoints (t : ℝ) : MomentShifts :=
  ![criticalLinePoint t, criticalLinePoint t,
    1-criticalLinePoint t, 1-criticalLinePoint t]

def bblrGammaQuotient (t : ℝ) (α : MomentShifts) (z : ℂ) : ℂ :=
  ∏ j : Fin 4, Gamma ((sourceZetaPoints t j+α j+z)/2) /
    Gamma ((sourceZetaPoints t j+α j)/2)

def bblrDualMultiplier (t : ℝ) (α : MomentShifts) : ℂ :=
  ∏ j : Fin 4, zetaChi (sourceZetaPoints t j+α j)

def bblrV (G : ℂ → ℂ) (α : MomentShifts) (x t : ℝ) : ℂ :=
  verticalIntegral 1 fun z => G z/z*bblrGammaQuotient t α z*
    (Real.pi : ℂ)^(-2*z)*(x : ℂ)^(-z)

def bblrAFESummand (G : ℂ → ℂ) (α : MomentShifts)
    (t : ℝ) (n : Fin 4 → ℕ) : ℂ :=
  ((((n 0+1)*(n 1+1) : ℕ) : ℂ) /
    (((n 2+1)*(n 3+1) : ℕ) : ℂ))^(-(t : ℂ)*I)*
    bblrV G α (positiveQuadProduct n) t /
    ∏ j : Fin 4, (n j+1 : ℂ)^(1/2+α j)

def bblrAFESum (G : ℂ → ℂ) (α : MomentShifts) (t : ℝ) : ℂ :=
  ∑' n : Fin 4 → ℕ, bblrAFESummand G α t n

def bblrAFEDiscrepancy (G : ℂ → ℂ) (α : MomentShifts) (t : ℝ) : ℂ :=
  shiftedFourthProduct t α-
    (bblrAFESum G α t+
      bblrDualMultiplier t α*bblrAFESum G (bblrSixShifts α 1) t)

end
end SixthMoment.Source
