import Sechstmoment.Numerator.U.ZeroModes.Ratio.GCDVStarDensity

/-! The literal unrestricted positive-integer common-X GCD V* expression.
Only the actual finite amplifier supports remain; both zeta factors and
all positive gaps are genuinely countable sums. Convergence and mask
completion are proved in the following modules. -/
namespace Sechstmoment
open Complex Real Source Set MeasureTheory
open scoped BigOperators Topology
noncomputable section

def a03UnrestrictedRatioGCDVStarIntegrand (dual positive : Bool) (Φ : ℝ→ℂ) (T : ℝ)
    (σ α : MomentShifts) (f g : ℝ→ℝ) (u v m n h : ℕ) (X : ℝ) : ℂ :=
  let a := u+1
  let b := v+1
  let M := m+1
  let N := n+1
  let H := h+1
  let d := Nat.gcd (a*M) (b*N)
  (f (Real.log (a:ℝ)/Real.log T):ℂ)*(g (Real.log (b:ℝ)/Real.log T):ℂ)*
    (d:ℂ)*(a:ℂ)^(-1+α 1)*(b:ℂ)^(-1+α 3)*(M:ℂ)^(-1-α 0+α 1)*
      (N:ℂ)^(-1-α 2+α 3)*(X:ℂ)^(-1-α 1-α 3)*
        (a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (rawMomentShifts T σ)) ((a:ℝ)*(M:ℝ)^2/X)*
          a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (rawMomentShifts T σ)) ((b:ℝ)*(N:ℝ)^2/X))*
            ∫ t : ℝ,Complex.exp (((-(T*rectangularGapSign positive*(d:ℝ)*H/X):ℝ):ℂ)*I*(t:ℂ))*
              a03RatioLeadingBranchProfile dual Φ T σ t*
                bblrVStar (polarPoleKiller T σ) (X^2/((a:ℝ)*b*(T*t)^2))

def a03UnrestrictedRatioGCDVStarTerm (dual positive : Bool) (Φ : ℝ→ℂ) (T : ℝ)
    (σ α : MomentShifts) (f g : ℝ→ℝ) (u v m n h : ℕ) : ℂ :=
  ∫ X : ℝ in Ioi 0,a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g u v m n h X

def a03ActualUnrestrictedRatioGCDVStar (dual : Bool) (Φ : ℝ→ℂ)
    (T a b : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  (T:ℂ)*∑ positive : Bool,∑ u∈Finset.range ⌊T^a⌋₊,∑ v∈Finset.range ⌊T^b⌋₊,
    ∑' m : ℕ,∑' n : ℕ,∑' h : ℕ,a03UnrestrictedRatioGCDVStarTerm dual positive Φ T σ α f g u v m n h

def a03ActualFourUnrestrictedRatioGCDVStar (dual : Bool) (Φ : ℝ→ℂ)
    (T a b : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∑ m : Bool,∑ n : Bool,a03ActualUnrestrictedRatioGCDVStar dual Φ T a b σ
    (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g

end
end Sechstmoment
