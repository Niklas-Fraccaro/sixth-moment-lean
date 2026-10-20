import Sechstmoment.Numerator.U.Sources.OffdiagonalMoment

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section

def a03ActualFiniteDiagonalMellinGrid (dual : Bool) (c T a b u v : ℝ)
    (f g Φ : ℝ→ℝ) (σ α : MomentShifts) : ℂ :=
  ∑ p∈Finset.range ⌊T^a⌋₊,∑ q∈Finset.range ⌊T^b⌋₊,
    ∑ k∈rectangularAFEProductScaleGrid (T^(2+u)),∑ n∈rectangularAFESmoothBox k,
      if diagonalQuadRelation (p+1) (q+1) n then
        (rectangularAFESmoothWeight k n:ℂ)*(∫ t : ℝ,
          rectangularMomentPairWeight T f g Φ p q t*
          (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
          rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)) else 0

def a03ActualFiniteDiagonalGammaMoment (dual : Bool) (c T a b u θ : ℝ)
    (σ : MomentShifts) (f g Φ : ℝ→ℝ) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫ v in Icc (-θ*Real.log T) (θ*Real.log T),
    a03ActualFiniteDiagonalMellinGrid dual c T a b u v f g Φ σ
      (a03SourceShifts dual T σ)

end
end Sechstmoment
