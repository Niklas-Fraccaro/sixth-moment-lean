import Sechstmoment.Numerator.U.ZeroModes.PolarChamberGap
import Sechstmoment.Numerator.U.ZeroModes.Ratio.PhysicalResidual

namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 0

theorem a03SourceNormalizedChamber_continuous (dual m n : Bool) :
    Continuous (Sechstmoment.a03SourceNormalizedChamber dual m n) := by
  apply continuous_pi
  intro j
  cases dual <;> cases m <;> cases n <;> fin_cases j
  all_goals
    norm_num [Sechstmoment.a03SourceNormalizedChamber,a03ZeroModeChamberShifts,
      a03ZeroModePairPermutation,bblrSixShifts]
    fun_prop

def a03SourceNormalizedChambersCompactSet (K : Set MomentShifts) : Set MomentShifts :=
  ⋃ p : Bool×(Bool×Bool),Sechstmoment.a03SourceNormalizedChamber p.1 p.2.1 p.2.2 '' K

theorem a03SourceNormalizedChambersCompactSet_isCompact (K : Set MomentShifts) (hK : IsCompact K) :
    IsCompact (a03SourceNormalizedChambersCompactSet K) := by
  exact isCompact_iUnion (fun p => hK.image (a03SourceNormalizedChamber_continuous p.1 p.2.1 p.2.2))

theorem a03SourceNormalizedChambersCompactSet_gap (K : Set MomentShifts) {κ : ℝ}
    (hρ : ∀ σ∈K,∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) :
    ∀ σ∈a03SourceNormalizedChambersCompactSet K,∀ k : PurePolarIndex,
      κ≤‖normalizedPurePolarRoot σ k‖ := by
  intro σ hσ
  obtain ⟨p,hp⟩ := mem_iUnion.mp hσ
  obtain ⟨τ,hτ,rfl⟩ := hp
  exact Sechstmoment.a03NormalizedPureRoot_gap_chambers τ (hρ τ hτ) p.1 p.2.1 p.2.2

theorem a03ZeroModeRatioPhysicalResidual_chambers_uniform_log_bound
    (K : Set MomentShifts) (hK : IsCompact K)
    {κ ε δ : ℝ} (hκ : 0<κ) (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (hρ : ∀ σ∈K,∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ dual m n : Bool,∀ σ∈K,
      ∀ g a b : ℕ,0<g → 0<a → 0<b → ∀ A B : ℕ→ℂ,∀ x : ℝ,0<x →
      ∀ s : ℂ,1+ε≤s.re →
      ‖a03ZeroModeRatioPhysicalResidual ε
        (a03ZeroModeChamberShifts m n (if dual then bblrSixShifts (rawMomentShifts T σ) 1 else rawMomentShifts T σ))
        g a b A B x s‖≤
        C*(Real.log T)^8*
          ‖a03ZeroModeRatioPhysicalPrefactor
            (a03ZeroModeChamberShifts m n (if dual then bblrSixShifts (rawMomentShifts T σ) 1 else rawMomentShifts T σ))
            g a b A B x s‖*(a:ℝ)^δ*(b:ℝ)^δ*
          ((x/(g*a:ℕ))^(a03ZeroModeRatioPrimaryLine ε)*(x/(g*b:ℕ))^(a03ZeroModeRatioPrimaryLine ε)+
           (x/(g*b:ℕ))^(a03ZeroModeRatioSecondaryLine ε)+
           (x/(g*a:ℕ))^(a03ZeroModeRatioSecondaryLine ε)) := by
  obtain ⟨C,hC,hbound⟩ := a03ZeroModeRatioPhysicalResidual_uniform_log_bound
    (a03SourceNormalizedChambersCompactSet K) (a03SourceNormalizedChambersCompactSet_isCompact K hK)
      hκ hε hε1 hδ (a03SourceNormalizedChambersCompactSet_gap K hρ)
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with T hbnd
  intro dual m n σ hσ g a b hg ha hb A B x hx s hs
  have hmem : Sechstmoment.a03SourceNormalizedChamber dual m n σ∈a03SourceNormalizedChambersCompactSet K :=
    mem_iUnion.mpr ⟨(dual,(m,n)),⟨σ,hσ,rfl⟩⟩
  have hh := hbnd _ hmem g a b hg ha hb A B x hx s hs
  rw [Sechstmoment.a03SourceNormalizedChamber_raw] at hh
  exact hh

end
end Sechstmoment.Source
