import Sechstmoment.Numerator.U.Separation.ShapeNormalization

namespace Sechstmoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 1000000

def phaseSortedScales (q : QuadraticScales) : QuadraticScales :=
  phasePairSwapScales (decide (q.M₂ < q.M₁)) (decide (q.N₂ < q.N₁)) q

def phaseNormalizedScales (q : QuadraticScales) : QuadraticScales :=
  let s := phaseSortedScales q
  if s.B*s.N₁ ≤ s.A*s.M₁ then s else phaseSideSwapScales s

theorem phase_sorted_scale_bounds (q : QuadraticScales) (hq : ∀ j, 1 ≤ q.size j) :
    (∀ j, 1 ≤ (phaseSortedScales q).size j) ∧
      (phaseSortedScales q).M₁ ≤ (phaseSortedScales q).M₂ ∧
      (phaseSortedScales q).N₁ ≤ (phaseSortedScales q).N₂ := by
  have ha := hq 0; have hb := hq 1; have hm₁ := hq 2; have hm₂ := hq 3
  have hn₁ := hq 4; have hn₂ := hq 5; have hh := hq 6
  norm_num [QuadraticScales.size] at ha hb hm₁ hm₂ hn₁ hn₂ hh
  by_cases hm : q.M₂ < q.M₁ <;> by_cases hn : q.N₂ < q.N₁ <;>
    simp only [phaseSortedScales,hm,hn,decide_true,decide_false,phasePairSwapScales,
      Bool.false_eq_true,ite_true,ite_false]
  all_goals
    refine ⟨?_,by linarith,by linarith⟩
    intro j
    fin_cases j <;> simp [QuadraticScales.size] <;> linarith

theorem phase_normalized_scale_bounds (q : QuadraticScales) (hq : ∀ j, 1 ≤ q.size j) :
    (∀ j, 1 ≤ (phaseNormalizedScales q).size j) ∧
      (phaseNormalizedScales q).M₁ ≤ (phaseNormalizedScales q).M₂ ∧
      (phaseNormalizedScales q).N₁ ≤ (phaseNormalizedScales q).N₂ ∧
      (phaseNormalizedScales q).B*(phaseNormalizedScales q).N₁ ≤
        (phaseNormalizedScales q).A*(phaseNormalizedScales q).M₁ := by
  have hs := phase_sorted_scale_bounds q hq
  unfold phaseNormalizedScales
  dsimp only
  split_ifs with h
  · exact ⟨hs.1,hs.2.1,hs.2.2,h⟩
  · refine ⟨?_,hs.2.2,hs.2.1,le_of_lt (lt_of_not_ge h)⟩
    intro j
    fin_cases j
    all_goals first
      | simpa [phaseSideSwapScales,QuadraticScales.size] using hs.1 0
      | simpa [phaseSideSwapScales,QuadraticScales.size] using hs.1 1
      | simpa [phaseSideSwapScales,QuadraticScales.size] using hs.1 2
      | simpa [phaseSideSwapScales,QuadraticScales.size] using hs.1 3
      | simpa [phaseSideSwapScales,QuadraticScales.size] using hs.1 4
      | simpa [phaseSideSwapScales,QuadraticScales.size] using hs.1 5
      | simpa [phaseSideSwapScales,QuadraticScales.size] using hs.1 6

theorem phase_sorted_products (q : QuadraticScales) :
    (phaseSortedScales q).M=q.M ∧ (phaseSortedScales q).N=q.N ∧
      (phaseSortedScales q).mass=q.mass :=
  phase_pair_swap_products _ _ q

theorem phase_normalized_invariants (q : QuadraticScales) :
    (phaseNormalizedScales q).A*(phaseNormalizedScales q).B=q.A*q.B ∧
      (phaseNormalizedScales q).M*(phaseNormalizedScales q).N=q.M*q.N ∧
      (phaseNormalizedScales q).H=q.H ∧ (phaseNormalizedScales q).mass=q.mass := by
  have hs := phase_sorted_products q
  unfold phaseNormalizedScales
  dsimp only
  split_ifs
  · simpa [phaseSortedScales,phasePairSwapScales] using
      (show q.A*q.B=q.A*q.B ∧ (phaseSortedScales q).M*(phaseSortedScales q).N=q.M*q.N ∧
        q.H=q.H ∧ (phaseSortedScales q).mass=q.mass from by
        rw [hs.1,hs.2.1,hs.2.2]; exact ⟨rfl,rfl,rfl,rfl⟩)
  · simp only [phaseSideSwapScales,QuadraticScales.M,QuadraticScales.N]
    change (phaseSortedScales q).B*(phaseSortedScales q).A=q.A*q.B ∧
      (phaseSortedScales q).N*(phaseSortedScales q).M=q.M*q.N ∧
      (phaseSortedScales q).H=q.H ∧ (phaseSideSwapScales (phaseSortedScales q)).mass=q.mass
    rw [phase_side_swap_mass,hs.2.2,hs.1,hs.2.1]
    simp [phaseSortedScales,phasePairSwapScales,mul_comm]

theorem phase_normalized_comparability {K : ℝ} (q : QuadraticScales)
    (h₁ : q.A*q.M ≤ K*(q.B*q.N)) (h₂ : q.B*q.N ≤ K*(q.A*q.M)) :
    (phaseNormalizedScales q).A*(phaseNormalizedScales q).M ≤
        K*((phaseNormalizedScales q).B*(phaseNormalizedScales q).N) ∧
      (phaseNormalizedScales q).B*(phaseNormalizedScales q).N ≤
        K*((phaseNormalizedScales q).A*(phaseNormalizedScales q).M) := by
  have hs := phase_sorted_products q
  unfold phaseNormalizedScales
  dsimp only
  split_ifs
  · change (phaseSortedScales q).A*(phaseSortedScales q).M ≤
        K*((phaseSortedScales q).B*(phaseSortedScales q).N) ∧ _
    rw [hs.1,hs.2.1]
    exact ⟨h₁,h₂⟩
  · change (phaseSortedScales q).B*(phaseSortedScales q).N ≤
        K*((phaseSortedScales q).A*(phaseSortedScales q).M) ∧ _
    rw [hs.1,hs.2.1]
    constructor
    · exact h₂
    · change (phaseSortedScales q).A*(phaseSortedScales q).M ≤
        K*((phaseSortedScales q).B*(phaseSortedScales q).N)
      rw [hs.1,hs.2.1]
      exact h₁

end
end Sechstmoment
