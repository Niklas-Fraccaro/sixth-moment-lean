import Sechstmoment.Numerator.U.Sources.Weights.NormalizationShape

namespace Sechstmoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 1000000

def phaseSortedWeights (q : QuadraticScales) (W : Fin 5 → ℝ → ℂ) : Fin 5 → ℝ → ℂ :=
  phasePairSwapWeights (decide (q.M₂ < q.M₁)) (decide (q.N₂ < q.N₁)) W
def phaseNormalizedWeights (q : QuadraticScales) (W : Fin 5 → ℝ → ℂ) : Fin 5 → ℝ → ℂ :=
  let s := phaseSortedScales q
  if s.B*s.N₁ ≤ s.A*s.M₁ then phaseSortedWeights q W
    else phaseSideSwapWeights (phaseSortedWeights q W)
def phaseNormalizedAlpha (q : QuadraticScales) (A B : ℕ → ℂ) : ℕ → ℂ :=
  let s := phaseSortedScales q
  if s.B*s.N₁ ≤ s.A*s.M₁ then A else B
def phaseNormalizedBeta (q : QuadraticScales) (A B : ℕ → ℂ) : ℕ → ℂ :=
  let s := phaseSortedScales q
  if s.B*s.N₁ ≤ s.A*s.M₁ then B else A
def phaseNormalizedSign (q : QuadraticScales) (positive : Bool) : Bool :=
  let s := phaseSortedScales q
  if s.B*s.N₁ ≤ s.A*s.M₁ then positive else !positive

theorem phase_normalized_quadratic_sum (q : QuadraticScales) (positive : Bool)
    (A B : ℕ → ℂ) (W : Fin 5 → ℝ → ℂ) :
    rectangularComplexQuadraticSum (phaseNormalizedSign q positive) (phaseNormalizedScales q)
      (phaseNormalizedAlpha q A B) (phaseNormalizedBeta q A B) (phaseNormalizedWeights q W)=
      rectangularComplexQuadraticSum positive q A B W := by
  unfold phaseNormalizedSign phaseNormalizedScales phaseNormalizedAlpha
    phaseNormalizedBeta phaseNormalizedWeights
  dsimp only
  split_ifs
  · exact phase_pair_swap_quadratic_sum _ _ positive q A B W
  · rw [phase_side_swap_quadratic_sum]
    exact phase_pair_swap_quadratic_sum _ _ positive q A B W

private theorem pair_weights_complex (q : QuadraticScales) (W : Fin 5 → ℝ → ℂ)
    (hW : ∀ i, RectangularComplexWeight (W i)) :
    ∀ i, RectangularComplexWeight (phaseSortedWeights q W i) := by
  intro i
  unfold phaseSortedWeights
  generalize decide (q.M₂ < q.M₁)=m
  generalize decide (q.N₂ < q.N₁)=n
  cases m <;> cases n <;> fin_cases i <;> simp [phasePairSwapWeights]
  all_goals first | exact hW 0 | exact hW 1 | exact hW 2 | exact hW 3 | exact hW 4

theorem phase_normalized_weights_complex (q : QuadraticScales) (W : Fin 5 → ℝ → ℂ)
    (hW : ∀ i, RectangularComplexWeight (W i)) :
    ∀ i, RectangularComplexWeight (phaseNormalizedWeights q W i) := by
  have hs := pair_weights_complex q W hW
  unfold phaseNormalizedWeights
  split_ifs
  · exact hs
  · intro i
    fin_cases i <;> simp [phaseSideSwapWeights]
    all_goals first | exact hs 0 | exact hs 1 | exact hs 2 | exact hs 3 | exact hs 4

theorem phase_normalized_weights_derivatives (q : QuadraticScales) (W : Fin 5 → ℝ → ℂ)
    (ε : ℝ) (bounds : ℕ → ℝ)
    (hd : ∀ j i x, ‖iteratedDeriv j (W i) x‖≤bounds j*q.mass^ε) :
    ∀ j i x, ‖iteratedDeriv j (phaseNormalizedWeights q W i) x‖≤
      bounds j*(phaseNormalizedScales q).mass^ε := by
  rw [(phase_normalized_invariants q).2.2.2]
  intro j i x
  unfold phaseNormalizedWeights
  split_ifs <;> unfold phaseSortedWeights
  all_goals
    generalize decide (q.M₂ < q.M₁)=m
    generalize decide (q.N₂ < q.N₁)=n
    cases m <;> cases n <;> fin_cases i <;> simp [phasePairSwapWeights,phaseSideSwapWeights]
    all_goals first | exact hd j 0 x | exact hd j 1 x | exact hd j 2 x |
      exact hd j 3 x | exact hd j 4 x

theorem phase_normalized_coefficient_supports (q : QuadraticScales) (A B : ℕ → ℂ)
    (hA : ∀ n : ℕ, (n:ℝ)∉Icc q.A (2*q.A) → A n=0)
    (hB : ∀ n : ℕ, (n:ℝ)∉Icc q.B (2*q.B) → B n=0) :
    (∀ n : ℕ, (n:ℝ)∉Icc (phaseNormalizedScales q).A (2*(phaseNormalizedScales q).A) →
      phaseNormalizedAlpha q A B n=0) ∧
    (∀ n : ℕ, (n:ℝ)∉Icc (phaseNormalizedScales q).B (2*(phaseNormalizedScales q).B) →
      phaseNormalizedBeta q A B n=0) := by
  unfold phaseNormalizedScales phaseNormalizedAlpha phaseNormalizedBeta
  dsimp only
  split_ifs
  · exact ⟨hA,hB⟩
  · exact ⟨hB,hA⟩

theorem phase_normalized_coefficient_bounds (q : QuadraticScales) (A B : ℕ → ℂ)
    (K ε : ℝ) (hA : ∀ n : ℕ, ‖A n‖≤K*q.A^ε) (hB : ∀ n : ℕ, ‖B n‖≤K*q.B^ε) :
    (∀ n : ℕ, ‖phaseNormalizedAlpha q A B n‖≤K*(phaseNormalizedScales q).A^ε) ∧
    (∀ n : ℕ, ‖phaseNormalizedBeta q A B n‖≤K*(phaseNormalizedScales q).B^ε) := by
  unfold phaseNormalizedScales phaseNormalizedAlpha phaseNormalizedBeta
  dsimp only
  split_ifs
  · exact ⟨hA,hB⟩
  · exact ⟨hB,hA⟩

theorem phase_source_mass_ge_one (q : QuadraticScales) (hq : ∀ j, 1≤q.size j) : 1≤q.mass := by
  have hA := hq 0; have hB := hq 1; have hM₁ := hq 2; have hM₂ := hq 3
  have hN₁ := hq 4; have hN₂ := hq 5
  norm_num [QuadraticScales.size] at hA hB hM₁ hM₂ hN₁ hN₂
  unfold QuadraticScales.mass QuadraticScales.M QuadraticScales.N
  calc
    (1:ℝ) = 1*1*(1*1)*(1*1) := by norm_num
    _ ≤ _ := by gcongr

theorem phase_normalized_source_admissible {ε K : ℝ} (hε : 0≤ε)
    (q : QuadraticScales) (hq : ∀ j, 1≤q.size j)
    (hH : q.H≤K*(q.A*q.B)^(1/2+ε)) (hδ : q.A*q.B≤K*q.M*q.N)
    (h₁ : q.A*q.M≤K*q.B*q.N) (h₂ : q.B*q.N≤K*q.A*q.M)
    (A B : ℕ → ℂ) (hAs : ∀ n : ℕ, (n:ℝ)∉Icc q.A (2*q.A) → A n=0)
    (hBs : ∀ n : ℕ, (n:ℝ)∉Icc q.B (2*q.B) → B n=0)
    (hAb : ∀ n : ℕ, ‖A n‖≤K*q.A^ε) (hBb : ∀ n : ℕ, ‖B n‖≤K*q.B^ε)
    (W : Fin 5 → ℝ → ℂ) (hW : ∀ i, RectangularComplexWeight (W i))
    (bounds : ℕ → ℝ) (hd : ∀ j i x, ‖iteratedDeriv j (W i) x‖≤bounds j*q.mass^ε)
    (c : Fin 5 → Bool) :
    QuadraticAdmissible ε 1 K bounds (phaseNormalizedScales q)
      (phaseNormalizedAlpha q A B) (phaseNormalizedBeta q A B)
      (rectangularRealComponent (phaseNormalizedWeights q W) c) := by
  have hs := phase_normalized_scale_bounds q hq
  have hi := phase_normalized_invariants q
  have hc := phase_normalized_comparability q (by simpa [mul_assoc] using h₁)
    (by simpa [mul_assoc] using h₂)
  have hcs := phase_normalized_coefficient_supports q A B hAs hBs
  have hcb := phase_normalized_coefficient_bounds q A B K ε hAb hBb
  have hw := phase_normalized_weights_complex q W hW
  have hwd := phase_normalized_weights_derivatives q W ε bounds hd
  have hm : 1≤(phaseNormalizedScales q).mass^ε :=
    Real.one_le_rpow (phase_source_mass_ge_one _ hs.1) hε
  have hm₂ : 0≤(phaseNormalizedScales q).M₂ := by
    have h := hs.1 3
    norm_num [QuadraticScales.size] at h
    linarith
  have hn₂ : 0≤(phaseNormalizedScales q).N₂ := by
    have h := hs.1 5
    norm_num [QuadraticScales.size] at h
    linarith
  refine ⟨hs.1,hs.2.1.trans (le_mul_of_one_le_right hm₂ hm),
    hs.2.2.1.trans (le_mul_of_one_le_right hn₂ hm),?_,?_,?_,?_,hs.2.2.2,
    hcs.1,hcs.2,hcb.1,hcb.2,rectangular_component_smooth _ hw c,?_⟩
  · rw [hi.1,hi.2.2.1]
    exact hH
  · rw [Real.rpow_one,hi.1]
    simpa [mul_assoc,hi.2.1] using hδ
  · simpa [mul_assoc] using hc.1
  · simpa [mul_assoc] using hc.2
  · intro j i x
    exact (rectangular_component_derivative_norm_le _ hw c j i x).trans (hwd j i x)

end
end Sechstmoment
