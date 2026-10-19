import Sechstmoment.Numerator.U.Sources.Weights.Superposition
import Sechstmoment.Numerator.U.Sources.Weights.TensorFactory

/-! Numerical source bookkeeping for the literal normalized actual
scales.  The source retains its Poisson term throughout. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem phase_normalized_max_amplifier (q : QuadraticScales) :
    max (phaseNormalizedScales q).A (phaseNormalizedScales q).B=max q.A q.B := by
  unfold phaseNormalizedScales phaseSortedScales phasePairSwapScales
  dsimp only
  split_ifs <;> simp [phaseSideSwapScales,max_comm]

theorem rectangularQuadraticMajorant_phaseNormalized (q : QuadraticScales) (X : ℝ) :
    rectangularQuadraticMajorant (phaseNormalizedScales q).A (phaseNormalizedScales q).B X
      (phaseNormalizedScales q).H=rectangularQuadraticMajorant q.A q.B X q.H := by
  unfold rectangularQuadraticMajorant
  rw [(phase_normalized_invariants q).1,(phase_normalized_invariants q).2.2.1,
    phase_normalized_max_amplifier]

theorem phaseSourceMajorant_rectangular_bound {ε D T r X : ℝ}
    (q : QuadraticScales) (hq : ∀ j, 0≤q.size j)
    (hD : 0≤D) (hT : 0≤T) (hε : 0≤ε) (hX : 0≤X)
    (hmass : q.mass=q.A*q.B*X^2)
    (hgrowth : q.mass≤D*T^r) (hgrowthH : q.mass*q.H^2≤D*T^r) :
    phaseSourceMajorant ε (phaseNormalizedScales q)≤
      (D^ε*T^(r*ε))*(2*rectangularQuadraticMajorant q.A q.B X q.H+q.H^2) := by
  have hA : 0≤q.A := hq 0
  have hB : 0≤q.B := hq 1
  have hH : 0≤q.H := hq 6
  have hm : 0≤q.mass := by rw [hmass]; positivity
  have hnorm : ∀ j, 0≤(phaseNormalizedScales q).size j := by
    have h0 := hq 0; have h1 := hq 1; have h2 := hq 2
    have h3 := hq 3; have h4 := hq 4; have h5 := hq 5; have h6 := hq 6
    norm_num [QuadraticScales.size] at h0 h1 h2 h3 h4 h5 h6
    unfold phaseNormalizedScales phaseSortedScales phasePairSwapScales
    dsimp only
    split_ifs <;> intro j <;> fin_cases j <;>
      simp_all [phaseSideSwapScales,QuadraticScales.size]
  have hmass' : (phaseNormalizedScales q).mass=
      (phaseNormalizedScales q).A*(phaseNormalizedScales q).B*X^2 := by
    rw [(phase_normalized_invariants q).1,(phase_normalized_invariants q).2.2.2]
    exact hmass
  have hmaj := rectangular_source_majorant_le (phaseNormalizedScales q)
    (hnorm 0) (hnorm 1) hX (hnorm 6) hmass'
  rw [rectangularQuadraticMajorant_phaseNormalized] at hmaj
  have hp₁ := rectangular_source_mass_power_le (mul_nonneg hm (sq_nonneg _)) hD hT hε hgrowthH
  have hp₂ := rectangular_source_mass_power_le hm hD hT hε hgrowth
  have hmajor0 : 0≤orientedQuadraticMajorant (phaseNormalizedScales q) := by
    have ha : 0≤(phaseNormalizedScales q).A := hnorm 0
    have hb : 0≤(phaseNormalizedScales q).B := hnorm 1
    have hh : 0≤(phaseNormalizedScales q).H := hnorm 6
    have hm' : 0≤(phaseNormalizedScales q).mass := by rw [(phase_normalized_invariants q).2.2.2]; exact hm
    unfold orientedQuadraticMajorant
    positivity
  unfold phaseSourceMajorant
  rw [(phase_normalized_invariants q).2.2.2,(phase_normalized_invariants q).2.2.1]
  calc
    _ ≤ (D^ε*T^(r*ε))*(2*rectangularQuadraticMajorant q.A q.B X q.H)+
        (D^ε*T^(r*ε))*q.H^2 := by
      apply add_le_add
      · exact mul_le_mul hp₁ hmaj hmajor0 (by positivity)
      · exact mul_le_mul_of_nonneg_right hp₂ (sq_nonneg _)
    _ = _ := by ring

/-- Both source power losses and the Poisson error are explicitly
back-transferred.  The lemma is numerical; no new source contract occurs. -/
theorem phaseSourceMajorant_back_transfer {ε D T r X K : ℝ}
    (q : QuadraticScales) (hq : ∀ j, 0<q.size j)
    (hD : 0≤D) (hT : 0<T) (hε : 0≤ε) (hX : 0<X) (hK : 0<K)
    (hmass : q.mass=q.A*q.B*X^2)
    (hgrowth : q.mass≤D*T^r) (hgrowthH : q.mass*q.H^2≤D*T^r)
    (hH0 : q.H≤K*(q.A*q.B)^(1/2:ℝ)*X/T) :
    T/((q.A*q.B)^(1/2:ℝ)*X)*phaseSourceMajorant ε (phaseNormalizedScales q)≤
      (D^ε*T^(r*ε))*(2*(K^(1/2:ℝ)*T^(1/2:ℝ)*(q.A*q.B)+
        K^(3/4:ℝ)*T^(1/4:ℝ)*(q.A*q.B)^(3/8:ℝ)*max q.A q.B^(1/4:ℝ)*X^(1/2:ℝ))+
          K^2*(q.A*q.B)^(1/2:ℝ)*X/T) := by
  have hA : 0<q.A := hq 0
  have hB : 0<q.B := hq 1
  have hH : 0<q.H := hq 6
  have hb := phaseSourceMajorant_rectangular_bound q (fun j => (hq j).le)
    hD hT.le hε hX.le hmass hgrowth hgrowthH
  calc
    _ ≤ T/((q.A*q.B)^(1/2:ℝ)*X)*
        ((D^ε*T^(r*ε))*(2*rectangularQuadraticMajorant q.A q.B X q.H+q.H^2)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (D^ε*T^(r*ε))*(2*(T/((q.A*q.B)^(1/2:ℝ)*X)*
        rectangularQuadraticMajorant q.A q.B X q.H)+T/((q.A*q.B)^(1/2:ℝ)*X)*q.H^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left (rectangular_H0_back_transfer hT hA hB hX hH hK hH0) (by norm_num))
      (rectangular_poisson_back_transfer hT (mul_pos hA hB) hX hH.le hK hH0)) (by positivity)

end
end Sechstmoment
