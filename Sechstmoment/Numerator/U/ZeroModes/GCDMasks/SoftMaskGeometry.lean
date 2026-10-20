import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.PassiveSupport
import Sechstmoment.Numerator.U.ZeroModes.Ratio.GeometricTails
import Sechstmoment.Numerator.U.ZeroModes.Ratio.Passive.SourceErrorAggregate

namespace Sechstmoment
open Complex Real Source Set
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem A03PassiveNativeZeroWitness.bad_soft_M_ratio
    {T A B H η ε : ℝ} {f g : ℝ→ℝ} {k : Fin 4→ℕ}
    (p : A03PassiveNativeZeroWitness T A B H η f g k)
    (hA : 0<A) (hB : 0<B) (hH : 0<H)
    (hbad : ¬(boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).M₁≤
      (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).M₂*
        (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).mass^ε) :
    (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).mass^ε/64≤
      (p.w 0:ℝ)*(p.w 2:ℝ)^2/p.X := by
  let q := phaseActualScales A B H k
  let qe := boundaryEmbeddedScales (boundaryActualFlags k) q
  have hqp := boundaryActual_scales_pos A B H k hA hB hH
  have h1 := boundaryEmbedded_size_bounds (boundaryActualFlags k) q (fun j => (hqp j).le) 2
  have h2 := boundaryEmbedded_size_bounds (boundaryActualFlags k) q (fun j => (hqp j).le) 3
  have hv1 := p.quad_support 0
  have hv2 := p.quad_support 1
  have hp : 0≤qe.mass^ε := Real.rpow_nonneg ((a03_actual_scales_mass_pos hA hB k).le.trans
    (boundaryEmbedded_mass_le _ _ (a03_actual_scales_mass_pos hA hB k).le)) _
  have hb : qe.M₂*qe.mass^ε<qe.M₁ := lt_of_not_ge hbad
  have hc : q.M₂*qe.mass^ε<32*q.M₁ := by
    have hh := mul_le_mul_of_nonneg_right h2.1 hp
    simp only [QuadraticScales.size] at hh h1
    exact lt_of_le_of_lt hh (hb.trans_le h1.2)
  have hratio := (a03NativeGCDCoordinateQuad_ratio p.w p.integer_pos p.X_pos).1
  rw [←hratio]
  apply (le_div_iff₀ (a03NativeGCDCoordinateQuad_pos p.w p.integer_pos p.X_pos 1)).mpr
  dsimp only [q,phaseActualScales] at hc
  have hm := mul_le_mul_of_nonneg_left hv2.2 hp
  nlinarith [hv1.1]

theorem A03PassiveNativeZeroWitness.bad_soft_N_ratio
    {T A B H η ε : ℝ} {f g : ℝ→ℝ} {k : Fin 4→ℕ}
    (p : A03PassiveNativeZeroWitness T A B H η f g k)
    (hA : 0<A) (hB : 0<B) (hH : 0<H)
    (hbad : ¬(boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).N₁≤
      (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).N₂*
        (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).mass^ε) :
    (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).mass^ε/64≤
      (p.w 1:ℝ)*(p.w 3:ℝ)^2/p.X := by
  let q := phaseActualScales A B H k
  let qe := boundaryEmbeddedScales (boundaryActualFlags k) q
  have hqp := boundaryActual_scales_pos A B H k hA hB hH
  have h1 := boundaryEmbedded_size_bounds (boundaryActualFlags k) q (fun j => (hqp j).le) 4
  have h2 := boundaryEmbedded_size_bounds (boundaryActualFlags k) q (fun j => (hqp j).le) 5
  have hv1 := p.quad_support 2
  have hv2 := p.quad_support 3
  have hp : 0≤qe.mass^ε := Real.rpow_nonneg ((a03_actual_scales_mass_pos hA hB k).le.trans
    (boundaryEmbedded_mass_le _ _ (a03_actual_scales_mass_pos hA hB k).le)) _
  have hb : qe.N₂*qe.mass^ε<qe.N₁ := lt_of_not_ge hbad
  have hc : q.N₂*qe.mass^ε<32*q.N₁ := by
    have hh := mul_le_mul_of_nonneg_right h2.1 hp
    simp only [QuadraticScales.size] at hh h1
    exact lt_of_le_of_lt hh (hb.trans_le h1.2)
  have hratio := (a03NativeGCDCoordinateQuad_ratio p.w p.integer_pos p.X_pos).2
  rw [←hratio]
  apply (le_div_iff₀ (a03NativeGCDCoordinateQuad_pos p.w p.integer_pos p.X_pos 3)).mpr
  dsimp only [q,phaseActualScales] at hc
  have hm := mul_le_mul_of_nonneg_left hv2.2 hp
  nlinarith [hv1.1]

theorem A03PassiveNativeZeroWitness.integrated_unit_bounds
    {T A B H η : ℝ} {f g : ℝ→ℝ} {k : Fin 4→ℕ}
    (p : A03PassiveNativeZeroWitness T A B H η f g k) :
    (k 1=0 → p.X/((p.w 0:ℝ)*p.w 2)≤4/3) ∧
      (k 3=0 → p.X/((p.w 1:ℝ)*p.w 3)≤4/3) := by
  constructor
  · intro hk
    have h := (p.quad_support 1).2
    change p.X/((p.w 0:ℝ)*p.w 2)≤2*rectangularAFESmoothScale (k 1) at h
    norm_num only [hk,rectangularAFESmoothScale,pow_zero] at h
    exact h
  · intro hk
    have h := (p.quad_support 3).2
    change p.X/((p.w 1:ℝ)*p.w 3)≤2*rectangularAFESmoothScale (k 3) at h
    norm_num only [hk,rectangularAFESmoothScale,pow_zero] at h
    exact h

end
end Sechstmoment
