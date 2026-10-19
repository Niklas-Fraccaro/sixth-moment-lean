import Sechstmoment.Numerator.U.Separation.NearPairProductLower
import Sechstmoment.Numerator.U.Sources.FiniteReindex
import Sechstmoment.Numerator.U.Sources.GlobalSupport

/-! Actual active-near witnesses force polynomial ratio thresholds on
every supported integer term in an excluded soft-order or unit block. -/
namespace Sechstmoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem a03_actual_quad_smooth_support (k v : Fin 4→ℕ)
    (hw : rectangularAFESmoothWeight k v≠0) (j : Fin 4) :
    (v j+1:ℝ)∈Icc (rectangularAFESmoothScale (k j)) (2*rectangularAFESmoothScale (k j)) := by
  rw [rectangularAFESmoothWeight_scaled_arguments] at hw
  have hz := (Finset.prod_ne_zero_iff.mp hw) j (Finset.mem_univ j)
  have hs := rectangularSmoothBlockWeight_tsupport (subset_tsupport _ hz)
  have hp := boundaryActual_scale_pos (k j)
  exact ⟨by simpa using (le_div_iff₀ hp).mp hs.1,(div_le_iff₀ hp).mp hs.2⟩

theorem a03_actual_quad_unit_coordinate (k v : Fin 4→ℕ)
    (hw : rectangularAFESmoothWeight k v≠0) (j : Fin 4) (hj : k j=0) : v j=0 := by
  have hs := (a03_actual_quad_smooth_support k v hw j).2
  simp only [hj,rectangularAFESmoothScale,pow_zero] at hs
  have hb : (v j:ℝ)<1 := by linarith
  have hb' : v j<1 := by exact_mod_cast hb
  omega

theorem a03_actual_scales_mass_pos {A B H : ℝ} (hA : 0<A) (hB : 0<B) (k : Fin 4→ℕ) :
    0<(phaseActualScales A B H k).mass := by
  unfold phaseActualScales QuadraticScales.mass QuadraticScales.M QuadraticScales.N
  have h0 := boundaryActual_scale_pos (k 0)
  have h1 := boundaryActual_scale_pos (k 1)
  have h2 := boundaryActual_scale_pos (k 2)
  have h3 := boundaryActual_scale_pos (k 3)
  positivity

theorem a03_actual_near_native_mass_lower {T A B H η : ℝ}
    (hA : 0<A) (hB : 0<B) (hH : 2/3≤H) (hη : 0<η)
    (f g : ℝ→ℝ) (k : Fin 4→ℕ)
    (hn : phaseActualActiveNearBlock T A B H η f g k) :
    1/(144*η^2)≤(phaseActualScales A B H k).mass := by
  obtain ⟨a,b,h,v,positive,ha,hb,hw,hh,_hr,hnear⟩ := hn
  have hH0 : 0<H := by linarith
  let q := phaseActualScales A B H k
  have hqp := boundaryActual_scales_pos A B H k hA hB hH0
  have hqs := phase_actual_source_tuple_support T A B H f g hA hB hH0 k v a b h ha hb hw hh
  have hg := phase_active_near_gap_scale_bound q (fun j => (hqp j).le)
    (rectangularAFESourceTuple a b v h) hqs hη.le hnear
  have hm : 0≤q.mass := (a03_actual_scales_mass_pos hA hB k).le
  change H≤8*η*Real.sqrt q.mass at hg
  have hs := Real.sq_sqrt hm
  have hl : 1≤12*η*Real.sqrt q.mass := by nlinarith
  have hsq : 1≤144*η^2*q.mass := by nlinarith [sq_nonneg (12*η*Real.sqrt q.mass-1)]
  exact (div_le_iff₀ (by positivity : 0<144*η^2)).mpr (by nlinarith)

theorem a03_actual_near_embedded_mass_lower {T A B H η : ℝ}
    (hA : 0<A) (hB : 0<B) (hH : 2/3≤H) (hη : 0<η)
    (f g : ℝ→ℝ) (k : Fin 4→ℕ)
    (hn : phaseActualActiveNearBlock T A B H η f g k) :
    1/(144*η^2)≤(boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).mass := by
  have hl := a03_actual_near_native_mass_lower hA hB hH hη f g k hn
  exact hl.trans (boundaryEmbedded_mass_le _ _ (le_trans (by positivity) hl))

/-- Any supported integer ratio in a block that fails the embedded soft
M-order exceeds the embedded mass power divided by a fixed constant. -/
theorem a03_actual_bad_soft_M_ratio {A B H ε : ℝ}
    (hA : 0<A) (hB : 0<B) (hH : 0<H) (k v : Fin 4→ℕ)
    (hw : rectangularAFESmoothWeight k v≠0)
    (hbad : ¬(boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).M₁≤
      (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).M₂*
        (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).mass^ε) :
    (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).mass^ε/64≤
      (v 0+1:ℝ)/(v 1+1:ℝ) := by
  let q := phaseActualScales A B H k
  let qe := boundaryEmbeddedScales (boundaryActualFlags k) q
  have hqp := boundaryActual_scales_pos A B H k hA hB hH
  have h1 := boundaryEmbedded_size_bounds (boundaryActualFlags k) q (fun j => (hqp j).le) 2
  have h2 := boundaryEmbedded_size_bounds (boundaryActualFlags k) q (fun j => (hqp j).le) 3
  have hv1 := a03_actual_quad_smooth_support k v hw 0
  have hv2 := a03_actual_quad_smooth_support k v hw 1
  have hp : 0≤qe.mass^ε := Real.rpow_nonneg ((a03_actual_scales_mass_pos hA hB k).le.trans
    (boundaryEmbedded_mass_le _ _ (a03_actual_scales_mass_pos hA hB k).le)) _
  have hb : qe.M₂*qe.mass^ε<qe.M₁ := by exact lt_of_not_ge hbad
  have hc : q.M₂*qe.mass^ε<32*q.M₁ := by
    have hh := mul_le_mul_of_nonneg_right h2.1 hp
    simp only [QuadraticScales.size] at hh h1
    exact lt_of_le_of_lt hh (hb.trans_le h1.2)
  apply (le_div_iff₀ (by positivity : (0:ℝ)<v 1+1)).mpr
  dsimp only [q,phaseActualScales] at hc
  have hm := mul_le_mul_of_nonneg_left hv2.2 hp
  nlinarith [hv1.1]

theorem a03_actual_bad_soft_N_ratio {A B H ε : ℝ}
    (hA : 0<A) (hB : 0<B) (hH : 0<H) (k v : Fin 4→ℕ)
    (hw : rectangularAFESmoothWeight k v≠0)
    (hbad : ¬(boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).N₁≤
      (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).N₂*
        (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).mass^ε) :
    (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).mass^ε/64≤
      (v 2+1:ℝ)/(v 3+1:ℝ) := by
  let q := phaseActualScales A B H k
  let qe := boundaryEmbeddedScales (boundaryActualFlags k) q
  have hqp := boundaryActual_scales_pos A B H k hA hB hH
  have h1 := boundaryEmbedded_size_bounds (boundaryActualFlags k) q (fun j => (hqp j).le) 4
  have h2 := boundaryEmbedded_size_bounds (boundaryActualFlags k) q (fun j => (hqp j).le) 5
  have hv1 := a03_actual_quad_smooth_support k v hw 2
  have hv2 := a03_actual_quad_smooth_support k v hw 3
  have hp : 0≤qe.mass^ε := Real.rpow_nonneg ((a03_actual_scales_mass_pos hA hB k).le.trans
    (boundaryEmbedded_mass_le _ _ (a03_actual_scales_mass_pos hA hB k).le)) _
  have hb : qe.N₂*qe.mass^ε<qe.N₁ := by exact lt_of_not_ge hbad
  have hc : q.N₂*qe.mass^ε<32*q.N₁ := by
    have hh := mul_le_mul_of_nonneg_right h2.1 hp
    simp only [QuadraticScales.size] at hh h1
    exact lt_of_le_of_lt hh (hb.trans_le h1.2)
  apply (le_div_iff₀ (by positivity : (0:ℝ)<v 3+1)).mpr
  dsimp only [q,phaseActualScales] at hc
  have hm := mul_le_mul_of_nonneg_left hv2.2 hp
  nlinarith [hv1.1]

/-- Integrated unit blocks are negligible because every supported first
integer factor has the same large-ratio threshold forced by an actual
near witness in that block. -/
theorem a03_actual_near_integrated_unit_ratio_lower {a b T A B H η : ℝ}
    (hT : 1<T) (hA : 0<A) (hB : 0<B) (hH : 0<H) (hη : 0<η) (hηsmall : η≤1/2)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (k v : Fin 4→ℕ) (hactive : phaseActualActiveNearBlock T A B H η f g k)
    (hv : rectangularAFESmoothWeight k v≠0) :
    (k 1=0 → 1/(4*η*T^a)≤(v 0+1:ℝ)/(v 1+1:ℝ)) ∧
      (k 3=0 → 1/(4*η*T^b)≤(v 2+1:ℝ)/(v 3+1:ℝ)) := by
  obtain ⟨p,r,h,w,positive,hp,hr,hw,hh,hrel,hnear⟩ := hactive
  have hpos := phase_actual_source_tuple_positive T A B H f g hA hB hH k w p r h hp hr hw hh
  have hsupp := phase_actual_source_tuple_support T A B H f g hA hB hH k w p r h hp hr hw hh
  have hpn : 0<p := by simpa [rectangularAFESourceTuple] using hpos 0
  have hrn : 0<r := by simpa [rectangularAFESourceTuple] using hpos 1
  have hpcap := phaseActualAmplifierCoefficient_nonzero_integer_cap hT f hf hpn hp
  have hrcap := phaseActualAmplifierCoefficient_nonzero_integer_cap hT g hg hrn hr
  have ht : 0<T := zero_lt_one.trans hT
  have hl := a03_near_tuple_integrated_unit_lower positive (rectangularAFESourceTuple p r w h)
    hη hηsmall (Real.rpow_pos_of_pos ht a) (Real.rpow_pos_of_pos ht b)
    (fun j => by have := hpos j; omega) hpcap hrcap hrel hnear
  constructor
  · intro hk
    have hwu := a03_actual_quad_unit_coordinate k w hw 1 hk
    have hvu := a03_actual_quad_unit_coordinate k v hv 1 hk
    have hlower := hl.1 (by simp [rectangularAFESourceTuple,hwu])
    have hu := (a03_actual_quad_smooth_support k w hw 0).2
    have hvlow := (a03_actual_quad_smooth_support k v hv 0).1
    change 1/(2*η*T^a)≤((w 0+1:ℕ):ℝ) at hlower
    push_cast at hlower
    simp only [hvu,Nat.cast_zero,zero_add,div_one]
    have he : 1/(4*η*T^a)=(1/(2*η*T^a))/2 := by ring
    rw [he]
    nlinarith
  · intro hk
    have hwu := a03_actual_quad_unit_coordinate k w hw 3 hk
    have hvu := a03_actual_quad_unit_coordinate k v hv 3 hk
    have hlower := hl.2 (by simp [rectangularAFESourceTuple,hwu])
    have hu := (a03_actual_quad_smooth_support k w hw 2).2
    have hvlow := (a03_actual_quad_smooth_support k v hv 2).1
    change 1/(2*η*T^b)≤((w 2+1:ℕ):ℝ) at hlower
    push_cast at hlower
    simp only [hvu,Nat.cast_zero,zero_add,div_one]
    have he : 1/(4*η*T^b)=(1/(2*η*T^b))/2 := by ring
    rw [he]
    nlinarith

/-- The near-block mass grows at least as a fixed positive multiple of
T^(2-2s), including every embedded unit scale. -/
theorem a03_actual_near_embedded_mass_power_lower {T A B H s : ℝ}
    (hT : 0<T) (hA : 0<A) (hB : 0<B) (hH : 2/3≤H)
    (f g : ℝ→ℝ) (k : Fin 4→ℕ)
    (hn : phaseActualActiveNearBlock T A B H (T^(s-1)) f g k) :
    (1/144:ℝ)*T^(2-2*s)≤
      (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)).mass := by
  have hl := a03_actual_near_embedded_mass_lower hA hB hH (Real.rpow_pos_of_pos hT _) f g k hn
  have he : 1/(144*(T^(s-1))^2)=(1/144:ℝ)*T^(2-2*s) := by
    have hp : (T^(s-1))^2=T^(2*s-2) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hT.le]
      congr 1
      norm_num
      ring
    rw [hp]
    calc
      _=(1/144:ℝ)*(T^(2*s-2))⁻¹ := by ring
      _=(1/144:ℝ)*T^(-(2*s-2)) := by rw [Real.rpow_neg hT.le]
      _=_ := by congr 1; congr 1; ring
  rwa [he] at hl

end
end Sechstmoment
