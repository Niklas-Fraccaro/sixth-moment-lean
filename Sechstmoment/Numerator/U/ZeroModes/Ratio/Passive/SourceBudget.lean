import Sechstmoment.Numerator.U.Sources.PassiveSoftSourceGlobalPower
import Sechstmoment.Numerator.U.ZeroModes.Ratio.SourceBudget

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03ActualPassiveSoftSourceBlockMajorant (T s ε : ℝ) (f g : ℝ → ℝ)
    (i : (Fin 3 → ℕ)×(Fin 4 → ℕ)) : ℝ :=
  let A := rectangularAFESmoothScale (i.1 0)
  let B := rectangularAFESmoothScale (i.1 1)
  let H := rectangularAFESmoothScale (i.1 2)
  let native := phaseActualScales A B H i.2
  let q := boundaryEmbeddedScales (boundaryActualFlags i.2) native
  if A03ActualPassiveNearZeroBlock T A B H (T^(s-1)) f g i.2 then
    T/((A*B)^(1/2:ℝ)*Real.sqrt (native.M*native.N))*phaseSourceMajorant ε (a03SoftSourceOrientedScales q)
    else 0

def a03ActualPassiveSoftSourceFiniteMajorant (T a b s u ε : ℝ) (f g : ℝ → ℝ) : ℝ :=
  ∑ i∈a03ActualSourceBlockGrid (T^a) (T^b)
    (8*T^((a+b)/2+s+u/2)) (T^(2+u)), a03ActualPassiveSoftSourceBlockMajorant T s ε f g i

def a03ActualPassiveSoftSourceGlobalMajorant (T a b s u ε θ : ℝ) (f g : ℝ → ℝ) : ℝ :=
  2*(2*θ*Real.log T)*a03ActualPassiveSoftSourceFiniteMajorant T a b s u ε f g

theorem a03ActualPassiveSoftSourceBlockMajorant_nonneg {T : ℝ} (hT : 0≤T) (s ε : ℝ)
    (f g : ℝ → ℝ) (i : (Fin 3 → ℕ)×(Fin 4 → ℕ)) :
    0≤a03ActualPassiveSoftSourceBlockMajorant T s ε f g i := by
  unfold a03ActualPassiveSoftSourceBlockMajorant
  dsimp only
  split_ifs
  · have hA := boundaryActual_scale_ge_two_thirds (i.1 0)
    have hB := boundaryActual_scale_ge_two_thirds (i.1 1)
    have hH := boundaryActual_scale_ge_two_thirds (i.1 2)
    have hq1 := boundaryActual_embedded_lower_bounds _ _ _ i.2 hA hB hH
    have hn := a03_soft_source_oriented_lower_bounds _ hq1
    have hm := phase_source_majorant_nonneg ε _ (fun j => zero_le_one.trans (hn j))
    have hAp : 0<rectangularAFESmoothScale (i.1 0) := by linarith
    have hBp : 0<rectangularAFESmoothScale (i.1 1) := by linarith
    have hHp : 0<rectangularAFESmoothScale (i.1 2) := by linarith
    have hp := boundaryActual_scales_pos _ _ _ i.2 hAp hBp hHp
    have hMN : 0<(phaseActualScales (rectangularAFESmoothScale (i.1 0))
      (rectangularAFESmoothScale (i.1 1)) (rectangularAFESmoothScale (i.1 2)) i.2).M*
      (phaseActualScales (rectangularAFESmoothScale (i.1 0))
      (rectangularAFESmoothScale (i.1 1)) (rectangularAFESmoothScale (i.1 2)) i.2).N := by
      unfold QuadraticScales.M QuadraticScales.N
      exact mul_pos (mul_pos (hp 2) (hp 3)) (mul_pos (hp 4) (hp 5))
    positivity
  · exact le_rfl

theorem a03_actual_passive_soft_source_finite_majorant_bound {a b s u ε : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hs0 : 0≤s) (hs : s≤1/8)
    (hu0 : 0<u) (hu : u≤1/8) (hε : 0≤ε)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop,
      0≤a03ActualPassiveSoftSourceFiniteMajorant T a b s u ε f g ∧
      a03ActualPassiveSoftSourceFiniteMajorant T a b s u ε f g≤C*(1+Real.log T)^7*
        (T^(1/2+a+b+s/2+4*ε)+T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*ε)) := by
  have hb0 : 0≤b := ha.trans hab
  have hh0 : 0≤(a+b)/2+s+u/2 := by positivity
  obtain ⟨D,hD,hd⟩ := a03_actual_source_block_grid_uniform_log_card ha hb0 hh0 hu0
  let C := D*(2097152*(67108864:ℝ)^ε)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  filter_upwards [hd,a03_actual_passive_soft_source_native_majorant_power_bound ha hab hlen hs hu hε f g hf hg,
    eventually_ge_atTop (1:ℝ)] with T hcard hblock hT
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hlog : 0≤1+Real.log T := by linarith [Real.log_nonneg hT]
  let grid := a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u))
  have hb : ∀ i∈grid, a03ActualPassiveSoftSourceBlockMajorant T s ε f g i≤
      (2097152*(67108864:ℝ)^ε)*(T^(1/2+a+b+s/2+4*ε)+T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*ε)) := by
    intro i hi
    unfold a03ActualPassiveSoftSourceBlockMajorant
    dsimp only
    split_ifs with hactive
    · exact hblock _ _ _ (boundaryActual_scale_ge_two_thirds (i.1 0))
        (boundaryActual_scale_ge_two_thirds (i.1 1)) (boundaryActual_scale_ge_two_thirds (i.1 2))
        i.2 (Finset.mem_product.mp hi).2 hactive
    · positivity
  refine ⟨Finset.sum_nonneg (fun i _ => a03ActualPassiveSoftSourceBlockMajorant_nonneg hTp.le s ε f g i),?_⟩
  calc
    _≤(grid.card:ℝ)*((2097152*(67108864:ℝ)^ε)*(T^(1/2+a+b+s/2+4*ε)+T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*ε))) := by
      exact (Finset.sum_le_sum hb).trans_eq (by simp)
    _≤(D*(1+Real.log T)^7)*((2097152*(67108864:ℝ)^ε)*(T^(1/2+a+b+s/2+4*ε)+T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*ε))) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _=_ := by dsimp [C]; ring

theorem a03_actual_passive_soft_source_global_majorant_bound {a b s u ε θ : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hs0 : 0≤s) (hs : s≤1/8)
    (hu0 : 0<u) (hu : u≤1/8) (hε : 0≤ε) (hθ : 0≤θ)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop,
      0≤a03ActualPassiveSoftSourceGlobalMajorant T a b s u ε θ f g ∧
      a03ActualPassiveSoftSourceGlobalMajorant T a b s u ε θ f g≤C*(1+Real.log T)^8*
        (T^(1/2+a+b+s/2+4*ε)+T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*ε)) := by
  obtain ⟨C,hC,hb⟩ := a03_actual_passive_soft_source_finite_majorant_bound ha hab hlen hs0 hs hu0 hu hε f g hf hg
  refine ⟨4*θ*C,by positivity,?_⟩
  filter_upwards [hb,eventually_ge_atTop (1:ℝ)] with T hb hT
  have hlog : 0≤Real.log T := Real.log_nonneg hT
  have hfinite0 := hb.1
  unfold a03ActualPassiveSoftSourceGlobalMajorant
  refine ⟨by positivity,?_⟩
  calc
    _≤2*(2*θ*Real.log T)*(C*(1+Real.log T)^7*
      (T^(1/2+a+b+s/2+4*ε)+T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*ε))) := mul_le_mul_of_nonneg_left hb.2 (by positivity)
    _≤2*(2*θ*(1+Real.log T))*(C*(1+Real.log T)^7*
      (T^(1/2+a+b+s/2+4*ε)+T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*ε))) := by gcongr; linarith
    _=_ := by ring


theorem a03ActualPassiveSoftSourceGlobalMajorant_eq_mellin_integral
    {T θ : ℝ} (hT : 1≤T) (hθ : 0≤θ) (a b s u ε : ℝ) (f g : ℝ → ℝ) :
    (∫ _v in Icc (-θ*Real.log T) (θ*Real.log T),
      ∑ _positive : Bool, a03ActualPassiveSoftSourceFiniteMajorant T a b s u ε f g)=
      a03ActualPassiveSoftSourceGlobalMajorant T a b s u ε θ f g := by
  simp only [Fintype.sum_bool]
  rw [setIntegral_const,Real.volume_real_Icc,max_eq_left (by nlinarith [Real.log_nonneg hT]),smul_eq_mul]
  unfold a03ActualPassiveSoftSourceGlobalMajorant
  ring

theorem a03_actual_passive_soft_source_global_majorant_isLittleO {a b s u ε θ : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hs0 : 0≤s) (hs : s≤1/8)
    (hu0 : 0<u) (hu : u≤1/8) (hε : 0≤ε) (hθ : 0≤θ)
    (hloss1 : s/2+4*ε≤rectangularSlack a b)
    (hloss2 : 3*s/4+u/4+4*ε≤rectangularSlack a b)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    (fun T : ℝ => a03ActualPassiveSoftSourceGlobalMajorant T a b s u ε θ f g)=o[atTop]
      (fun T : ℝ => T) := by
  obtain ⟨C,hC,hb⟩ := a03_actual_passive_soft_source_global_majorant_bound ha hab hlen hs0 hs hu0 hu hε hθ f g hf hg
  have henvelope := (polylog_weighted_power_sum_isLittleO hab hlen 8).const_mul_left (256*C)
  apply (show (fun T : ℝ => a03ActualPassiveSoftSourceGlobalMajorant T a b s u ε θ f g)=O[atTop]
    (fun T : ℝ => (256*C)*((Real.log T)^8*(T^rectangularFirstExponent a b (rectangularSlack a b)+
      T^rectangularSecondExponent a b (rectangularSlack a b)))) from ?_).trans_isLittleO henvelope
  apply Eventually.isBigO
  filter_upwards [hb,Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    eventually_ge_atTop (1:ℝ)] with T hb hlog hT
  rw [Real.norm_of_nonneg hb.1]
  have hl : (1+Real.log T)^8≤256*(Real.log T)^8 := by
    have he := pow_le_pow_left₀ (by linarith : 0≤1+Real.log T) (by linarith : 1+Real.log T≤2*Real.log T) 8
    simpa only [mul_pow,show (2:ℝ)^8=256 by norm_num] using he
  have hp1 : T^(1/2+a+b+s/2+4*ε)≤T^rectangularFirstExponent a b (rectangularSlack a b) :=
    Real.rpow_le_rpow_of_exponent_le hT (by unfold rectangularFirstExponent; linarith only [hloss1])
  have hp2 : T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*ε)≤T^rectangularSecondExponent a b (rectangularSlack a b) :=
    Real.rpow_le_rpow_of_exponent_le hT (by unfold rectangularSecondExponent; linarith only [hloss2])
  calc
    _≤C*(1+Real.log T)^8*(T^(1/2+a+b+s/2+4*ε)+T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*ε)) := hb.2
    _≤C*(256*(Real.log T)^8)*(T^rectangularFirstExponent a b (rectangularSlack a b)+
      T^rectangularSecondExponent a b (rectangularSlack a b)) := by gcongr
    _=_ := by ring

theorem a03_actual_passive_soft_source_restored_global_majorant_isLittleO {a b s u ε e θ : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hs0 : 0≤s) (hs : s≤1/8)
    (hu0 : 0<u) (hu : u≤1/8) (hε : 0≤ε) (hθ : 0≤θ)
    (hloss1 : s/2+4*ε+e≤rectangularSlack a b)
    (hloss2 : 3*s/4+u/4+4*ε+e≤rectangularSlack a b)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    (fun T : ℝ => T^e*a03ActualPassiveSoftSourceGlobalMajorant T a b s u ε θ f g)=o[atTop]
      (fun T : ℝ => T) := by
  obtain ⟨C,hC,hb⟩ := a03_actual_passive_soft_source_global_majorant_bound ha hab hlen hs0 hs hu0 hu hε hθ f g hf hg
  have henvelope := (polylog_weighted_power_sum_isLittleO hab hlen 8).const_mul_left (256*C)
  apply (show (fun T : ℝ => T^e*a03ActualPassiveSoftSourceGlobalMajorant T a b s u ε θ f g)=O[atTop]
    (fun T : ℝ => (256*C)*((Real.log T)^8*(T^rectangularFirstExponent a b (rectangularSlack a b)+
      T^rectangularSecondExponent a b (rectangularSlack a b)))) from ?_).trans_isLittleO henvelope
  apply Eventually.isBigO
  filter_upwards [hb,Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    eventually_ge_atTop (1:ℝ)] with T hb hlog hT
  have hTp : 0<T := zero_lt_one.trans_le hT
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hTp.le e) hb.1)]
  have hl : (1+Real.log T)^8≤256*(Real.log T)^8 := by
    have he := pow_le_pow_left₀ (by linarith : 0≤1+Real.log T) (by linarith : 1+Real.log T≤2*Real.log T) 8
    simpa only [mul_pow,show (2:ℝ)^8=256 by norm_num] using he
  have hp1 : T^(1/2+a+b+s/2+4*ε+e)≤T^rectangularFirstExponent a b (rectangularSlack a b) :=
    Real.rpow_le_rpow_of_exponent_le hT (by unfold rectangularFirstExponent; linarith only [hloss1])
  have hp2 : T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*ε+e)≤T^rectangularSecondExponent a b (rectangularSlack a b) :=
    Real.rpow_le_rpow_of_exponent_le hT (by unfold rectangularSecondExponent; linarith only [hloss2])
  calc
    _≤T^e*(C*(1+Real.log T)^8*(T^(1/2+a+b+s/2+4*ε)+T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*ε))) :=
      mul_le_mul_of_nonneg_left hb.2 (Real.rpow_nonneg hTp.le e)
    _=C*(1+Real.log T)^8*(T^(1/2+a+b+s/2+4*ε+e)+T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*ε+e)) := by
      simp_rw [Real.rpow_add hTp]
      ring
    _≤C*(256*(Real.log T)^8)*(T^rectangularFirstExponent a b (rectangularSlack a b)+
      T^rectangularSecondExponent a b (rectangularSlack a b)) := by gcongr
    _=_ := by ring


end
end Sechstmoment
