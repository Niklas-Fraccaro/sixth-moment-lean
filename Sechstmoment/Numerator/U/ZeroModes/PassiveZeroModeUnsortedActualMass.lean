import Sechstmoment.Numerator.U.Sources.PassiveNativeSourceGrowth
import Sechstmoment.Numerator.U.ZeroModes.UnsortedActualMass

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_actual_passive_zero_mode_unsorted_mass_uniform_polylog {a b s η : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hη : 0<η)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ,
      2/3≤A → 2/3≤B → 2/3≤H → ∀ k : Fin 4→ℕ,
      k∈rectangularAFEProductScaleGrid (T^(2+η)) →
      A03ActualPassiveNearZeroBlock T A B H (T^(s-1)) f g k →
      a03ZeroModeLiteralMass (phaseActualScales A B H k)≤C*H*(1+Real.log T)^4 := by
  let r := a+b+2+η
  let C := 2*Real.log 2*(1+Real.log 8+r)^4
  have hr : 0≤r := by dsimp [r]; linarith
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  filter_upwards [a03_actual_passive_source_scale_budget f g hf hg,eventually_ge_atTop (1:ℝ)] with T hbnd hT
  intro A B H hA hB hH k hk hactive
  let q := phaseActualScales A B H k
  have hAp : 0<A := by linarith
  have hBp : 0<B := by linarith
  have hHp : 0<H := by linarith
  have hbnd := hbnd A B H hAp hBp hHp k hk hactive
  have hl : ∀ j,2/3≤(phaseActualScales A B H k).size j := by
    intro j
    fin_cases j <;> simp [phaseActualScales,QuadraticScales.size] <;>
      first | exact hA | exact hB | exact hH | exact boundaryActual_scale_ge_two_thirds _
  have hbasic : q.A=A ∧ q.B=B ∧ q.H=H ∧ q.M*q.N=(phaseActualScales A B H k).M*(phaseActualScales A B H k).N := ⟨rfl,rfl,rfl,rfl⟩
  have hquad := a03ZeroModeQuadScales_le_four_product q hl
  have hcut : q.M*q.N≤T^(2+η) := hbasic.2.2.2.trans_le hbnd.2.2.1
  have hTpow : T^(2+η)≤T^r := Real.rpow_le_rpow_of_exponent_le hT (by dsimp [r]; linarith)
  have hM₁ : q.M₁≤4*T^r := (hquad 0).trans (mul_le_mul_of_nonneg_left (hcut.trans hTpow) (by norm_num))
  have hN₁ : q.N₁≤4*T^r := (hquad 2).trans (mul_le_mul_of_nonneg_left (hcut.trans hTpow) (by norm_num))
  have hAc : q.A≤4*T^r := by
    rw [hbasic.1]
    exact hbnd.1.trans ((Real.rpow_le_rpow_of_exponent_le hT (show a≤r by dsimp [r]; linarith)).trans
      (by nlinarith [Real.rpow_nonneg (zero_le_one.trans hT) r]))
  have hBc : q.B≤4*T^r := by
    rw [hbasic.2.1]
    exact hbnd.2.1.trans ((Real.rpow_le_rpow_of_exponent_le hT (show b≤r by dsimp [r]; linarith)).trans
      (by nlinarith [Real.rpow_nonneg (zero_le_one.trans hT) r]))
  have h := a03ZeroModeLiteralMass_le_polylog hT hr q
    (by rw [hbasic.2.2.1]; exact hHp) (by have := hl 3; change 2/3≤q.M₂ at this; linarith)
    ⟨hl 0,hl 1,hl 2,hl 4⟩ ⟨hAc,hBc,hM₁,hN₁⟩
  change a03ZeroModeLiteralMass q≤C*H*(1+Real.log T)^4
  change a03ZeroModeLiteralMass q≤C*q.H*(1+Real.log T)^4 at h
  rwa [hbasic.2.2.1] at h


def a03ActualPassiveUnsortedZeroModeBlockMass (T s : ℝ) (f g : ℝ→ℝ)
    (i : (Fin 3→ℕ)×(Fin 4→ℕ)) : ℝ :=
  let A := rectangularAFESmoothScale (i.1 0)
  let B := rectangularAFESmoothScale (i.1 1)
  let H := rectangularAFESmoothScale (i.1 2)
  if A03ActualPassiveNearZeroBlock T A B H (T^(s-1)) f g i.2 then
    a03ZeroModeLiteralMass (phaseActualScales A B H i.2) else 0

def a03ActualPassiveUnsortedZeroModeFiniteMass (T a b s η : ℝ) (f g : ℝ→ℝ) : ℝ :=
  ∑ i∈a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+η/2)) (T^(2+η)),
    a03ActualPassiveUnsortedZeroModeBlockMass T s f g i

def a03ActualPassiveUnsortedZeroModeGlobalMass (T a b s η θ : ℝ) (f g : ℝ→ℝ) : ℝ :=
  2*(2*θ*Real.log T)*a03ActualPassiveUnsortedZeroModeFiniteMass T a b s η f g

theorem a03ActualPassiveUnsortedZeroModeBlockMass_nonneg (T s : ℝ) (f g : ℝ→ℝ)
    (i : (Fin 3→ℕ)×(Fin 4→ℕ)) : 0≤a03ActualPassiveUnsortedZeroModeBlockMass T s f g i := by
  unfold a03ActualPassiveUnsortedZeroModeBlockMass
  dsimp only
  split_ifs
  · exact a03ZeroModeLiteralMass_nonneg _
  · exact le_rfl

theorem a03_actual_passive_unsorted_zero_mode_finite_mass_uniform_bound {a b s η : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hs : 0≤s) (hη : 0<η)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,
      0≤a03ActualPassiveUnsortedZeroModeFiniteMass T a b s η f g ∧
      a03ActualPassiveUnsortedZeroModeFiniteMass T a b s η f g≤C*(1+Real.log T)^11*T^((a+b)/2+s+η/2) := by
  obtain ⟨D,hD,hd⟩ := a03_actual_passive_zero_mode_unsorted_mass_uniform_polylog ha hb hη f g hf hg
  obtain ⟨E,hE,he⟩ := a03_actual_source_block_grid_uniform_log_card ha hb (by positivity : 0≤(a+b)/2+s+η/2) hη
  refine ⟨8*D*E,by positivity,?_⟩
  filter_upwards [hd,he,a03_actual_passive_source_scale_budget f g hf hg,eventually_ge_atTop (1:ℝ)]
    with T hd he hscale hT
  let grid := a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+η/2)) (T^(2+η))
  have hlog : 0≤1+Real.log T := by linarith [Real.log_nonneg hT]
  have hbnd : ∀ i∈grid,a03ActualPassiveUnsortedZeroModeBlockMass T s f g i≤8*D*(1+Real.log T)^4*T^((a+b)/2+s+η/2) := by
    intro i hi
    let A := rectangularAFESmoothScale (i.1 0)
    let B := rectangularAFESmoothScale (i.1 1)
    let H := rectangularAFESmoothScale (i.1 2)
    have hA : 2/3≤A := boundaryActual_scale_ge_two_thirds _
    have hB : 2/3≤B := boundaryActual_scale_ge_two_thirds _
    have hH : 2/3≤H := boundaryActual_scale_ge_two_thirds _
    have hk := (Finset.mem_product.mp hi).2
    unfold a03ActualPassiveUnsortedZeroModeBlockMass
    dsimp only
    split_ifs with hactive
    · have hmass := hd A B H hA hB hH i.2 hk hactive
      have hgap := (hscale A B H (by linarith) (by linarith) (by linarith) i.2 hk hactive).2.2.2.2.2
      calc
        _≤D*H*(1+Real.log T)^4 := hmass
        _≤D*(8*T^((a+b)/2+s+η/2))*(1+Real.log T)^4 := by gcongr
        _=_ := by ring
    · positivity
  refine ⟨Finset.sum_nonneg (fun i _ => a03ActualPassiveUnsortedZeroModeBlockMass_nonneg T s f g i),?_⟩
  calc
    _≤(grid.card:ℝ)*(8*D*(1+Real.log T)^4*T^((a+b)/2+s+η/2)) :=
      (Finset.sum_le_sum hbnd).trans_eq (by simp)
    _≤(E*(1+Real.log T)^7)*(8*D*(1+Real.log T)^4*T^((a+b)/2+s+η/2)) :=
      mul_le_mul_of_nonneg_right he (by positivity)
    _=_ := by ring

theorem a03_actual_passive_unsorted_zero_mode_global_mass_uniform_bound {a b s η θ : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hs : 0≤s) (hη : 0<η) (hθ : 0≤θ)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,
      0≤a03ActualPassiveUnsortedZeroModeGlobalMass T a b s η θ f g ∧
      a03ActualPassiveUnsortedZeroModeGlobalMass T a b s η θ f g≤C*(1+Real.log T)^12*T^((a+b)/2+s+η/2) := by
  obtain ⟨C,hC,hbnd⟩ := a03_actual_passive_unsorted_zero_mode_finite_mass_uniform_bound ha hb hs hη f g hf hg
  refine ⟨4*θ*C,by positivity,?_⟩
  filter_upwards [hbnd,eventually_ge_atTop (1:ℝ)] with T hbnd hT
  have hl : 0≤Real.log T := Real.log_nonneg hT
  have hfinite0 := hbnd.1
  unfold a03ActualPassiveUnsortedZeroModeGlobalMass
  refine ⟨by positivity,?_⟩
  calc
    _≤2*(2*θ*Real.log T)*(C*(1+Real.log T)^11*T^((a+b)/2+s+η/2)) :=
      mul_le_mul_of_nonneg_left hbnd.2 (by positivity)
    _≤2*(2*θ*(1+Real.log T))*(C*(1+Real.log T)^11*T^((a+b)/2+s+η/2)) := by gcongr; linarith
    _=_ := by ring

theorem a03_actual_passive_unsorted_zero_mode_weighted_global_mass_isLittleO {a b s η θ ε : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hs : 0≤s) (hη : 0<η) (hθ : 0≤θ)
    (hexp : (a+b)/2+s+η/2+ε<1)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    (fun T : ℝ => T^ε*a03ActualPassiveUnsortedZeroModeGlobalMass T a b s η θ f g)=o[atTop] (fun T : ℝ => T) := by
  obtain ⟨C,hC,hbnd⟩ := a03_actual_passive_unsorted_zero_mode_global_mass_uniform_bound ha hb hs hη hθ f g hf hg
  have ho := (polylog_mul_rpow_isLittleO_id 12 hexp).const_mul_left (4096*C)
  have ho' : (fun T : ℝ => (4096*C)*(Real.log T)^12*T^((a+b)/2+s+η/2+ε))=o[atTop] (fun T : ℝ => T) := by
    simpa only [mul_assoc] using ho
  apply (show (fun T : ℝ => T^ε*a03ActualPassiveUnsortedZeroModeGlobalMass T a b s η θ f g)=O[atTop]
    (fun T : ℝ => (4096*C)*(Real.log T)^12*T^((a+b)/2+s+η/2+ε)) from ?_).trans_isLittleO ho'
  apply Eventually.isBigO
  filter_upwards [hbnd,eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with T hbnd hT hlog
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hT) ε) hbnd.1)]
  have hl : (1+Real.log T)^12≤4096*(Real.log T)^12 := by
    have h := pow_le_pow_left₀ (by linarith : 0≤1+Real.log T) (by linarith : 1+Real.log T≤2*Real.log T) 12
    simpa only [mul_pow,show (2:ℝ)^12=4096 by norm_num] using h
  have hp : T^ε*T^((a+b)/2+s+η/2)=T^((a+b)/2+s+η/2+ε) := by
    rw [←Real.rpow_add (zero_lt_one.trans_le hT)]
    congr 1
    ring
  calc
    _≤T^ε*(C*(1+Real.log T)^12*T^((a+b)/2+s+η/2)) := mul_le_mul_of_nonneg_left hbnd.2 (by positivity)
    _≤T^ε*(C*(4096*(Real.log T)^12)*T^((a+b)/2+s+η/2)) := by gcongr
    _=_ := by rw [show T^ε*(C*(4096*(Real.log T)^12)*T^((a+b)/2+s+η/2))=
      (4096*C)*(Real.log T)^12*(T^ε*T^((a+b)/2+s+η/2)) by ring,hp]

end
end Sechstmoment
