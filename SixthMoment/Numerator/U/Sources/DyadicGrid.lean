import SixthMoment.Numerator.U.Sources.Weights.ProfileLengths

namespace SixthMoment
open Complex Source Real Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def a03SourceScaleDepth (X : ℝ) : ℕ :=
  ⌊Real.log ((3/2:ℝ)*X)/Real.log (3/2:ℝ)⌋₊+1

def a03SourceScaleGrid (X : ℝ) : Finset ℕ := Finset.range (a03SourceScaleDepth X)

theorem a03SourceScaleGrid_mem_of_scale_le {X : ℝ} (_hX : 0<X) (k : ℕ)
    (hk : rectangularAFESmoothScale k≤X) : k∈a03SourceScaleGrid X := by
  have hq : 0<Real.log (3/2:ℝ) := Real.log_pos (by norm_num)
  have hp : (3/2:ℝ)^k≤(3/2)*X := by
    have h := (div_le_iff₀ (by norm_num : (0:ℝ)<3/2)).mp hk
    simpa only [mul_comm] using h
  have hl := Real.log_le_log (pow_pos (by norm_num : (0:ℝ)<3/2) k) hp
  rw [Real.log_pow] at hl
  have hd : (k:ℝ)≤Real.log ((3/2:ℝ)*X)/Real.log (3/2:ℝ) := (le_div_iff₀ hq).mpr hl
  have hf := Nat.lt_floor_add_one (Real.log ((3/2:ℝ)*X)/Real.log (3/2:ℝ))
  have hh : (k:ℝ)<(⌊Real.log ((3/2:ℝ)*X)/Real.log (3/2:ℝ)⌋₊+1:ℝ) := by linarith
  simp only [a03SourceScaleGrid,a03SourceScaleDepth,Finset.mem_range]
  exact_mod_cast hh

theorem a03_source_scalar_weight_eq (n k : ℕ) :
    rectangularSmoothBlockWeight ((n:ℝ)/rectangularAFESmoothScale k)=
      rectangularSmoothBlockWeight ((3/2:ℝ)*n/(3/2:ℝ)^k) := by
  congr 1
  unfold rectangularAFESmoothScale
  field_simp

theorem a03_source_scalar_weight_zero_outside {X : ℝ} (hX : 0<X)
    {n : ℕ} (hn : (n:ℝ)≤X) {k : ℕ} (hk : k∉a03SourceScaleGrid X) :
    rectangularSmoothBlockWeight ((n:ℝ)/rectangularAFESmoothScale k)=0 := by
  by_contra hw
  have hs : 0<rectangularAFESmoothScale k := by unfold rectangularAFESmoothScale; positivity
  have hi : 1<(n:ℝ)/rectangularAFESmoothScale k :=
    lt_of_not_ge (fun h => hw (rectangularSmoothBlockWeight_zero_le h))
  have hscale : rectangularAFESmoothScale k≤X := by
    have h := (lt_div_iff₀ hs).mp hi
    simpa only [one_mul] using h.le.trans hn
  exact hk (a03SourceScaleGrid_mem_of_scale_le hX k hscale)

theorem a03_source_scalar_finite_partition {X : ℝ} (hX : 0<X)
    {n : ℕ} (hn : 1≤n) (hcap : (n:ℝ)≤X) :
    (∑ k∈a03SourceScaleGrid X,
      rectangularSmoothBlockWeight ((n:ℝ)/rectangularAFESmoothScale k))=1 := by
  simp_rw [a03_source_scalar_weight_eq]
  have he := rectangularSmoothBlockWeight_tsum (by exact_mod_cast hn : (1:ℝ)≤n)
  rw [←he]
  exact (tsum_eq_sum (s := a03SourceScaleGrid X) (fun k hk => by
    rw [←a03_source_scalar_weight_eq]
    exact a03_source_scalar_weight_zero_outside hX hcap hk)).symm

theorem a03_source_amplifier_finite_partition {T : ℝ} (hT : 1<T) (a : ℝ)
    (f : ℝ→ℝ) {n : ℕ} (hn : 1≤n) (hcap : (n:ℝ)≤T^a) :
    (∑ k∈a03SourceScaleGrid (T^a),
      phaseActualAmplifierCoefficient T f (rectangularAFESmoothScale k) n)=
      (f (Real.log n/Real.log T):ℂ)*(n:ℂ)^(-(1/2:ℂ)) := by
  have he := a03_source_scalar_finite_partition
    (Real.rpow_pos_of_pos (zero_lt_one.trans hT) a) hn hcap
  unfold phaseActualAmplifierCoefficient
  rw [←Finset.sum_mul,←Finset.sum_mul,←Complex.ofReal_sum,he,Complex.ofReal_one,one_mul]

theorem a03_source_scale_grid_uniform_log_card {L r : ℝ} (hL : 1≤L) (hr : 0≤r) :
    ∃ C : ℝ, 0≤C ∧ ∀ T : ℝ, 1≤T →
      ((a03SourceScaleGrid (L*T^r)).card:ℝ)≤C*(1+Real.log T) := by
  have hq : 0<Real.log (3/2:ℝ) := Real.log_pos (by norm_num)
  let A := Real.log ((3/2:ℝ)*L)/Real.log (3/2:ℝ)
  let B := r/Real.log (3/2:ℝ)
  have hA : 0≤A := div_nonneg (Real.log_nonneg (by nlinarith)) hq.le
  have hB : 0≤B := div_nonneg hr hq.le
  refine ⟨A+1+B,by positivity,?_⟩
  intro T hT
  have ht : 0<T := zero_lt_one.trans_le hT
  have hlog : 0≤Real.log T := Real.log_nonneg hT
  have he : Real.log ((3/2:ℝ)*(L*T^r))/Real.log (3/2:ℝ)=A+B*Real.log T := by
    rw [show (3/2:ℝ)*(L*T^r)=((3/2)*L)*T^r by ring,
      Real.log_mul (by positivity) (Real.rpow_pos_of_pos ht r).ne',Real.log_rpow ht]
    dsimp [A,B]
    field_simp
  have hf := Nat.floor_le (show 0≤Real.log ((3/2:ℝ)*(L*T^r))/Real.log (3/2:ℝ) by rw [he]; positivity)
  simp only [a03SourceScaleGrid,Finset.card_range,a03SourceScaleDepth,Nat.cast_add,Nat.cast_one]
  rw [he] at hf ⊢
  nlinarith

def a03ActualSourceBlockGrid (A B H X : ℝ) : Finset ((Fin 3→ℕ)×(Fin 4→ℕ)) :=
  (Fintype.piFinset (fun j : Fin 3 => a03SourceScaleGrid (![A,B,H] j))).product
    (rectangularAFEProductScaleGrid X)

theorem a03_actual_source_block_grid_uniform_log_card {a b h η : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hh : 0≤h) (hη : 0<η) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop,
      ((a03ActualSourceBlockGrid (T^a) (T^b) (8*T^h) (T^(2+η))).card:ℝ)≤
        C*(1+Real.log T)^7 := by
  obtain ⟨A,hA,hac⟩ := a03_source_scale_grid_uniform_log_card (by norm_num : (1:ℝ)≤1) ha
  obtain ⟨B,hB,hbc⟩ := a03_source_scale_grid_uniform_log_card (by norm_num : (1:ℝ)≤1) hb
  obtain ⟨H,hH,hhc⟩ := a03_source_scale_grid_uniform_log_card (by norm_num : (1:ℝ)≤8) hh
  obtain ⟨D,hD,hdc⟩ := rectangular_AFE_product_scale_grid_uniform_log_card hη
  refine ⟨A*B*H*D,by positivity,?_⟩
  filter_upwards [hdc,eventually_ge_atTop (1:ℝ)] with T hdc hT
  have hac := hac T hT
  have hbc := hbc T hT
  have hhc := hhc T hT
  simp only [one_mul] at hac hbc
  have hc : ((a03ActualSourceBlockGrid (T^a) (T^b) (8*T^h) (T^(2+η))).card:ℝ)=
      ((a03SourceScaleGrid (T^a)).card:ℝ)*((a03SourceScaleGrid (T^b)).card:ℝ)*
        ((a03SourceScaleGrid (8*T^h)).card:ℝ)*((rectangularAFEProductScaleGrid (T^(2+η))).card:ℝ) := by
    unfold a03ActualSourceBlockGrid
    change ((Fintype.piFinset (fun j : Fin 3 => a03SourceScaleGrid (![T^a,T^b,8*T^h] j)) ×ˢ rectangularAFEProductScaleGrid (T^(2+η))).card:ℝ) = _
    rw [Finset.card_product,Fintype.card_piFinset]
    simp only [Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Fin.prod_univ_zero,mul_one,Nat.cast_mul]
    ring
  rw [hc]
  have hlog : 0≤1+Real.log T := by linarith [Real.log_nonneg hT]
  calc
    _≤(A*(1+Real.log T))*(B*(1+Real.log T))*(H*(1+Real.log T))*(D*(1+Real.log T)^4) := by gcongr
    _=_ := by ring

end
end SixthMoment
