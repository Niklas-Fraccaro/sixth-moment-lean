import Sechstmoment.Numerator.U.Separation.TimeFarFiniteBudget
import Sechstmoment.Numerator.U.Sources.ErrorAggregate

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03SourceAmplifierGapGrid (T a b s u : ℝ) : Finset (Fin 3→ℕ) :=
  Fintype.piFinset (fun j : Fin 3 => a03SourceScaleGrid
    (![T^a,T^b,8*T^((a+b)/2+s+u/2)] j))

def a03SourceAmplifierGapWeight (p q h : ℕ) (j : Fin 3→ℕ) : ℝ :=
  ∏ r : Fin 3, rectangularSmoothBlockWeight
    (((![p,q,h] r : ℕ):ℝ)/rectangularAFESmoothScale (j r))

def a03ActualSourceNearPartition (T a b s u : ℝ) (f g : ℝ→ℝ)
    (k : Fin 4→ℕ) (p q h : ℕ) : ℝ :=
  ∑ j∈a03SourceAmplifierGapGrid T a b s u,
    if phaseActualActiveNearBlock T (rectangularAFESmoothScale (j 0))
      (rectangularAFESmoothScale (j 1)) (rectangularAFESmoothScale (j 2)) (T^(s-1)) f g k then
        a03SourceAmplifierGapWeight p q h j else 0

theorem a03_source_scalar_partial_weight_bounds (X : ℝ) {n : ℕ} (hn : 1≤n) :
    0≤(∑ k∈a03SourceScaleGrid X,rectangularSmoothBlockWeight ((n:ℝ)/rectangularAFESmoothScale k)) ∧
    (∑ k∈a03SourceScaleGrid X,rectangularSmoothBlockWeight ((n:ℝ)/rectangularAFESmoothScale k))≤1 := by
  refine ⟨Finset.sum_nonneg (fun _ _ => rectangularSmoothBlockWeight_nonneg _),?_⟩
  simp_rw [a03_source_scalar_weight_eq]
  have hs := (rectangularSmoothBlockWeight_summable (n:ℝ)).sum_le_tsum
    (a03SourceScaleGrid X) (fun k _ => rectangularSmoothBlockWeight_nonneg _)
  simpa only [rectangularSmoothBlockWeight_tsum (by exact_mod_cast hn : (1:ℝ)≤n)] using hs

theorem a03SourceAmplifierGapWeight_nonneg (p q h : ℕ) (j : Fin 3→ℕ) :
    0≤a03SourceAmplifierGapWeight p q h j :=
  Finset.prod_nonneg (fun _ _ => rectangularSmoothBlockWeight_nonneg _)

theorem a03_source_amplifier_gap_weight_sum (T a b s u : ℝ) (p q h : ℕ) :
    (∑ j∈a03SourceAmplifierGapGrid T a b s u,a03SourceAmplifierGapWeight p q h j)=
      (∑ r∈a03SourceScaleGrid (T^a),rectangularSmoothBlockWeight ((p:ℝ)/rectangularAFESmoothScale r))*
      (∑ r∈a03SourceScaleGrid (T^b),rectangularSmoothBlockWeight ((q:ℝ)/rectangularAFESmoothScale r))*
      (∑ r∈a03SourceScaleGrid (8*T^((a+b)/2+s+u/2)),rectangularSmoothBlockWeight ((h:ℝ)/rectangularAFESmoothScale r)) := by
  unfold a03SourceAmplifierGapGrid a03SourceAmplifierGapWeight
  have he := Finset.prod_univ_sum
    (fun j : Fin 3 => a03SourceScaleGrid (![T^a,T^b,8*T^((a+b)/2+s+u/2)] j))
    (fun r (k : ℕ) => rectangularSmoothBlockWeight (((![p,q,h] r:ℕ):ℝ)/rectangularAFESmoothScale k))
  simpa only [Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.prod_univ_zero,mul_one,mul_assoc] using he.symm

theorem a03ActualSourceNearPartition_bounds (T a b s u : ℝ) (f g : ℝ→ℝ)
    (k : Fin 4→ℕ) {p q h : ℕ} (hp : 1≤p) (hq : 1≤q) (hh : 1≤h) :
    0≤a03ActualSourceNearPartition T a b s u f g k p q h ∧
      a03ActualSourceNearPartition T a b s u f g k p q h≤1 := by
  unfold a03ActualSourceNearPartition
  refine ⟨Finset.sum_nonneg (fun j _ => by split_ifs; exact a03SourceAmplifierGapWeight_nonneg p q h j; exact le_rfl),?_⟩
  calc
    _≤∑ j∈a03SourceAmplifierGapGrid T a b s u,a03SourceAmplifierGapWeight p q h j := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs
      · exact le_rfl
      · exact a03SourceAmplifierGapWeight_nonneg p q h j
    _≤1 := by
      rw [a03_source_amplifier_gap_weight_sum]
      have hp' := a03_source_scalar_partial_weight_bounds (T^a) hp
      have hq' := a03_source_scalar_partial_weight_bounds (T^b) hq
      have hh' := a03_source_scalar_partial_weight_bounds (8*T^((a+b)/2+s+u/2)) hh
      nlinarith [mul_nonneg hp'.1 hq'.1,mul_le_mul hp'.2 hq'.2 hq'.1 zero_le_one]

theorem phaseActualAmplifierCoefficient_ne_zero_of_factors (T A : ℝ) (f : ℝ→ℝ)
    {p : ℕ} (hp : 0<p) (hw : rectangularSmoothBlockWeight ((p:ℝ)/A)≠0)
    (hf : f (Real.log (p:ℝ)/Real.log T)≠0) : phaseActualAmplifierCoefficient T f A p≠0 := by
  unfold phaseActualAmplifierCoefficient
  apply mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hw) (Complex.ofReal_ne_zero.mpr hf))
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp.ne'))

theorem a03_actual_near_tuple_gap_cap {T a b s u : ℝ} (hT : 0<T)
    (k n : Fin 4→ℕ) (hk : k∈rectangularAFEProductScaleGrid (T^(2+u)))
    (hw : rectangularAFESmoothWeight k n≠0) {p q h : ℕ}
    (hpCap : (p:ℝ)≤T^a) (hqCap : (q:ℝ)≤T^b)
    (hnear : rectangularNearRelation (T^(s-1)) (rectangularAFESourceTuple p q n h)) :
    (h:ℝ)≤8*T^((a+b)/2+s+u/2) := by
  have hpq : (p:ℝ)*q≤T^(a+b) := by
    have h := mul_le_mul hpCap hqCap (Nat.cast_nonneg q) (Real.rpow_nonneg hT.le a)
    rwa [←Real.rpow_add hT] at h
  have hquad := rectangular_AFE_smooth_grid_integer_product_le k n hk hw
  let mass : ℝ := (p:ℝ)*q*(positiveQuadProduct n:ℝ)
  have hmass : mass≤16*T^(a+b+2+u) := by
    calc
      _≤T^(a+b)*(16*T^(2+u)) := mul_le_mul hpq hquad (Nat.cast_nonneg _) (Real.rpow_nonneg hT.le _)
      _=16*T^(a+b+2+u) := by simp only [Real.rpow_add hT]; ring
  have hroot : Real.sqrt mass≤4*T^((a+b+2+u)/2) := by
    calc
      _≤Real.sqrt (16*T^(a+b+2+u)) := Real.sqrt_le_sqrt hmass
      _=4*T^((a+b+2+u)/2) := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤16),show Real.sqrt (16:ℝ)=4 by norm_num,
          Real.sqrt_eq_rpow,←Real.rpow_mul hT.le]
        congr 2
        ring
  have hn : (h:ℝ)≤T^(s-1)*Real.sqrt mass := by
    simpa [rectangularNearRelation,rectangularAFESourceTuple,mass,positiveQuadProduct,Nat.cast_mul,mul_assoc] using hnear
  calc
    _≤T^(s-1)*Real.sqrt mass := hn
    _≤T^(s-1)*(4*T^((a+b+2+u)/2)) := mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg hT.le _)
    _=4*T^((a+b)/2+s+u/2) := by
      rw [show (a+b)/2+s+u/2=(s-1)+(a+b+2+u)/2 by ring,Real.rpow_add hT]
      ring
    _≤_ := by nlinarith [Real.rpow_nonneg hT.le ((a+b)/2+s+u/2)]

theorem a03ActualSourceNearPartition_eq_one {T a b s u : ℝ} (hT : 0<T)
    (f g : ℝ→ℝ) (k n : Fin 4→ℕ) {p q h : ℕ}
    (hp : 1≤p) (hq : 1≤q) (hh : 1≤h)
    (hpCap : (p:ℝ)≤T^a) (hqCap : (q:ℝ)≤T^b)
    (hhCap : (h:ℝ)≤8*T^((a+b)/2+s+u/2))
    (hf : f (Real.log (p:ℝ)/Real.log T)≠0) (hg : g (Real.log (q:ℝ)/Real.log T)≠0)
    (hw : rectangularAFESmoothWeight k n≠0) (positive : Bool)
    (hrel : signedQuadraticRelation positive (rectangularAFESourceTuple p q n h))
    (hnear : rectangularNearRelation (T^(s-1)) (rectangularAFESourceTuple p q n h)) :
    a03ActualSourceNearPartition T a b s u f g k p q h=1 := by
  have hsum : a03ActualSourceNearPartition T a b s u f g k p q h=
      ∑ j∈a03SourceAmplifierGapGrid T a b s u,a03SourceAmplifierGapWeight p q h j := by
    unfold a03ActualSourceNearPartition
    apply Finset.sum_congr rfl
    intro j _
    by_cases hweight : a03SourceAmplifierGapWeight p q h j=0
    · simp [hweight]
    · have hweights := Finset.prod_ne_zero_iff.mp hweight
      have hWp : rectangularSmoothBlockWeight ((p:ℝ)/rectangularAFESmoothScale (j 0))≠0 := by
        simpa [a03SourceAmplifierGapWeight] using hweights 0 (Finset.mem_univ _)
      have hWq : rectangularSmoothBlockWeight ((q:ℝ)/rectangularAFESmoothScale (j 1))≠0 := by
        simpa [a03SourceAmplifierGapWeight] using hweights 1 (Finset.mem_univ _)
      have hWh : rectangularSmoothBlockWeight ((h:ℝ)/rectangularAFESmoothScale (j 2))≠0 := by
        simpa [a03SourceAmplifierGapWeight] using hweights 2 (Finset.mem_univ _)
      have hactive : phaseActualActiveNearBlock T (rectangularAFESmoothScale (j 0))
          (rectangularAFESmoothScale (j 1)) (rectangularAFESmoothScale (j 2)) (T^(s-1)) f g k :=
        ⟨p,q,h,n,positive,
          phaseActualAmplifierCoefficient_ne_zero_of_factors T _ f (by omega) hWp hf,
          phaseActualAmplifierCoefficient_ne_zero_of_factors T _ g (by omega) hWq hg,
          hw,hWh,hrel,hnear⟩
      simp only [hactive,ite_true]
  rw [hsum,a03_source_amplifier_gap_weight_sum,
    a03_source_scalar_finite_partition (Real.rpow_pos_of_pos hT a) hp hpCap,
    a03_source_scalar_finite_partition (Real.rpow_pos_of_pos hT b) hq hqCap,
    a03_source_scalar_finite_partition (by positivity : 0<8*T^((a+b)/2+s+u/2)) hh hhCap]
  norm_num

end
end Sechstmoment
