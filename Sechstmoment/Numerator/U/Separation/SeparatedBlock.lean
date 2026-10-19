import Sechstmoment.Numerator.U.Separation.ActualGapPhase
import Sechstmoment.Numerator.U.Separation.PhaseCoefficientBounds
import Sechstmoment.Numerator.U.Separation.SeparatedPhaseRemainder

/-! The finite literal signed source block has a proved five-product
expansion and uniform remainder on its supported logarithmic near range. -/
namespace Sechstmoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 1000000

theorem rectangularMellinBlockWeight_norm_le_one {s : ℂ} (hs : s.re≤0) (x : ℝ) :
    ‖rectangularMellinBlockWeight s x‖≤1 := by
  by_cases hx : x∈Icc (1:ℝ) 2
  · have hxpos : 0<x := zero_lt_one.trans_le hx.1
    have hp : ‖(x:ℂ)^s‖≤1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
      calc
        _ ≤ x^(0:ℝ) := Real.rpow_le_rpow_of_exponent_le hx.1 hs
        _ = _ := Real.rpow_zero x
    unfold rectangularMellinBlockWeight
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (rectangularSmoothBlockWeight_nonneg x)]
    calc
      _ ≤ 1*1 := mul_le_mul (rectangularSmoothBlockWeight_le_one x) hp
        (norm_nonneg _) (by norm_num)
      _ = _ := one_mul 1
  · have hz : rectangularMellinBlockWeight s x=0 := by
      by_contra h
      exact hx ((rectangularMellinBlockWeight_complexWeight s).2 (subset_tsupport _ h))
    simp only [hz,norm_zero,zero_le_one]

theorem phaseBaseSmoothFactor_norm_le_one (q : QuadraticScales)
    (α : MomentShifts) (z : ℂ) (hs : ∀ i, (-(1/2+α i+z)).re≤0)
    (n : Fin 7 → ℕ) : ‖phaseBaseSmoothFactor q α z n‖≤1 := by
  unfold phaseBaseSmoothFactor
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (rectangularSmoothBlockWeight_nonneg _),norm_prod]
  calc
    _ ≤ 1*(∏ _j : Fin 4, (1:ℝ)) := by
      apply mul_le_mul (rectangularSmoothBlockWeight_le_one _) _
        (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (by norm_num)
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro j _
      exact rectangularMellinBlockWeight_norm_le_one (hs j) _
    _ = _ := by simp

def phaseSignedSourceBlock (positive : Bool) (q : QuadraticScales)
    (α : MomentShifts) (z : ℂ) (A β : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n∈quadraticIndexSet q, if signedQuadraticRelation positive n then
    (A (n 0)*β (n 1)*phaseBaseSmoothFactor q α z n)*
      (1+((rectangularGapSign positive*(n 6:ℝ)/((n 1:ℝ)*n 4*n 5):ℝ):ℂ))^(-(t:ℂ)*I) else 0

theorem phase_signed_source_block_finite_identity (positive : Bool) (q : QuadraticScales)
    (hB : 0<q.B) (hH : 0<q.H) (hN₁ : 0<q.N₁) (hN₂ : 0<q.N₂)
    (α : MomentShifts) (z : ℂ) (A β : ℕ → ℂ) (t : ℝ) (N : ℕ) :
    (∑ k∈Finset.range N, phaseSeparationScalar q (rectangularGapSign positive) t k*
      rectangularComplexQuadraticSum positive q A (phaseAdjustedBeta q β k) (phaseFiveWeights α z k))=
      ∑ n∈quadraticIndexSet q, if signedQuadraticRelation positive n then
        (A (n 0)*β (n 1)*phaseBaseSmoothFactor q α z n)*
          ∑ k∈Finset.range N, phaseBinomialCoefficient (-(t:ℂ)*I) k*
            ((rectangularGapSign positive*(n 6:ℝ)/((n 1:ℝ)*n 4*n 5):ℝ):ℂ)^k else 0 := by
  unfold rectangularComplexQuadraticSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have hp (j : Fin 7) : 0<n j := by
    have hj := (Fintype.mem_piFinset.mp hn) j
    exact lt_of_lt_of_le (by norm_num : 0<1) (Finset.mem_Icc.mp hj).1
  by_cases he : signedQuadraticRelation positive n
  · simp only [he,ite_true]
    simpa only [Finset.mul_sum] using phase_five_product_finite_identity q hB hH hN₁ hN₂ α z A β
      (rectangularGapSign positive) t n (hp 1) (hp 4) (hp 5) N
  · simp only [he,ite_false,mul_zero,Finset.sum_const_zero]

private theorem supported_ratio_bound (q : QuadraticScales)
    (hB : 0<q.B) (hH : 0<q.H) (hN₁ : 0<q.N₁) (hN₂ : 0<q.N₂)
    (α : MomentShifts) (z : ℂ) (A β : ℕ → ℂ)
    (hβ : ∀ b : ℕ, (b:ℝ)∉Icc q.B (2*q.B) → β b=0)
    (positive : Bool) (n : Fin 7 → ℕ)
    (hn : A (n 0)*β (n 1)*phaseBaseSmoothFactor q α z n≠0) :
    |rectangularGapSign positive*(n 6:ℝ)/((n 1:ℝ)*n 4*n 5)|≤2*q.H/(q.B*q.N₁*q.N₂) := by
  have hb0 : β (n 1)≠0 := by
    intro he
    exact hn (by simp only [he,mul_zero,zero_mul])
  have hb : (n 1:ℝ)∈Icc q.B (2*q.B) := by
    by_contra he
    exact hb0 (hβ _ he)
  have hw : phaseBaseSmoothFactor q α z n≠0 := by
    intro he
    exact hn (by simp only [he,mul_zero])
  have hh0 : rectangularSmoothBlockWeight ((n 6:ℝ)/q.H)≠0 := by
    intro he
    exact hw (by simp only [phaseBaseSmoothFactor,he,Complex.ofReal_zero,zero_mul])
  have hh := rectangularSmoothBlockWeight_tsupport (subset_tsupport _ hh0)
  have hp : ∀ j : Fin 4, rectangularActualMellinBlockWeight α z j
      (phaseQuadVariable n j/phaseQuadScale q j)≠0 := by
    have he : (∏ j : Fin 4, rectangularActualMellinBlockWeight α z j
        (phaseQuadVariable n j/phaseQuadScale q j))≠0 := by
      intro hz
      exact hw (by simp only [phaseBaseSmoothFactor,hz,mul_zero])
    exact fun j => (Finset.prod_ne_zero_iff.mp he) j (Finset.mem_univ j)
  have h₁ := (rectangularActualMellinBlockWeight_complexWeight α z 2).2 (subset_tsupport _ (hp 2))
  have h₂ := (rectangularActualMellinBlockWeight_complexWeight α z 3).2 (subset_tsupport _ (hp 3))
  change (n 4:ℝ)/q.N₁∈Icc 1 2 at h₁
  change (n 5:ℝ)/q.N₂∈Icc 1 2 at h₂
  have hn₁ : q.N₁≤(n 4:ℝ) := by
    have he := (le_div_iff₀ hN₁).mp h₁.1
    simpa only [one_mul] using he
  have hn₂ : q.N₂≤(n 5:ℝ) := by
    have he := (le_div_iff₀ hN₂).mp h₂.1
    simpa only [one_mul] using he
  have hgap : (n 6:ℝ)≤2*q.H := (div_le_iff₀ hH).mp hh.2
  have hd : 0<q.B*q.N₁*q.N₂ := by positivity
  have hbpos : 0<(n 1:ℝ) := hB.trans_le hb.1
  have hn₁pos : 0<(n 4:ℝ) := hN₁.trans_le hn₁
  have hn₂pos : 0<(n 5:ℝ) := hN₂.trans_le hn₂
  have hprod : q.B*q.N₁*q.N₂≤(n 1:ℝ)*n 4*n 5 := by
    gcongr
    exact hb.1
  have hsign : |rectangularGapSign positive|=1 := by
    cases positive <;> norm_num [rectangularGapSign]
  rw [abs_div,abs_mul,hsign,abs_of_nonneg (Nat.cast_nonneg _),one_mul,
    abs_of_pos (mul_pos (mul_pos hbpos hn₁pos) hn₂pos)]
  exact div_le_div₀ (by positivity) hgap hd hprod

theorem phase_signed_source_block_uniform_remainder {θ : ℝ} (hθ : 0≤θ) (M : ℝ) :
    ∃ L : ℝ, 0<L ∧ ∀ T : ℝ, Real.exp 1≤T →
      (⌈L*Real.log T⌉₊:ℝ)≤(L+1)*Real.log T ∧
      ∀ q : QuadraticScales, 0<q.B → 0<q.H → 0<q.N₁ → 0<q.N₂ →
      2*q.H/(q.B*q.N₁*q.N₂)≤1/4 →
      T*(2*q.H/(q.B*q.N₁*q.N₂))≤θ*Real.log T →
      ∀ α : MomentShifts, ∀ z : ℂ, ∀ A β : ℕ → ℂ,
      (∀ b : ℕ, (b:ℝ)∉Icc q.B (2*q.B) → β b=0) → ∀ t : ℝ, |t|≤2*T →
      ∀ positive : Bool,
      ‖phaseSignedSourceBlock positive q α z A β t-
        ∑ k∈Finset.range ⌈L*Real.log T⌉₊, phaseSeparationScalar q (rectangularGapSign positive) t k*
          rectangularComplexQuadraticSum positive q A (phaseAdjustedBeta q β k) (phaseFiveWeights α z k)‖≤
        (∑ n∈quadraticIndexSet q, ‖A (n 0)*β (n 1)*phaseBaseSmoothFactor q α z n‖)*T^(-M) := by
  obtain ⟨L,hL,hb⟩ := phase_five_product_uniform_remainder hθ M
  refine ⟨L,hL,?_⟩
  intro T hT
  have hTpos : 0<T := (Real.exp_pos 1).trans_le hT
  refine ⟨(hb T hT).1,?_⟩
  intro q hB hH hN₁ hN₂ hr4 hTr α z A β hβ t ht positive
  rw [phase_signed_source_block_finite_identity positive q hB hH hN₁ hN₂]
  unfold phaseSignedSourceBlock
  rw [← Finset.sum_sub_distrib,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  by_cases he : signedQuadraticRelation positive n
  · simp only [he,ite_true]
    by_cases hz : A (n 0)*β (n 1)*phaseBaseSmoothFactor q α z n=0
    · simp only [hz,zero_mul,sub_self,norm_zero,le_refl]
    · have hp (j : Fin 7) : 0<n j := by
        have hj := (Fintype.mem_piFinset.mp hn) j
        exact lt_of_lt_of_le (by norm_num : 0<1) (Finset.mem_Icc.mp hj).1
      have hx := supported_ratio_bound q hB hH hN₁ hN₂ α z A β hβ positive n hz
      have hm := (hb T hT).2 q hB hH hN₁ hN₂ α z A β (rectangularGapSign positive) t
        (2*q.H/(q.B*q.N₁*q.N₂)) ht (by positivity) hr4 hTr n (hp 1) (hp 4) (hp 5) hx
      rw [phase_five_product_finite_identity q hB hH hN₁ hN₂ α z A β
        (rectangularGapSign positive) t n (hp 1) (hp 4) (hp 5)] at hm
      exact hm
  · simp only [he,ite_false,sub_self,norm_zero]
    exact mul_nonneg (norm_nonneg _) (by positivity)

end
end Sechstmoment
