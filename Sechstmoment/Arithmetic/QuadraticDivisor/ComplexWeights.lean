import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic
import Mathlib.Topology.Algebra.ConstMulAction
import Sechstmoment.Arithmetic.QuadraticDivisor.Estimates.SourceAdapter


namespace Sechstmoment

set_option maxHeartbeats 2000000

open Complex Source MeasureTheory Set
open scoped BigOperators Topology
open Classical

noncomputable section

def RectangularComplexWeight (W : ℝ → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) W ∧ tsupport W ⊆ Icc 1 2

def rectangularRealComponent (W : Fin 5 → ℝ → ℂ) (c : Fin 5 → Bool)
    (i : Fin 5) (x : ℝ) : ℝ := if c i then (W i x).im else (W i x).re

def rectangularComponentPhase (c : Fin 5 → Bool) : ℂ :=
  ∏ i, if c i then I else 1

def rectangularWeightArguments (q : QuadraticScales) (n : Fin 7 → ℕ) : Fin 5 → ℝ :=
  ![n 6/q.H, n 2/q.M₁, n 3/q.M₂, n 4/q.N₁, n 5/q.N₂]

def rectangularZeroArguments (q : QuadraticScales) (n : Fin 5 → ℕ) (x : ℝ) : Fin 5 → ℝ :=
  let d : ℝ := Nat.gcd (n 0*n 2) (n 1*n 3)
  ![d*n 4/q.H, n 2/q.M₁, n 1*n 3*x/(d*q.M₂),
    n 3/q.N₁, n 0*n 2*x/(d*q.N₂)]

def rectangularComplexQuadraticSum (positive : Bool) (q : QuadraticScales)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℂ) : ℂ :=
  ∑ n ∈ quadraticIndexSet q, if signedQuadraticRelation positive n then
    α (n 0)*β (n 1)*∏ i, W i (rectangularWeightArguments q n i) else 0

def rectangularComplexZeroMode (q : QuadraticScales) (α β : ℕ → ℂ)
    (W : Fin 5 → ℝ → ℂ) : ℂ :=
  ∑ n ∈ quadraticMainIndexSet q, α (n 0)*β (n 1)*
    ∫ x : ℝ in Ioi 0, ∏ i, W i (rectangularZeroArguments q n x i)

def rectangularComplexDiscrepancy (positive : Bool) (q : QuadraticScales)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℂ) : ℂ :=
  rectangularComplexQuadraticSum positive q α β W - rectangularComplexZeroMode q α β W

theorem rectangular_complex_product_expand (W : Fin 5 → ℝ → ℂ) (x : Fin 5 → ℝ) :
    (∏ i, W i (x i)) = ∑ c : Fin 5 → Bool, rectangularComponentPhase c*
      ∏ i, (rectangularRealComponent W c i (x i) : ℂ) := by
  calc
    _ = ∏ i, ∑ b : Bool, (if b then I else 1)*
        ((if b then (W i (x i)).im else (W i (x i)).re : ℝ) : ℂ) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [Bool.false_eq_true, ite_false, ite_true, one_mul, Fintype.sum_bool]
      simpa only [add_comm, mul_comm] using (Complex.re_add_im (W i (x i))).symm
    _ = ∑ c : Fin 5 → Bool, ∏ i, (if c i then I else 1)*
        ((if c i then (W i (x i)).im else (W i (x i)).re : ℝ) : ℂ) :=
      Fintype.prod_sum _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.prod_mul_distrib]
      rfl

theorem rectangular_component_phase_norm (c : Fin 5 → Bool) :
    ‖rectangularComponentPhase c‖ = 1 := by
  simp only [rectangularComponentPhase, norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  cases c i <;> simp

theorem rectangular_component_smooth (W : Fin 5 → ℝ → ℂ)
    (hW : ∀ i, RectangularComplexWeight (W i)) (c : Fin 5 → Bool) (i : Fin 5) :
    SmoothDyadicWeight (rectangularRealComponent W c i) := by
  unfold rectangularRealComponent
  split
  · refine ⟨Complex.imCLM.contDiff.comp (hW i).1, ?_⟩
    apply Set.Subset.trans _ (hW i).2
    exact tsupport_comp_subset (g := Complex.im) (by simp) (W i)
  · refine ⟨Complex.reCLM.contDiff.comp (hW i).1, ?_⟩
    apply Set.Subset.trans _ (hW i).2
    exact tsupport_comp_subset (g := Complex.re) (by simp) (W i)

theorem rectangular_component_derivative (W : Fin 5 → ℝ → ℂ)
    (hW : ∀ i, RectangularComplexWeight (W i)) (c : Fin 5 → Bool)
    (j : ℕ) (i : Fin 5) (x : ℝ) :
    iteratedDeriv j (rectangularRealComponent W c i) x =
      if c i then (iteratedDeriv j (W i) x).im else (iteratedDeriv j (W i) x).re := by
  have hp (L : ℂ →L[ℝ] ℝ) : iteratedDeriv j (L ∘ W i) x = L (iteratedDeriv j (W i) x) := by
    rw [iteratedDeriv_eq_iteratedFDeriv,
      L.iteratedFDeriv_comp_left (hW i).1.contDiffAt (by simp)]
    rfl
  unfold rectangularRealComponent
  split
  · exact hp Complex.imCLM
  · exact hp Complex.reCLM

theorem rectangular_component_derivative_norm_le (W : Fin 5 → ℝ → ℂ)
    (hW : ∀ i, RectangularComplexWeight (W i)) (c : Fin 5 → Bool)
    (j : ℕ) (i : Fin 5) (x : ℝ) :
    ‖iteratedDeriv j (rectangularRealComponent W c i) x‖ ≤ ‖iteratedDeriv j (W i) x‖ := by
  rw [rectangular_component_derivative W hW c j i x]
  cases c i <;> simp only [Bool.false_eq_true, ite_false, ite_true, Real.norm_eq_abs]
  · exact Complex.abs_re_le_norm _
  · exact Complex.abs_im_le_norm _

theorem rectangular_component_admissible {ε δ K : ℝ} (bounds : ℕ → ℝ)
    (q : QuadraticScales) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℂ)
    (hshape : QuadraticAdmissible ε δ K bounds q α β (fun i x => (W i x).re))
    (hW : ∀ i, RectangularComplexWeight (W i))
    (hd : ∀ j i x, ‖iteratedDeriv j (W i) x‖ ≤ bounds j*q.mass^ε)
    (c : Fin 5 → Bool) : QuadraticAdmissible ε δ K bounds q α β
      (rectangularRealComponent W c) := by
  rcases hshape with ⟨hs, hm, hn, hh, hδ, hmn, hnm, horient, hαs, hβs, hα, hβ, _, _⟩
  refine ⟨hs, hm, hn, hh, hδ, hmn, hnm, horient, hαs, hβs, hα, hβ,
    rectangular_component_smooth W hW c, ?_⟩
  intro j i x
  exact (rectangular_component_derivative_norm_le W hW c j i x).trans (hd j i x)

theorem rectangular_component_zero_integrable (q : QuadraticScales)
    (hq : 0 < q.M₂) (n : Fin 5 → ℕ) (hn : ∀ j, 1 ≤ n j)
    (W : Fin 5 → ℝ → ℂ) (hW : ∀ i, RectangularComplexWeight (W i))
    (c : Fin 5 → Bool) : Integrable (fun x : ℝ =>
      ∏ i, (rectangularRealComponent W c i (rectangularZeroArguments q n x i) : ℂ)) := by
  let d : ℝ := Nat.gcd (n 0*n 2) (n 1*n 3)
  have hd : 0 < d := by
    change (0 : ℝ) < (Nat.gcd (n 0*n 2) (n 1*n 3) : ℝ)
    exact_mod_cast Nat.gcd_pos_of_pos_left (n 1*n 3)
      (Nat.mul_pos (lt_of_lt_of_le (by norm_num) (hn 0)) (lt_of_lt_of_le (by norm_num) (hn 2)))
  have hc : Continuous (fun x : ℝ =>
      ∏ i, (rectangularRealComponent W c i (rectangularZeroArguments q n x i) : ℂ)) := by
    apply continuous_finsetProd
    intro i hi
    apply Complex.continuous_ofReal.comp
    apply ((rectangular_component_smooth W hW c i).1.continuous).comp
    fin_cases i <;> simp only [rectangularZeroArguments] <;> fun_prop
  have hcomp : HasCompactSupport (rectangularRealComponent W c 2) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (rectangular_component_smooth W hW c 2).2
  have hl : (n 1:ℝ)*(n 3:ℝ)/(d*q.M₂) ≠ 0 := by
    have h₁ : (0:ℝ) < n 1 := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 1) (hn 1)
    have h₃ : (0:ℝ) < n 3 := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 1) (hn 3)
    positivity
  have hscaled : HasCompactSupport (fun x : ℝ =>
      (rectangularRealComponent W c 2 ((n 1:ℝ)*(n 3:ℝ)*x/(d*q.M₂)) : ℂ)) := by
    have hs := hcomp.comp_smul hl
    have hs' : HasCompactSupport (fun x : ℝ =>
        rectangularRealComponent W c 2 ((n 1:ℝ)*(n 3:ℝ)*x/(d*q.M₂))) := by
      convert hs using 1
      ext x
      simp only [smul_eq_mul]
      congr 1
      ring
    exact hs'.comp_left (show Complex.ofReal 0 = 0 from rfl)
  have hsupport : HasCompactSupport (fun x : ℝ =>
      ∏ i, (rectangularRealComponent W c i (rectangularZeroArguments q n x i) : ℂ)) := by
    convert hscaled.mul_right (f' := fun x : ℝ =>
      (rectangularRealComponent W c 0 (rectangularZeroArguments q n x 0) : ℂ)*
      (rectangularRealComponent W c 1 (rectangularZeroArguments q n x 1) : ℂ)*
      (rectangularRealComponent W c 3 (rectangularZeroArguments q n x 3) : ℂ)*
      (rectangularRealComponent W c 4 (rectangularZeroArguments q n x 4) : ℂ)) using 1
    ext x
    simp [rectangularZeroArguments, d, Fin.prod_univ_five]
    ring
  exact hc.integrable_of_hasCompactSupport hsupport

theorem rectangular_real_zero_summand_product (q : QuadraticScales)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (n : Fin 5 → ℕ) :
    quadraticZeroModeSummand q α β W n = α (n 0)*β (n 1)*
      ∫ x : ℝ in Ioi 0, ∏ i, (W i (rectangularZeroArguments q n x i) : ℂ) := by
  have hp : (fun x : ℝ => ∏ i, (W i (rectangularZeroArguments q n x i) : ℂ)) =
      fun x : ℝ => (W 0 (rectangularZeroArguments q n x 0) : ℂ)*
        (W 1 (rectangularZeroArguments q n x 1) : ℂ)*
        (W 3 (rectangularZeroArguments q n x 3) : ℂ)*
        ((W 2 (rectangularZeroArguments q n x 2) : ℂ)*
          (W 4 (rectangularZeroArguments q n x 4) : ℂ)) := by
    ext x
    rw [Fin.prod_univ_five]
    ring
  rw [hp]
  dsimp [rectangularZeroArguments]
  rw [integral_const_mul]
  dsimp [quadraticZeroModeSummand]
  ring

theorem rectangular_complex_quadratic_sum_expand (positive : Bool) (q : QuadraticScales)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℂ) :
    rectangularComplexQuadraticSum positive q α β W =
      ∑ c : Fin 5 → Bool, rectangularComponentPhase c*
        signedQuadraticSum positive q α β (rectangularRealComponent W c) := by
  unfold rectangularComplexQuadraticSum signedQuadraticSum
  calc
    _ = ∑ n ∈ quadraticIndexSet q, ∑ c : Fin 5 → Bool,
        rectangularComponentPhase c*
          (if signedQuadraticRelation positive n then
            quadraticSummand q α β (rectangularRealComponent W c) n else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases h : signedQuadraticRelation positive n
      · simp only [h, ite_true]
        rw [rectangular_complex_product_expand, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c hc
        simp [quadraticSummand, rectangularWeightArguments, Fin.prod_univ_five]
        ring
      · simp [h]
    _ = _ := ?_
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mul_sum]

theorem rectangular_complex_zero_mode_expand (q : QuadraticScales) (hq : 0 < q.M₂)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℂ)
    (hW : ∀ i, RectangularComplexWeight (W i)) :
    rectangularComplexZeroMode q α β W =
      ∑ c : Fin 5 → Bool, rectangularComponentPhase c*
        quadraticZeroMode q α β (rectangularRealComponent W c) := by
  unfold rectangularComplexZeroMode quadraticZeroMode
  calc
    _ = ∑ n ∈ quadraticMainIndexSet q, ∑ c : Fin 5 → Bool,
        rectangularComponentPhase c*quadraticZeroModeSummand q α β
          (rectangularRealComponent W c) n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnn : ∀ j, 1 ≤ n j := by
        intro j
        exact (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hn j)).1
      have hp : (fun x : ℝ => ∏ i, W i (rectangularZeroArguments q n x i)) =
          fun x : ℝ => ∑ c : Fin 5 → Bool, rectangularComponentPhase c*
            ∏ i, (rectangularRealComponent W c i (rectangularZeroArguments q n x i) : ℂ) := by
        ext x
        exact rectangular_complex_product_expand W (rectangularZeroArguments q n x)
      rw [hp, integral_finsetSum]
      · simp_rw [integral_const_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c hc
        rw [rectangular_real_zero_summand_product]
        ring
      · intro c hc
        exact ((rectangular_component_zero_integrable q hq n hnn W hW c).integrableOn).const_mul _
    _ = _ := ?_
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mul_sum]

theorem rectangular_complex_discrepancy_expand (positive : Bool) (q : QuadraticScales)
    (hq : 0 < q.M₂) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℂ)
    (hW : ∀ i, RectangularComplexWeight (W i)) :
    rectangularComplexDiscrepancy positive q α β W =
      ∑ c : Fin 5 → Bool, rectangularComponentPhase c*
        signedQuadraticDiscrepancy positive q α β (rectangularRealComponent W c) := by
  rw [rectangularComplexDiscrepancy, rectangular_complex_quadratic_sum_expand,
    rectangular_complex_zero_mode_expand q hq α β W hW, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  rw [signedQuadraticDiscrepancy, mul_sub]

theorem rectangular_BBLRv1_complex_weights (hinput : SeparatedQuadraticInput)
    {ε δ K : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hK : 1 ≤ K)
    (bounds : ℕ → ℝ) (hbounds : ∀ j, 0 ≤ bounds j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : QuadraticScales) (α β : ℕ → ℂ)
      (W : Fin 5 → ℝ → ℂ),
      QuadraticAdmissible (DivisorProof.inputExponent ε δ) δ K bounds q α β (fun i x => (W i x).re) →
      (∀ i, RectangularComplexWeight (W i)) →
      (∀ j i x, ‖iteratedDeriv j (W i) x‖ ≤ bounds j*q.mass^(DivisorProof.inputExponent ε δ)) →
      ∀ positive : Bool, ‖rectangularComplexDiscrepancy positive q α β W‖ ≤
        C*((q.mass*q.H^2)^ε*orientedQuadraticMajorant q+q.mass^ε*q.H^2) := by
  obtain ⟨C, hC, hsource⟩ := hinput ε hε δ hδ K hK bounds hbounds
  refine ⟨32*C, by positivity, ?_⟩
  intro q α β W hshape hW hd positive
  have hq : 0 < q.M₂ := by
    have hs := hshape.1 3
    norm_num [QuadraticScales.size] at hs
    linarith
  rw [rectangular_complex_discrepancy_expand positive q hq α β W hW]
  calc
    _ ≤ ∑ c : Fin 5 → Bool, ‖rectangularComponentPhase c*
        signedQuadraticDiscrepancy positive q α β (rectangularRealComponent W c)‖ := norm_sum_le _ _
    _ ≤ ∑ _c : Fin 5 → Bool,
        C*((q.mass*q.H^2)^ε*orientedQuadraticMajorant q+q.mass^ε*q.H^2) := by
      apply Finset.sum_le_sum
      intro c hc
      rw [norm_mul, rectangular_component_phase_norm, one_mul]
      exact hsource q α β (rectangularRealComponent W c)
        (rectangular_component_admissible bounds q α β W hshape hW hd c) positive
    _ = _ := by simp; ring

theorem rectangular_BBLRv1_complex_actual_transfer (hinput : SeparatedQuadraticInput)
    {ε δ K : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hK : 1 ≤ K)
    (bounds : ℕ → ℝ) (hbounds : ∀ j, 0 ≤ bounds j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : QuadraticScales) (α β : ℕ → ℂ)
      (W : Fin 5 → ℝ → ℂ),
      QuadraticAdmissible (DivisorProof.inputExponent ε δ) δ K bounds q α β (fun i x => (W i x).re) →
      (∀ i, RectangularComplexWeight (W i)) →
      (∀ j i x, ‖iteratedDeriv j (W i) x‖ ≤ bounds j*q.mass^(DivisorProof.inputExponent ε δ)) →
      ∀ positive : Bool, ∀ X D T r L : ℝ,
      0 < X → 0 ≤ D → 0 < T → 0 < L →
      q.mass = q.A*q.B*X^2 → q.mass ≤ D*T^r → q.mass*q.H^2 ≤ D*T^r →
      q.H ≤ L*(q.A*q.B)^(1/2:ℝ)*X/T →
      ‖((T/((q.A*q.B)^(1/2:ℝ)*X) : ℝ) : ℂ)*
        rectangularComplexDiscrepancy positive q α β W‖ ≤
        C*(D^ε*T^(r*ε))*
          (2*(L^(1/2:ℝ)*T^(1/2:ℝ)*(q.A*q.B)+
            L^(3/4:ℝ)*T^(1/4:ℝ)*(q.A*q.B)^(3/8:ℝ)*
              max q.A q.B^(1/4:ℝ)*X^(1/2:ℝ))+
            L^2*(q.A*q.B)^(1/2:ℝ)*X/T) := by
  obtain ⟨C, hC, hsource⟩ := hinput ε hε δ hδ K hK bounds hbounds
  refine ⟨32*C, by positivity, ?_⟩
  intro q α β W hshape hW hd positive X D T r L hX hD hT hL hmass hgrowth hgrowthH hH0
  have hp : ∀ j, 0 < q.size j := fun j => lt_of_lt_of_le (by norm_num) (hshape.1 j)
  have hA : 0 < q.A := by simpa [QuadraticScales.size] using hp 0
  have hB : 0 < q.B := by simpa [QuadraticScales.size] using hp 1
  have hM : 0 < q.M₂ := by simpa [QuadraticScales.size] using hp 3
  have hH : 0 < q.H := by simpa [QuadraticScales.size] using hp 6
  rw [rectangular_complex_discrepancy_expand positive q hM α β W hW, Finset.mul_sum]
  calc
    _ ≤ ∑ c : Fin 5 → Bool,
        ‖((T/((q.A*q.B)^(1/2:ℝ)*X) : ℝ) : ℂ)*
          (rectangularComponentPhase c*signedQuadraticDiscrepancy positive q α β
            (rectangularRealComponent W c))‖ := norm_sum_le _ _
    _ ≤ ∑ _c : Fin 5 → Bool, C*(D^ε*T^(r*ε))*
        (2*(L^(1/2:ℝ)*T^(1/2:ℝ)*(q.A*q.B)+
          L^(3/4:ℝ)*T^(1/4:ℝ)*(q.A*q.B)^(3/8:ℝ)*
            max q.A q.B^(1/4:ℝ)*X^(1/2:ℝ))+
          L^2*(q.A*q.B)^(1/2:ℝ)*X/T) := by
      apply Finset.sum_le_sum
      intro c hc
      rw [← mul_left_comm, norm_mul, rectangular_component_phase_norm, one_mul]
      exact rectangular_actual_signed_transfer positive q α β (rectangularRealComponent W c)
        hA hB hX hH hC hD hT hε.le hL hmass hgrowth hgrowthH hH0
          (hsource q α β (rectangularRealComponent W c)
            (rectangular_component_admissible bounds q α β W hshape hW hd c) positive)
    _ = _ := by simp; ring

end
end Sechstmoment
