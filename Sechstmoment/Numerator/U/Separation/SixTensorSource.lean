import Sechstmoment.Numerator.U.Separation.Tensor.SixBeta
import Sechstmoment.Numerator.U.Separation.Tensor.SixSeparation
import Sechstmoment.Numerator.U.Sources.Weights.KernelIntegral

/-! Exact finite signed-source reconstruction of a genuine six-variable
Schwartz tensor. No assertion that the actual AFE kernels already satisfy
uniform Schwartz seminorm bounds is made in this bridge. -/
namespace Sechstmoment
open Complex Real Source Set MeasureTheory
open scoped BigOperators FourierTransform RealInnerProductSpace Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def a03SixSourceArguments (q : QuadraticScales) (n : Fin 7 → ℕ) : Fin 6 → ℝ :=
  Fin.cons ((n 1 : ℝ)/q.B) (rectangularWeightArguments q n)

theorem a03SixTensorExponent_continuous (j : Fin 6) :
    Continuous (fun ν : A03SixTensorSpace => a03SixTensorExponent ν j) := by
  unfold a03SixTensorExponent
  fun_prop

theorem a03SixTensorWeight_measurable (a : A03SixTensorSpace → ℝ) (ha : Measurable a)
    (j : Fin 5) (x : ℝ) :
    Measurable (fun ν => a03SixTensorWeight a ν j x) := by
  by_cases hx : x=0
  · subst x
    have hw : rectangularSmoothBlockWeight 0=0 :=
      rectangularSmoothBlockWeight_zero_le (by norm_num)
    simp only [a03SixTensorWeight,rectangularMellinBlockWeight,hw,Complex.ofReal_zero,
      zero_mul,mul_zero]
    exact measurable_const
  · have hc : Continuous (fun ν : A03SixTensorSpace =>
        (x : ℂ)^a03SixTensorExponent ν j.succ) :=
      (a03SixTensorExponent_continuous j.succ).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hx))
    exact (Complex.measurable_ofReal.comp ha).mul (measurable_const.mul hc.measurable)

theorem a03SixTensorBeta_measurable {B : ℝ} (hB : 0<B) (β : ℕ → ℂ)
    (hβ : ∀ n : ℕ, (n : ℝ)∉Icc B (2*B) → β n=0) (n : ℕ) :
    Measurable (fun ν => a03SixTensorBeta ν B β n) := by
  by_cases hn : n=0
  · subst n
    have hb : β 0=0 := hβ 0 (by simp only [Nat.cast_zero,mem_Icc]; intro h; linarith)
    simp only [a03SixTensorBeta,hb,zero_mul]
    exact measurable_const
  · have hn0 : 0<(n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hx : (((n : ℝ)/B : ℝ) : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (div_pos hn0 hB).ne'
    have hc : Continuous (fun ν : A03SixTensorSpace =>
        (((n : ℝ)/B : ℝ) : ℂ)^a03SixTensorExponent ν 0) :=
      (a03SixTensorExponent_continuous 0).const_cpow (Or.inl hx)
    exact (continuous_const.mul hc).measurable

theorem a03SixTensor_character_product_integrable
    (c : A03SixTensorSpace → ℂ) (hc : Integrable c)
    (a : A03SixTensorSpace → ℝ) (ha : Measurable a)
    {D : ℝ} (hD : 0≤D) (hW : ∀ ν i x, ‖a03SixTensorWeight a ν i x‖≤D)
    (x : Fin 6 → ℝ) (hx : 0<x 0) :
    Integrable (fun ν => c ν*((x 0 : ℂ)^a03SixTensorExponent ν 0*
      ∏ j, a03SixTensorWeight a ν j (x j.succ))) := by
  have hcphase : Continuous (fun ν : A03SixTensorSpace =>
      (x 0 : ℂ)^a03SixTensorExponent ν 0) :=
    (a03SixTensorExponent_continuous 0).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have hp := phase_tensor_product_integrable volume c hc (a03SixTensorWeight a)
    (fun i y => (a03SixTensorWeight_measurable a ha i y).aestronglyMeasurable)
    hD hW (fun j => x j.succ)
  have hbounded : ∀ ν, ‖(x 0 : ℂ)^a03SixTensorExponent ν 0‖≤1 := by
    intro ν
    rw [a03SixTensor_character_norm ν hx]
  have hi := hp.mul_bdd (hcphase.aestronglyMeasurable) (ae_of_all _ hbounded)
  convert hi using 1
  funext ν
  ring

theorem a03SixSourceArguments_first_positive (q : QuadraticScales) (n : Fin 7 → ℕ)
    (hB : 0<q.B) (hn : n∈quadraticIndexSet q) : 0<a03SixSourceArguments q n 0 := by
  have hn1 : 0<n 1 := by
    have h := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hn 1)).1
    omega
  exact div_pos (by exact_mod_cast hn1) hB

theorem a03SixTensor_source_integrable
    (f : SchwartzMap A03SixTensorSpace ℂ) (a : A03SixTensorSpace → ℝ)
    (ha : Measurable a) (hc : Integrable (a03SixTensorCoefficient f a))
    {D : ℝ} (hD : 0≤D) (hW : ∀ ν i x, ‖a03SixTensorWeight a ν i x‖≤D)
    (positive : Bool) (q : QuadraticScales) (hB : 0<q.B) (α β : ℕ → ℂ) :
    Integrable (fun ν => a03SixTensorCoefficient f a ν*
      rectangularComplexQuadraticSum positive q α (a03SixTensorBeta ν q.B β)
        (a03SixTensorWeight a ν)) := by
  have hterm (n : Fin 7 → ℕ) (hn : n∈quadraticIndexSet q) :
      Integrable (fun ν => if signedQuadraticRelation positive n then
        (α (n 0)*β (n 1))*(a03SixTensorCoefficient f a ν*
          ((((n 1 : ℝ)/q.B : ℝ) : ℂ)^a03SixTensorExponent ν 0*
            ∏ j, a03SixTensorWeight a ν j (rectangularWeightArguments q n j))) else 0) := by
    by_cases hr : signedQuadraticRelation positive n
    · simpa only [hr,ite_true,a03SixSourceArguments,Fin.cons_zero,Fin.cons_succ] using
        (a03SixTensor_character_product_integrable _ hc a ha hD hW
          (a03SixSourceArguments q n) (a03SixSourceArguments_first_positive q n hB hn)).const_mul
          (α (n 0)*β (n 1))
    · simp only [hr,ite_false]
      exact integrable_zero _ _ volume
  have hs := integrable_finsetSum (quadraticIndexSet q) hterm
  convert hs using 1
  funext ν
  unfold rectangularComplexQuadraticSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hr : signedQuadraticRelation positive n
  · simp only [hr,ite_true,a03SixTensorBeta]
    ring
  · simp only [hr,ite_false,mul_zero]

theorem a03SixTensor_finite_signed_source_reconstruction
    (f : SchwartzMap A03SixTensorSpace ℂ) (a : A03SixTensorSpace → ℝ)
    (ham : Measurable a) (ha : ∀ ν, 0<a ν) (hc : Integrable (a03SixTensorCoefficient f a))
    {D : ℝ} (hD : 0≤D) (hW : ∀ ν i x, ‖a03SixTensorWeight a ν i x‖≤D)
    (positive : Bool) (q : QuadraticScales) (hB : 0<q.B) (α β : ℕ → ℂ) :
    (∫ ν, a03SixTensorCoefficient f a ν*rectangularComplexQuadraticSum positive q α
      (a03SixTensorBeta ν q.B β) (a03SixTensorWeight a ν)) =
      ∑ n∈quadraticIndexSet q, if signedQuadraticRelation positive n then
        α (n 0)*β (n 1)*(∏ j : Fin 5,
          (rectangularSmoothBlockWeight (rectangularWeightArguments q n j) : ℂ))*
          f (a03SixTensorLogPoint (a03SixSourceArguments q n)) else 0 := by
  let F (n : Fin 7 → ℕ) (ν : A03SixTensorSpace) : ℂ :=
    if signedQuadraticRelation positive n then (α (n 0)*β (n 1))*
      (a03SixTensorCoefficient f a ν*((a03SixSourceArguments q n 0 : ℂ)^a03SixTensorExponent ν 0*
        ∏ j, a03SixTensorWeight a ν j (a03SixSourceArguments q n j.succ))) else 0
  have hF (n : Fin 7 → ℕ) (hn : n∈quadraticIndexSet q) : Integrable (F n) := by
    by_cases hr : signedQuadraticRelation positive n
    · simpa only [F,hr,ite_true] using
        (a03SixTensor_character_product_integrable _ hc a ham hD hW
          (a03SixSourceArguments q n) (a03SixSourceArguments_first_positive q n hB hn)).const_mul
          (α (n 0)*β (n 1))
    · simpa only [F,hr,ite_false,zero_mul] using hc.const_mul (0 : ℂ)
  calc
    _ = ∫ ν, ∑ n∈quadraticIndexSet q, F n ν := by
      apply integral_congr_ae
      apply ae_of_all volume
      intro ν
      dsimp only
      unfold rectangularComplexQuadraticSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      by_cases hr : signedQuadraticRelation positive n
      · simp only [F,hr,ite_true,a03SixTensorBeta,a03SixSourceArguments,
          Fin.cons_zero,Fin.cons_succ]
        ring
      · simp only [F,hr,ite_false,mul_zero]
    _ = ∑ n∈quadraticIndexSet q, ∫ ν, F n ν := integral_finsetSum _ hF
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hr : signedQuadraticRelation positive n
      · simp only [F,hr,ite_true,integral_const_mul]
        rw [←a03SixTensor_exact_separation_all_real f a ha (a03SixSourceArguments q n)
          (a03SixSourceArguments_first_positive q n hB hn)]
        simp only [a03SixSourceArguments,Fin.cons_succ]
        ring
      · simp only [F,hr,ite_false,integral_zero]

theorem a03SixTensor_uniform_finite_source_reconstruction {ι : Type*}
    (f : ι → SchwartzMap A03SixTensorSpace ℂ)
    (hf : ∀ k n : ℕ, ∃ C : ℝ, 0≤C ∧ ∀ i, SchwartzMap.seminorm ℂ k n (f i)≤C) :
    ∃ a : A03SixTensorSpace → ℝ, ∃ B : ℕ → ℝ, ∃ K : ℝ,
      Measurable a ∧ (∀ ν, 0<a ν) ∧ (∀ j, 0≤B j) ∧ 0≤K ∧
      (∀ ν j, RectangularComplexWeight (a03SixTensorWeight a ν j)) ∧
      (∀ j ν i x, ‖iteratedDeriv j (a03SixTensorWeight a ν i) x‖≤B j) ∧
      (∀ i, Integrable (a03SixTensorCoefficient (f i) a) ∧
        (∫ ν, ‖a03SixTensorCoefficient (f i) a ν‖)≤K) ∧
      (∀ i (positive : Bool) (q : QuadraticScales), 0<q.B → ∀ α β : ℕ → ℂ,
        Integrable (fun ν => a03SixTensorCoefficient (f i) a ν*
          rectangularComplexQuadraticSum positive q α (a03SixTensorBeta ν q.B β)
            (a03SixTensorWeight a ν)) ∧
        (∫ ν, a03SixTensorCoefficient (f i) a ν*rectangularComplexQuadraticSum positive q α
          (a03SixTensorBeta ν q.B β) (a03SixTensorWeight a ν)) =
          ∑ n∈quadraticIndexSet q, if signedQuadraticRelation positive n then
            α (n 0)*β (n 1)*(∏ j : Fin 5,
              (rectangularSmoothBlockWeight (rectangularWeightArguments q n j) : ℂ))*
              f i (a03SixTensorLogPoint (a03SixSourceArguments q n)) else 0) := by
  obtain ⟨a,B,K,ham,ha,hB,hK,hW,hder,hcoeff,_hexact⟩ := a03SixTensor_uniform_separation f hf
  have h0 : ∀ ν i x, ‖a03SixTensorWeight a ν i x‖≤B 0 := by
    intro ν i x
    simpa using hder 0 ν i x
  refine ⟨a,B,K,ham,ha,hB,hK,hW,hder,hcoeff,?_⟩
  intro i positive q hq α β
  exact ⟨a03SixTensor_source_integrable (f i) a ham (hcoeff i).1 (hB 0) h0 positive q hq α β,
    a03SixTensor_finite_signed_source_reconstruction (f i) a ham ha (hcoeff i).1
      (hB 0) h0 positive q hq α β⟩

end
end Sechstmoment
