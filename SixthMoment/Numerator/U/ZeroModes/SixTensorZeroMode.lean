import SixthMoment.Numerator.U.Sources.SixTensorZeroIntegrability
import SixthMoment.Numerator.U.Sources.SortedEndpoint

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology FourierTransform RealInnerProductSpace
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03SixZeroPairArguments (m n : Bool) (y : Fin 5→ℝ) : Fin 5→ℝ :=
  ![y 0,if m then y 2 else y 1,if m then y 1 else y 2,
    if n then y 4 else y 3,if n then y 3 else y 4]

def a03SixZeroSourceArguments (m n : Bool) (q : QuadraticScales)
    (v : Fin 5→ℕ) (x : ℝ) : Fin 6→ℝ :=
  Fin.cons ((v 1:ℝ)/q.B) (a03SixZeroPairArguments m n (rectangularZeroArguments q v x))

def a03SixTensorPhysicalZeroMode (F : A03SixTensorSpace→ℂ) (m n : Bool)
    (q : QuadraticScales) (α β : ℕ→ℂ) : ℂ :=
  ∑ v∈quadraticMainIndexSet q, α (v 0)*β (v 1)*
    ∫ x : ℝ in Ioi 0, (∏ j : Fin 5,
      (rectangularSmoothBlockWeight (a03SixZeroSourceArguments m n q v x j.succ):ℂ))*
        F (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))

theorem a03SixZero_pair_weight_product (m n : Bool) (W : Fin 5→ℝ→ℂ) (y : Fin 5→ℝ) :
    (∏ j, phasePairSwapWeights m n W j (y j))=
      ∏ j, W j (a03SixZeroPairArguments m n y j) := by
  cases m <;> cases n <;>
    simp [phasePairSwapWeights,a03SixZeroPairArguments,Fin.prod_univ_five,
      mul_comm,mul_left_comm,mul_assoc]

theorem a03SixZero_first_argument_positive (m n : Bool) (q : QuadraticScales)
    (hB : 0<q.B) (v : Fin 5→ℕ) (hv : v∈quadraticMainIndexSet q) (x : ℝ) :
    0<a03SixZeroSourceArguments m n q v x 0 := by
  have h1 := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hv 1)).1
  exact div_pos (by exact_mod_cast (show 0<v 1 by omega)) hB


theorem a03SixTensor_physical_zero_term_integrable
    (f : SchwartzMap A03SixTensorSpace ℂ) (a : A03SixTensorSpace→ℝ)
    (ham : Measurable a) (ha : ∀ ν,0<a ν) (hc : Integrable (a03SixTensorCoefficient f a))
    {D : ℝ} (hD : 0≤D) (hW : ∀ ν i x, ‖a03SixTensorWeight a ν i x‖≤D)
    (m n : Bool) (q : QuadraticScales) (hB : 0<q.B) (hM₂ : 0<q.M₂)
    (v : Fin 5→ℕ) (hv : v∈quadraticMainIndexSet q) :
    Integrable (fun x : ℝ => (∏ j : Fin 5,
      (rectangularSmoothBlockWeight (a03SixZeroSourceArguments m n q v x j.succ):ℂ))*
        f (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))) (volume.restrict (Ioi 0)) := by
  have hvpos : ∀ j,1≤v j := fun j => (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hv j)).1
  have hj := a03SixTensor_zero_joint_integrable f a ham hc hD hW m n q hB hM₂ v hvpos
  apply hj.integral_prod_right.congr
  apply ae_of_all
  intro x
  simp only [a03SixZero_pair_weight_product]
  exact (a03SixTensor_exact_separation_all_real f a ha
    (a03SixZeroSourceArguments m n q v x)
    (a03SixZero_first_argument_positive m n q hB v hv x)).symm

theorem a03SixTensor_native_zero_reconstruction
    (f : SchwartzMap A03SixTensorSpace ℂ) (a : A03SixTensorSpace→ℝ)
    (ham : Measurable a) (ha : ∀ ν,0<a ν) (hc : Integrable (a03SixTensorCoefficient f a))
    {D : ℝ} (hD : 0≤D) (hW : ∀ ν i x, ‖a03SixTensorWeight a ν i x‖≤D)
    (m n : Bool) (q : QuadraticScales) (hB : 0<q.B) (hM₂ : 0<q.M₂) (α β : ℕ→ℂ) :
    Integrable (fun ν => a03SixTensorCoefficient f a ν*
      rectangularComplexZeroMode q α (a03SixTensorBeta ν q.B β)
        (phasePairSwapWeights m n (a03SixTensorWeight a ν))) ∧
    (∫ ν, a03SixTensorCoefficient f a ν*
      rectangularComplexZeroMode q α (a03SixTensorBeta ν q.B β)
        (phasePairSwapWeights m n (a03SixTensorWeight a ν)))=
      a03SixTensorPhysicalZeroMode f m n q α β := by
  let J (v : Fin 5→ℕ) (ν : A03SixTensorSpace) (x : ℝ) : ℂ :=
    a03SixTensorCoefficient f a ν*((((v 1:ℝ)/q.B:ℝ):ℂ)^a03SixTensorExponent ν 0*
      ∏ i, phasePairSwapWeights m n (a03SixTensorWeight a ν) i (rectangularZeroArguments q v x i))
  let F (v : Fin 5→ℕ) (ν : A03SixTensorSpace) : ℂ :=
    (α (v 0)*β (v 1))*∫ x : ℝ in Ioi 0, J v ν x
  have hJ (v : Fin 5→ℕ) (hv : v∈quadraticMainIndexSet q) :
      Integrable (Function.uncurry (J v)) (volume.prod (volume.restrict (Ioi 0))) := by
    have hvpos : ∀ j,1≤v j := fun j => (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hv j)).1
    exact a03SixTensor_zero_joint_integrable f a ham hc hD hW m n q hB hM₂ v hvpos
  have hF (v : Fin 5→ℕ) (hv : v∈quadraticMainIndexSet q) : Integrable (F v) :=
    (hJ v hv).integral_prod_left.const_mul _
  have hpoint (ν : A03SixTensorSpace) : a03SixTensorCoefficient f a ν*
      rectangularComplexZeroMode q α (a03SixTensorBeta ν q.B β)
        (phasePairSwapWeights m n (a03SixTensorWeight a ν))=∑ v∈quadraticMainIndexSet q,F v ν := by
    unfold rectangularComplexZeroMode
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    simp only [F,J,a03SixTensorBeta,integral_const_mul]
    ring
  refine ⟨?_,?_⟩
  · convert integrable_finsetSum (quadraticMainIndexSet q) hF using 1
    funext ν
    exact hpoint ν
  · calc
      _=∫ ν, ∑ v∈quadraticMainIndexSet q,F v ν := by
        apply integral_congr_ae
        exact ae_of_all volume hpoint
      _=∑ v∈quadraticMainIndexSet q,∫ ν,F v ν := integral_finsetSum _ hF
      _=_ := by
        unfold a03SixTensorPhysicalZeroMode
        apply Finset.sum_congr rfl
        intro v hv
        simp only [F,integral_const_mul]
        rw [integral_integral_swap (hJ v hv)]
        congr 1
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [J,a03SixZero_pair_weight_product]
        exact (a03SixTensor_exact_separation_all_real f a ha
          (a03SixZeroSourceArguments m n q v x)
          (a03SixZero_first_argument_positive m n q hB v hv x)).symm

theorem a03SixTensorPhysicalZeroMode_congr_on_dyadic_box
    (F G : A03SixTensorSpace→ℂ) (m n : Bool) (q : QuadraticScales) (hB : 0<q.B)
    (α β : ℕ→ℂ) (hβ : ∀ v : ℕ,(v:ℝ)∉Icc q.B (2*q.B) → β v=0)
    (hFG : ∀ x : Fin 6→ℝ,(∀ j,x j∈Icc (1:ℝ) 2) →
      F (a03SixTensorLogPoint x)=G (a03SixTensorLogPoint x)) :
    a03SixTensorPhysicalZeroMode F m n q α β=a03SixTensorPhysicalZeroMode G m n q α β := by
  unfold a03SixTensorPhysicalZeroMode
  apply Finset.sum_congr rfl
  intro v _
  by_cases hβ0 : β (v 1)=0
  · simp [hβ0]
  · have hbs : (v 1:ℝ)∈Icc q.B (2*q.B) := by
      by_contra hb
      exact hβ0 (hβ (v 1) hb)
    rw [←integral_const_mul,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hp : (∏ j : Fin 5,
        (rectangularSmoothBlockWeight (a03SixZeroSourceArguments m n q v x j.succ):ℂ))=0
    · simp [hp]
    · rw [hFG]
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · exact ⟨(le_div_iff₀ hB).mpr (by simpa only [one_mul] using hbs.1),
          (div_le_iff₀ hB).mpr (by simpa only [mul_comm] using hbs.2)⟩
      · have hwi : rectangularSmoothBlockWeight (a03SixZeroSourceArguments m n q v x i.succ)≠0 := by
          intro hz
          apply hp
          exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hz])
        exact rectangularSmoothBlockWeight_tsupport (subset_tsupport _ hwi)

theorem a03SixTensorPhysicalZeroMode_remove_log_cutoff
    (f : SchwartzMap A03SixTensorSpace ℂ) (F : A03SixTensorSpace→ℂ)
    (hgraph : ∀ y,f y=a03TensorLogCutoff y*F y)
    (m n : Bool) (q : QuadraticScales) (hB : 0<q.B) (α β : ℕ→ℂ)
    (hβ : ∀ v : ℕ,(v:ℝ)∉Icc q.B (2*q.B) → β v=0) :
    a03SixTensorPhysicalZeroMode f m n q α β=a03SixTensorPhysicalZeroMode F m n q α β := by
  apply a03SixTensorPhysicalZeroMode_congr_on_dyadic_box f F m n q hB α β hβ
  intro x hx
  rw [hgraph,a03TensorLogCutoff_logPoint_one hx,one_mul]


def a03EndpointPhysicalSortedZeroMode (F : A03SixTensorSpace→ℂ) (T A B H : ℝ)
    (f g : ℝ→ℝ) (k : Fin 4→ℕ) : ℂ :=
  let q := phaseActualScales A B H k
  let q' := boundaryEmbeddedScales (boundaryActualFlags k) q
  let m := decide (q'.M₂<q'.M₁)
  let n := decide (q'.N₂<q'.N₁)
  a03SixTensorPhysicalZeroMode F m n (phasePairSwapScales m n q)
    (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B)

theorem a03_actual_native_sorted_zero_integral_eq_physical
    (kernel : SchwartzMap A03SixTensorSpace ℂ) (normalizer : A03SixTensorSpace→ℝ)
    (ham : Measurable normalizer) (ha : ∀ ν,0<normalizer ν)
    (hc : Integrable (a03SixTensorCoefficient kernel normalizer))
    {D : ℝ} (hD : 0≤D) (hW : ∀ ν i x, ‖a03SixTensorWeight normalizer ν i x‖≤D)
    (T A B H : ℝ) (f g : ℝ→ℝ) (k : Fin 4→ℕ) (hA : 0<A) (hB : 0<B) (hH : 0<H) :
    Integrable (fun ν => a03SixTensorCoefficient kernel normalizer ν*
      a03EndpointNativeSortedZeroMode T A B H f g k normalizer ν) ∧
    a03EndpointNativeSortedZeroIntegral kernel normalizer T A B H f g k=
      a03EndpointPhysicalSortedZeroMode kernel T A B H f g k := by
  let q := phaseActualScales A B H k
  let q' := boundaryEmbeddedScales (boundaryActualFlags k) q
  let m := decide (q'.M₂<q'.M₁)
  let n := decide (q'.N₂<q'.N₁)
  have hq := boundaryActual_scales_pos A B H k hA hB hH
  have hM₁ : 0<q.M₁ := by simpa [q,QuadraticScales.size] using hq 2
  have hM₂ : 0<q.M₂ := by simpa [q,QuadraticScales.size] using hq 3
  have hsortedM : 0<(phasePairSwapScales m n q).M₂ := by
    dsimp [phasePairSwapScales]
    split_ifs
    · exact hM₁
    · exact hM₂
  have hz := a03SixTensor_native_zero_reconstruction kernel normalizer ham ha hc hD hW
    m n (phasePairSwapScales m n q) hB hsortedM
      (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B)
  exact hz

theorem a03_actual_native_sorted_zero_integral_eq_uncut_physical
    (kernel : SchwartzMap A03SixTensorSpace ℂ) (F : A03SixTensorSpace→ℂ)
    (hgraph : ∀ y,kernel y=a03TensorLogCutoff y*F y)
    (normalizer : A03SixTensorSpace→ℝ) (ham : Measurable normalizer) (ha : ∀ ν,0<normalizer ν)
    (hc : Integrable (a03SixTensorCoefficient kernel normalizer))
    {D : ℝ} (hD : 0≤D) (hW : ∀ ν i x, ‖a03SixTensorWeight normalizer ν i x‖≤D)
    (T A B H : ℝ) (f g : ℝ→ℝ) (k : Fin 4→ℕ) (hA : 0<A) (hB : 0<B) (hH : 0<H) :
    Integrable (fun ν => a03SixTensorCoefficient kernel normalizer ν*
      a03EndpointNativeSortedZeroMode T A B H f g k normalizer ν) ∧
    a03EndpointNativeSortedZeroIntegral kernel normalizer T A B H f g k=
      a03EndpointPhysicalSortedZeroMode F T A B H f g k := by
  obtain ⟨hi,he⟩ := a03_actual_native_sorted_zero_integral_eq_physical kernel normalizer ham ha hc hD hW
    T A B H f g k hA hB hH
  refine ⟨hi,he.trans ?_⟩
  unfold a03EndpointPhysicalSortedZeroMode
  exact a03SixTensorPhysicalZeroMode_remove_log_cutoff kernel F hgraph _ _ _ hB _ _
    (phaseActualAmplifierCoefficient_support T g hB)

theorem a03_actual_endpoint_zero_integral_eventually_eq_uncut_physical
    {a b s : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hs : s<1/2)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ,0<A → 0<B → 0<H →
      ∀ k : Fin 4→ℕ,phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
      ∀ kernel : SchwartzMap A03SixTensorSpace ℂ, ∀ F : A03SixTensorSpace→ℂ,
      (∀ y,kernel y=a03TensorLogCutoff y*F y) →
      ∀ normalizer : A03SixTensorSpace→ℝ,Measurable normalizer → (∀ ν,0<normalizer ν) →
      Integrable (a03SixTensorCoefficient kernel normalizer) →
      ∀ D : ℝ,0≤D → (∀ ν i x,‖a03SixTensorWeight normalizer ν i x‖≤D) →
      Integrable (fun ν => a03SixTensorCoefficient kernel normalizer ν*
        a03EndpointNormalizedZeroMode T A B H f g k normalizer ν) ∧
      a03EndpointZeroIntegral kernel normalizer T A B H f g k=
        a03EndpointPhysicalSortedZeroMode F T A B H f g k := by
  filter_upwards [a03_actual_endpoint_zero_integral_eq_native_sorted ha hab hlen hs f g hf hg]
    with T hback
  intro A B H hA hB hH k hactive kernel F hgraph normalizer ham hpos hcoef D hD hW
  have hweights : ∀ ν i,RectangularComplexWeight (a03SixTensorWeight normalizer ν i) :=
    a03SixTensorWeight_complexWeight normalizer
  have he := hback A B H hA hB hH k hactive normalizer hweights kernel
  have hp := a03_actual_native_sorted_zero_integral_eq_uncut_physical kernel F hgraph
    normalizer ham hpos hcoef hD hW T A B H f g k hA hB hH
  exact ⟨he.2.mpr hp.1,he.1.trans hp.2⟩

theorem a03SixTensor_uniform_native_zero_reconstruction {ι : Type*}
    (f : ι→SchwartzMap A03SixTensorSpace ℂ)
    (hf : ∀ k n : ℕ,∃ C : ℝ,0≤C ∧ ∀ i,SchwartzMap.seminorm ℂ k n (f i)≤C) :
    ∃ a : A03SixTensorSpace→ℝ, ∃ bounds : ℕ→ℝ, ∃ K : ℝ,
      Measurable a ∧ (∀ ν,0<a ν) ∧ (∀ j,0≤bounds j) ∧ 0≤K ∧
      (∀ ν j,RectangularComplexWeight (a03SixTensorWeight a ν j)) ∧
      (∀ j ν i x,‖iteratedDeriv j (a03SixTensorWeight a ν i) x‖≤bounds j) ∧
      (∀ i,Integrable (a03SixTensorCoefficient (f i) a) ∧ (∫ ν,‖a03SixTensorCoefficient (f i) a ν‖)≤K) ∧
      (∀ i m n q,0<q.B → 0<q.M₂ → ∀ α β : ℕ→ℂ,
        Integrable (fun ν => a03SixTensorCoefficient (f i) a ν*
          rectangularComplexZeroMode q α (a03SixTensorBeta ν q.B β)
            (phasePairSwapWeights m n (a03SixTensorWeight a ν))) ∧
        (∫ ν,a03SixTensorCoefficient (f i) a ν*
          rectangularComplexZeroMode q α (a03SixTensorBeta ν q.B β)
            (phasePairSwapWeights m n (a03SixTensorWeight a ν)))=
          a03SixTensorPhysicalZeroMode (f i) m n q α β) := by
  obtain ⟨a,bounds,K,ham,ha,hb,hK,hW,hd,hcoef,_hexact⟩ := a03SixTensor_uniform_separation f hf
  refine ⟨a,bounds,K,ham,ha,hb,hK,hW,hd,hcoef,?_⟩
  intro i m n q hB hM₂ α β
  exact a03SixTensor_native_zero_reconstruction (f i) a ham ha (hcoef i).1 (hb 0)
    (fun ν i x => by simpa using hd 0 ν i x) m n q hB hM₂ α β

end
end SixthMoment
