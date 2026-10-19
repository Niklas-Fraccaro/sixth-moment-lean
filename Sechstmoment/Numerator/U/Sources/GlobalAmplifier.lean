import Sechstmoment.Numerator.U.Diagonal.ActualNearAmplifierMass
import Sechstmoment.Numerator.U.Reconstruction.TensorActualSourceEndpoint

/-! Recover the genuine reciprocal square-root amplifier factors before
using the quadratic source.  The literal endpoint coefficients already
contain these factors; the source class used here extracts them rather
than discarding them in a coefficient bound. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem phaseActualAmplifierCoefficient_norm_le_block_sqrt
    (T A : ℝ) (f : ℝ → ℝ) {F : ℝ} (hA : 0<A) (hF : 0≤F)
    (hf : ∀ x, ‖f x‖≤F) (n : ℕ) :
    ‖phaseActualAmplifierCoefficient T f A n‖≤F/Real.sqrt A := by
  by_cases hn : phaseActualAmplifierCoefficient T f A n=0
  · rw [hn,norm_zero]; positivity
  · have hs : (n:ℝ)∈Icc A (2*A) := by
      by_contra h
      exact hn (phaseActualAmplifierCoefficient_support T f hA n h)
    have hnp : 0<n := by exact_mod_cast hA.trans_le hs.1
    exact (phaseActualAmplifierCoefficient_norm_le_reciprocal_sqrt T A f hF hf hnp).trans
      (div_le_div_of_nonneg_left hF (Real.sqrt_pos.mpr hA)
        (Real.sqrt_le_sqrt hs.1))

theorem boundaryActual_alpha_norm_le_block_sqrt (T A : ℝ) (f : ℝ → ℝ)
    (k : Fin 4 → ℕ) {F : ℝ} (hA : 0<A) (hF : 0≤F)
    (hf : ∀ x, ‖f x‖≤F) (n : ℕ) :
    ‖boundaryActualAlpha T A f k n‖≤F/Real.sqrt A := by
  exact rectangular_unit_coefficient_bound _ (by positivity)
    (fun m => rectangular_unit_coefficient_bound _ (by positivity)
      (phaseActualAmplifierCoefficient_norm_le_block_sqrt T A f hA hF hf) m) n

theorem a03SixActualBoundaryBeta_norm_le_block_sqrt (T B : ℝ) (g : ℝ → ℝ)
    (k : Fin 4 → ℕ) (ν : A03SixTensorSpace) {G : ℝ} (hB : 0<B)
    (hG : 0≤G) (hg : ∀ x, ‖g x‖≤G) (n : ℕ) :
    ‖a03SixActualBoundaryBeta T B g k ν n‖≤G/Real.sqrt B := by
  have hb (m : ℕ) :
      ‖a03SixTensorBeta ν B (phaseActualAmplifierCoefficient T g B) m‖≤G/Real.sqrt B := by
    rw [a03SixTensorBeta_norm ν hB _ (phaseActualAmplifierCoefficient_support T g hB)]
    exact phaseActualAmplifierCoefficient_norm_le_block_sqrt T B g hB hG hg m
  exact rectangular_unit_coefficient_bound _ (by positivity)
    (fun m => rectangular_unit_coefficient_bound _ (by positivity) hb m) n

def a03EndpointScaledAlpha (T A : ℝ) (f : ℝ → ℝ) (k : Fin 4 → ℕ) (n : ℕ) : ℂ :=
  (Real.sqrt A : ℂ)*boundaryActualAlpha T A f k n

def a03EndpointScaledBeta (T B : ℝ) (g : ℝ → ℝ) (k : Fin 4 → ℕ)
    (ν : A03SixTensorSpace) (n : ℕ) : ℂ :=
  (Real.sqrt B : ℂ)*a03SixActualBoundaryBeta T B g k ν n

def a03EndpointScaledDiscrepancy (positive : Bool) (T A B H : ℝ) (f g : ℝ → ℝ)
    (k : Fin 4 → ℕ) (normalizer : A03SixTensorSpace → ℝ) (ν : A03SixTensorSpace) : ℂ :=
  let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
  rectangularComplexDiscrepancy (phaseNormalizedSign q positive) (phaseNormalizedScales q)
    (phaseNormalizedAlpha q (a03EndpointScaledAlpha T A f k) (a03EndpointScaledBeta T B g k ν))
    (phaseNormalizedBeta q (a03EndpointScaledAlpha T A f k) (a03EndpointScaledBeta T B g k ν))
    (phaseNormalizedWeights q (a03SixTensorWeight normalizer ν))

theorem rectangularComplexDiscrepancy_mul_coefficients (positive : Bool)
    (q : QuadraticScales) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℂ) (x y : ℂ) :
    rectangularComplexDiscrepancy positive q (fun n => x*α n) (fun n => y*β n) W=
      (x*y)*rectangularComplexDiscrepancy positive q α β W := by
  unfold rectangularComplexDiscrepancy rectangularComplexQuadraticSum rectangularComplexZeroMode
  rw [mul_sub,Finset.mul_sum,Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro n _
    split_ifs <;> ring
  · apply Finset.sum_congr rfl
    intro n _
    ring

theorem a03EndpointScaledDiscrepancy_eq (positive : Bool) (T A B H : ℝ)
    (f g : ℝ → ℝ) (k : Fin 4 → ℕ) (normalizer : A03SixTensorSpace → ℝ)
    (ν : A03SixTensorSpace) :
    a03EndpointScaledDiscrepancy positive T A B H f g k normalizer ν=
      ((Real.sqrt A : ℂ)*(Real.sqrt B : ℂ))*
        a03EndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν := by
  let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
  unfold a03EndpointScaledDiscrepancy a03EndpointNormalizedDiscrepancy
    phaseNormalizedAlpha phaseNormalizedBeta
  dsimp only
  split_ifs
  · exact rectangularComplexDiscrepancy_mul_coefficients
      (phaseNormalizedSign q positive) (phaseNormalizedScales q)
      (boundaryActualAlpha T A f k) (a03SixActualBoundaryBeta T B g k ν)
      (phaseNormalizedWeights q (a03SixTensorWeight normalizer ν))
      (Real.sqrt A : ℂ) (Real.sqrt B : ℂ)
  · have he := rectangularComplexDiscrepancy_mul_coefficients
      (phaseNormalizedSign q positive) (phaseNormalizedScales q)
      (a03SixActualBoundaryBeta T B g k ν) (boundaryActualAlpha T A f k)
      (phaseNormalizedWeights q (a03SixTensorWeight normalizer ν))
      (Real.sqrt B : ℂ) (Real.sqrt A : ℂ)
    rw [mul_comm (Real.sqrt B : ℂ) (Real.sqrt A : ℂ)] at he
    exact he

def phaseActualScaledSixFourierSourceClasses (ε K : ℝ) (bounds : ℕ → ℝ)
    (normalizer : A03SixTensorSpace → ℝ) (T A B H : ℝ) (f g : ℝ → ℝ)
    (k : Fin 4 → ℕ) : Prop :=
  ∀ ν : A03SixTensorSpace, ∀ component : Fin 5 → Bool,
    let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
    QuadraticAdmissible ε 1 K bounds (phaseNormalizedScales q)
      (phaseNormalizedAlpha q (a03EndpointScaledAlpha T A f k) (a03EndpointScaledBeta T B g k ν))
      (phaseNormalizedBeta q (a03EndpointScaledAlpha T A f k) (a03EndpointScaledBeta T B g k ν))
      (rectangularRealComponent (phaseNormalizedWeights q (a03SixTensorWeight normalizer ν)) component)

/-- A source-admissible physical block retains its source class after the
two actual amplifier square-root factors are extracted.  The enlarged
constant depends only on the original class and the two profile bounds. -/
theorem phaseActualScaledSixFourierSourceClasses_of_actual
    {ε K F G : ℝ} (hε : 0≤ε) (hK : 1≤K) (hF : 0≤F) (hG : 0≤G)
    (T A B H : ℝ) (f g : ℝ → ℝ) (k : Fin 4 → ℕ)
    (hA : 2/3≤A) (hB : 2/3≤B) (hH : 2/3≤H)
    (hf : ∀ x, ‖f x‖≤F) (hg : ∀ x, ‖g x‖≤G)
    (bounds : ℕ → ℝ) (normalizer : A03SixTensorSpace → ℝ)
    (hadm : phaseActualSixFourierSourceClasses ε K bounds normalizer T A B H f g k) :
    phaseActualScaledSixFourierSourceClasses ε (max K (max F G)) bounds normalizer T A B H f g k := by
  intro ν component
  let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
  let L := max K (max F G)
  have hKL : K≤L := le_max_left _ _
  have hFL : F≤L := (le_max_left F G).trans (le_max_right _ _)
  have hGL : G≤L := (le_max_right F G).trans (le_max_right _ _)
  have hL : 0≤L := (zero_le_one.trans hK).trans hKL
  have hAp : 0<A := by linarith
  have hBp : 0<B := by linarith
  have hq : ∀ j, 1≤q.size j := boundaryActual_embedded_lower_bounds A B H k hA hB hH
  have hAs : ∀ n : ℕ, (n:ℝ)∉Icc q.A (2*q.A) → a03EndpointScaledAlpha T A f k n=0 := by
    intro n hn
    simp only [a03EndpointScaledAlpha,boundaryActual_alpha_support T A B H f k hAp n hn,mul_zero]
  have hBs : ∀ n : ℕ, (n:ℝ)∉Icc q.B (2*q.B) → a03EndpointScaledBeta T B g k ν n=0 := by
    intro n hn
    simp only [a03EndpointScaledBeta,a03SixActualBoundaryBeta_support T A B H g k ν hBp n hn,mul_zero]
  have hAb : ∀ n, ‖a03EndpointScaledAlpha T A f k n‖≤L*q.A^ε := by
    intro n
    have hA1 : 1≤q.A := by simpa [QuadraticScales.size] using hq 0
    unfold a03EndpointScaledAlpha
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg A)]
    calc
      _ ≤ Real.sqrt A*(F/Real.sqrt A) := mul_le_mul_of_nonneg_left
        (boundaryActual_alpha_norm_le_block_sqrt T A f k hAp hF hf n) (Real.sqrt_nonneg A)
      _ = F := mul_div_cancel₀ F (Real.sqrt_pos.mpr hAp).ne'
      _ ≤ L*q.A^ε := hFL.trans (le_mul_of_one_le_right hL (Real.one_le_rpow hA1 hε))
  have hBb : ∀ n, ‖a03EndpointScaledBeta T B g k ν n‖≤L*q.B^ε := by
    intro n
    have hB1 : 1≤q.B := by simpa [QuadraticScales.size] using hq 1
    unfold a03EndpointScaledBeta
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg B)]
    calc
      _ ≤ Real.sqrt B*(G/Real.sqrt B) := mul_le_mul_of_nonneg_left
        (a03SixActualBoundaryBeta_norm_le_block_sqrt T B g k ν hBp hG hg n) (Real.sqrt_nonneg B)
      _ = G := mul_div_cancel₀ G (Real.sqrt_pos.mpr hBp).ne'
      _ ≤ L*q.B^ε := hGL.trans (le_mul_of_one_le_right hL (Real.one_le_rpow hB1 hε))
  have hcs := phase_normalized_coefficient_supports q _ _ hAs hBs
  have hcb := phase_normalized_coefficient_bounds q _ _ L ε hAb hBb
  rcases hadm ν component with ⟨hs,hm,hn,hh,hδ,hl,hr,ho,_hAs,_hBs,_hAb,_hBb,hW,hd⟩
  have hgeo : phaseSourceGeometry ε K (phaseNormalizedScales q) := by
    exact ⟨hs,hm,hn,hh,by simpa only [Real.rpow_one] using hδ,hl,hr,ho⟩
  rcases phase_source_geometry_mono _ hgeo hKL with ⟨hs',hm',hn',hh',hδ',hl',hr',ho'⟩
  exact ⟨hs',hm',hn',hh',by simpa only [Real.rpow_one] using hδ',hl',hr',ho',
    hcs.1,hcs.2,hcb.1,hcb.2,hW,hd⟩


/-- The uniform literal source superposition estimate includes the actual
reciprocal amplifier square roots.  Neither an amplifier mass nor an error
budget is supplied as a hypothesis. -/
theorem a03_actual_source_sqrt_superposition
    (hinput : SeparatedQuadraticInput) {ε K F G : ℝ} (hε : 0<ε) (hK : 1≤K)
    (hF : 0≤F) (hG : 0≤G) (f g : ℝ → ℝ)
    (hf : ∀ x, ‖f x‖≤F) (hg : ∀ x, ‖g x‖≤G)
    (bounds : ℕ → ℝ) (hbounds : ∀ j, 0≤bounds j)
    (normalizer : A03SixTensorSpace → ℝ) (hm : Measurable normalizer)
    (hW : ∀ ν j, RectangularComplexWeight (a03SixTensorWeight normalizer ν j)) :
    ∃ C : ℝ, 0≤C ∧ ∀ T A B H k
      (c : A03SixTensorSpace → ℂ), Integrable c →
      2/3≤A → 2/3≤B → 2/3≤H →
      phaseActualSixFourierSourceClasses (DivisorProof.inputExponent ε 1) K bounds normalizer T A B H f g k →
      ∀ positive : Bool,
      Integrable (fun ν => c ν*a03EndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν) ∧
      ‖∫ ν, c ν*a03EndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν‖ ≤
        (C*phaseSourceMajorant ε (phaseNormalizedScales
          (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k))))/
            Real.sqrt (A*B)*(∫ ν, ‖c ν‖) := by
  let L := max K (max F G)
  have hL : 1≤L := hK.trans (le_max_left _ _)
  obtain ⟨C,hC,hsource⟩ := phase_BBLRv1_integrable_component_source
    hinput hε (by norm_num : (0:ℝ)<1) hL bounds hbounds
  obtain ⟨Cbase,_hCbase,hbase⟩ := a03_actual_source_class_superposition
    hinput hε hK bounds hbounds normalizer hm hW
  refine ⟨C,hC,?_⟩
  intro T A B H k c hc hA hB hH hadm positive
  have hAp : 0<A := by linarith
  have hBp : 0<B := by linarith
  let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
  let α := fun _ : A03SixTensorSpace => a03EndpointScaledAlpha T A f k
  let β := fun ν => a03EndpointScaledBeta T B g k ν
  have hα : ∀ n, Measurable (fun ν => α ν n) := fun _ => measurable_const
  have hβ : ∀ n, Measurable (fun ν => β ν n) := by
    intro n
    exact measurable_const.mul ((a03SixActualBoundaryBeta_measurable T B g k hBp) n)
  have hscaled := phaseActualScaledSixFourierSourceClasses_of_actual (DivisorProof.inputExponent_pos hε (by norm_num)).le hK hF hG
    T A B H f g k hA hB hH hf hg bounds normalizer hadm
  obtain ⟨_hscaled,hbound⟩ := hsource A03SixTensorSpace volume (phaseNormalizedScales q)
    (fun ν => phaseNormalizedAlpha q (α ν) (β ν))
    (fun ν => phaseNormalizedBeta q (α ν) (β ν))
    (fun ν => phaseNormalizedWeights q (a03SixTensorWeight normalizer ν)) c hc
    (phase_normalized_alpha_measurable q α β hα hβ)
    (phase_normalized_beta_measurable q α β hα hβ)
    (phase_normalized_weights_measurable q (a03SixTensorWeight normalizer)
      (a03SixTensorWeight_measurable normalizer hm))
    hscaled (fun ν => phase_normalized_weights_complex q _ (hW ν)) (phaseNormalizedSign q positive)
  have heq : (∫ ν, c ν*a03EndpointScaledDiscrepancy positive T A B H f g k normalizer ν)=
      ((Real.sqrt A : ℂ)*(Real.sqrt B : ℂ))*
        ∫ ν, c ν*a03EndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν := by
    simp_rw [a03EndpointScaledDiscrepancy_eq]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all volume fun ν => by ring
  change ‖∫ ν, c ν*a03EndpointScaledDiscrepancy positive T A B H f g k normalizer ν‖≤
    (C*phaseSourceMajorant ε (phaseNormalizedScales q))*(∫ ν, ‖c ν‖) at hbound
  rw [heq,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg A),Real.norm_of_nonneg (Real.sqrt_nonneg B),
    ← Real.sqrt_mul hAp.le] at hbound
  refine ⟨(hbase T A B H f g k c hc hadm hBp positive).1,?_⟩
  have hsqrt : 0<Real.sqrt (A*B) := Real.sqrt_pos.mpr (mul_pos hAp hBp)
  calc
    _ ≤ ((C*phaseSourceMajorant ε (phaseNormalizedScales q))*(∫ ν, ‖c ν‖))/Real.sqrt (A*B) :=
      (le_div_iff₀ hsqrt).mpr (by simpa only [mul_comm] using hbound)
    _ = _ := by ring


def a03EndpointZeroIntegral (kernel : SchwartzMap A03SixTensorSpace ℂ)
    (normalizer : A03SixTensorSpace → ℝ) (T A B H : ℝ) (f g : ℝ → ℝ)
    (k : Fin 4 → ℕ) : ℂ :=
  ∫ ν, a03SixTensorCoefficient kernel normalizer ν*
    a03EndpointNormalizedZeroMode T A B H f g k normalizer ν

/-- Exact endpoint difference and quantitative square-root budget, usable
for either genuine original or dual physical tensor family. -/
theorem a03_actual_tensor_endpoint_difference_sqrt
    (kernel : SchwartzMap A03SixTensorSpace ℂ) (normalizer : A03SixTensorSpace → ℝ)
    (hm : Measurable normalizer) (hc : Integrable (a03SixTensorCoefficient kernel normalizer))
    {D : ℝ} (hD : 0≤D) (h0 : ∀ ν i x, ‖a03SixTensorWeight normalizer ν i x‖≤D)
    (hW : ∀ ν i, RectangularComplexWeight (a03SixTensorWeight normalizer ν i))
    (positive : Bool) (T A B H : ℝ) (f g : ℝ → ℝ) (k : Fin 4 → ℕ)
    (hA : 0<A) (hB : 0<B) (hH : 0<H) (physical : ℂ)
    (hphysical : (∫ ν, a03SixTensorCoefficient kernel normalizer ν*
      a03EndpointNormalizedSum positive T A B H f g k normalizer ν)=physical)
    (hdisc : Integrable (fun ν => a03SixTensorCoefficient kernel normalizer ν*
      a03EndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν)) :
    Integrable (fun ν => a03SixTensorCoefficient kernel normalizer ν*
      a03EndpointNormalizedZeroMode T A B H f g k normalizer ν) ∧
    physical-a03EndpointZeroIntegral kernel normalizer T A B H f g k=
      ∫ ν, a03SixTensorCoefficient kernel normalizer ν*
        a03EndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν := by
  have hnative := a03SixTensor_source_integrable kernel normalizer hm hc hD h0
    positive (phaseActualScales A B H k) hB
    (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B)
  have hsum : Integrable (fun ν => a03SixTensorCoefficient kernel normalizer ν*
      a03EndpointNormalizedSum positive T A B H f g k normalizer ν) := by
    apply hnative.congr
    exact ae_of_all volume fun ν => congrArg (fun z : ℂ =>
      a03SixTensorCoefficient kernel normalizer ν*z)
      (a03Six_actual_normalized_source_sum positive T A B H f g k ν _ (hW ν) hA hB hH)
  have hz : Integrable (fun ν => a03SixTensorCoefficient kernel normalizer ν*
      a03EndpointNormalizedZeroMode T A B H f g k normalizer ν) := by
    apply (hsum.sub hdisc).congr
    apply ae_of_all volume
    intro ν
    simp only [Pi.sub_apply]
    unfold a03EndpointNormalizedSum a03EndpointNormalizedDiscrepancy
      a03EndpointNormalizedZeroMode rectangularComplexDiscrepancy
    dsimp only
    ring
  refine ⟨hz,?_⟩
  rw [←hphysical]
  unfold a03EndpointZeroIntegral
  rw [←integral_sub hsum hz]
  apply integral_congr_ae
  apply ae_of_all volume
  intro ν
  unfold a03EndpointNormalizedSum a03EndpointNormalizedDiscrepancy
    a03EndpointNormalizedZeroMode rectangularComplexDiscrepancy
  dsimp only
  ring


/-- Genuine main source endpoint, preserving the reciprocal amplifier
square roots and deriving every source field from the physical factory. -/
theorem a03_actual_main_tensor_source_endpoint_sqrt
    (hinput : SeparatedQuadraticInput) {a b εsource εkernel c κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hεsource : 0<εsource)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc 1 2)
    (hc : 0<c) (hc1 : c≤1) (hεkernel : 4*c<εkernel)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ T0 : ℝ, ∃ kernels : {p : A03NearTensorData // A03NearTensorValid T0 θ κ p} → SchwartzMap A03SixTensorSpace ℂ,
      ∃ s u Ccoef Csource : ℝ, ∃ normalizer : A03SixTensorSpace → ℝ,
      (∀ p y, kernels p y=a03TensorLogCutoff y*a03ActualTensorNormalizedKernel Φ c εkernel p.val y) ∧
      0<s ∧ s<1/2 ∧ 0<u ∧ 0≤Ccoef ∧ 0≤Csource ∧ Measurable normalizer ∧
      (∀ ν, 0<normalizer ν) ∧
      (∃ D : ℝ, 0≤D ∧ ∀ ν i x, ‖a03SixTensorWeight normalizer ν i x‖≤D) ∧
      (∀ ν j, RectangularComplexWeight (a03SixTensorWeight normalizer ν j)) ∧
      (∀ p, Integrable (a03SixTensorCoefficient (kernels p) normalizer) ∧
        (∫ ν, ‖a03SixTensorCoefficient (kernels p) normalizer ν‖)≤Ccoef) ∧
      ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 2/3≤A → 2/3≤B → 2/3≤H →
        ∀ k : Fin 4 → ℕ, k∈rectangularAFEProductScaleGrid (T^(2+u)) →
        phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
        ∀ σ : MomentShifts, (∀ j, ‖σ j‖≤R) →
        (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
        ∀ v : ℝ, |v|≤θ*Real.log T → ∀ positive : Bool,
        ∃ hvalid : A03NearTensorValid T0 θ κ
          (phaseActualNearTensorData T σ (rawMomentShifts T σ) v A B H k positive),
        let p := (⟨phaseActualNearTensorData T σ (rawMomentShifts T σ) v A B H k positive,hvalid⟩ :
          {p : A03NearTensorData // A03NearTensorValid T0 θ κ p})
        let coeff := a03SixTensorCoefficient (kernels p) normalizer
        let physical := a03EndpointPhysicalTensorSum (a03ActualTensorNormalizedKernel Φ c εkernel)
          positive T A B H σ (rawMomentShifts T σ) v f g k
        let zero := a03EndpointZeroIntegral (kernels p) normalizer T A B H f g k
        (∫ ν, coeff ν*a03EndpointNormalizedSum positive T A B H f g k normalizer ν)=physical ∧
        Integrable (fun ν => coeff ν*a03EndpointNormalizedZeroMode T A B H f g k normalizer ν) ∧
        physical-zero=(∫ ν, coeff ν*a03EndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν) ∧
        ‖physical-zero‖≤(Csource*Ccoef/Real.sqrt (A*B))*phaseSourceMajorant εsource
          (phaseNormalizedScales (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k))) := by
  obtain ⟨T0,kernels,s,u,K,Ccoef,normalizer,bounds,hgraph,hs,hs2,hu,hK,hCcoef,hm,hn,
    hbounds,hW,hd,hcoef,_heq,hfuture⟩ :=
    phase_actual_main_tensor_source_factory ha hab hlen (DivisorProof.inputExponent_pos hεsource (by norm_num : (0:ℝ)<1)) f g hf hg hΦ hΦs hc hc1 hεkernel hκ hθ hR
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgb⟩ := rectangular_supported_profile_bounded g hg
  obtain ⟨Csource,hCsource,hsource⟩ := a03_actual_source_sqrt_superposition
    hinput hεsource hK hF hG f g hfb hgb bounds hbounds normalizer hm hW
  refine ⟨T0,kernels,s,u,Ccoef,Csource,normalizer,hgraph,hs,hs2,hu,hCcoef,hCsource,hm,hn,
    ⟨bounds 0,hbounds 0,fun ν i x => by simpa using hd 0 ν i x⟩,hW,hcoef,?_⟩
  filter_upwards [hfuture] with T hactual
  intro A B H hA hB hH k hk hactive σ hσ hroot v hv positive
  obtain ⟨hvalid,hadm⟩ := hactual A B H hA hB hH k hk hactive σ hσ hroot v hv positive
  let p := (⟨phaseActualNearTensorData T σ (rawMomentShifts T σ) v A B H k positive,hvalid⟩ :
    {p : A03NearTensorData // A03NearTensorValid T0 θ κ p})
  let coeff := a03SixTensorCoefficient (kernels p) normalizer
  have hAp : 0<A := by linarith
  have hBp : 0<B := by linarith
  have hHp : 0<H := by linarith
  have h0 : ∀ ν i x, ‖a03SixTensorWeight normalizer ν i x‖≤bounds 0 := by
    intro ν i x
    simpa using hd 0 ν i x
  have hfinite := a03_actual_tensor_finite_signed_source_reconstruction T A B H c εkernel σ (rawMomentShifts T σ) v k positive f g Φ hBp
    (kernels p) (hgraph p) normalizer hm hn (hcoef p).1 (hbounds 0) h0
  have htransport := a03Six_actual_normalized_source_integral positive T A B H f g k
    normalizer hW coeff hAp hBp hHp
  have hequality : (∫ ν, coeff ν*a03EndpointNormalizedSum positive T A B H f g k normalizer ν)=
      a03EndpointPhysicalTensorSum (a03ActualTensorNormalizedKernel Φ c εkernel)
        positive T A B H σ (rawMomentShifts T σ) v f g k := htransport.symm.trans hfinite
  obtain ⟨hdisc,hbound⟩ := hsource T A B H k coeff (hcoef p).1 hA hB hH hadm positive
  obtain ⟨hzero,hdiff⟩ := a03_actual_tensor_endpoint_difference_sqrt (kernels p) normalizer
    hm (hcoef p).1 (hbounds 0) h0 hW positive T A B H f g k hAp hBp hHp _ hequality hdisc
  have hmajor : 0≤phaseSourceMajorant εsource (phaseNormalizedScales
      (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k))) :=
    phase_source_majorant_nonneg _ _ (fun j => zero_le_one.trans ((hadm 0 (fun _ => false)).1 j))
  refine ⟨hvalid,hequality,hzero,hdiff,?_⟩
  rw [hdiff]
  calc
    _ ≤ (Csource*phaseSourceMajorant εsource (phaseNormalizedScales
        (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k))))/
          Real.sqrt (A*B)*Ccoef := hbound.trans
      (mul_le_mul_of_nonneg_left (hcoef p).2 (by positivity))
    _ = _ := by ring


/-- Genuine dual source endpoint, preserving the reciprocal amplifier
square roots and deriving every source field from the physical factory. -/
theorem a03_actual_dual_tensor_source_endpoint_sqrt
    (hinput : SeparatedQuadraticInput) {a b εsource εkernel c κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hεsource : 0<εsource)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc 1 2)
    (hc : 0<c) (hc1 : c≤1) (hεkernel : 4*c<εkernel)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ T0 : ℝ, ∃ kernels : {p : A03NearTensorData // A03DualNearTensorValid T0 θ κ R p} → SchwartzMap A03SixTensorSpace ℂ,
      ∃ s u Ccoef Csource : ℝ, ∃ normalizer : A03SixTensorSpace → ℝ,
      (∀ p y, kernels p y=a03TensorLogCutoff y*a03ActualDualTensorNormalizedKernel Φ c εkernel p.val y) ∧
      0<s ∧ s<1/2 ∧ 0<u ∧ 0≤Ccoef ∧ 0≤Csource ∧ Measurable normalizer ∧
      (∀ ν, 0<normalizer ν) ∧
      (∃ D : ℝ, 0≤D ∧ ∀ ν i x, ‖a03SixTensorWeight normalizer ν i x‖≤D) ∧
      (∀ ν j, RectangularComplexWeight (a03SixTensorWeight normalizer ν j)) ∧
      (∀ p, Integrable (a03SixTensorCoefficient (kernels p) normalizer) ∧
        (∫ ν, ‖a03SixTensorCoefficient (kernels p) normalizer ν‖)≤Ccoef) ∧
      ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 2/3≤A → 2/3≤B → 2/3≤H →
        ∀ k : Fin 4 → ℕ, k∈rectangularAFEProductScaleGrid (T^(2+u)) →
        phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
        ∀ σ : MomentShifts, (∀ j, ‖σ j‖≤R) →
        (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
        ∀ v : ℝ, |v|≤θ*Real.log T → ∀ positive : Bool,
        ∃ hvalid : A03DualNearTensorValid T0 θ κ R
          (phaseActualNearTensorData T σ (bblrSixShifts (rawMomentShifts T σ) 1) v A B H k positive),
        let p := (⟨phaseActualNearTensorData T σ (bblrSixShifts (rawMomentShifts T σ) 1) v A B H k positive,hvalid⟩ :
          {p : A03NearTensorData // A03DualNearTensorValid T0 θ κ R p})
        let coeff := a03SixTensorCoefficient (kernels p) normalizer
        let physical := a03EndpointPhysicalTensorSum (a03ActualDualTensorNormalizedKernel Φ c εkernel)
          positive T A B H σ (bblrSixShifts (rawMomentShifts T σ) 1) v f g k
        let zero := a03EndpointZeroIntegral (kernels p) normalizer T A B H f g k
        (∫ ν, coeff ν*a03EndpointNormalizedSum positive T A B H f g k normalizer ν)=physical ∧
        Integrable (fun ν => coeff ν*a03EndpointNormalizedZeroMode T A B H f g k normalizer ν) ∧
        physical-zero=(∫ ν, coeff ν*a03EndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν) ∧
        ‖physical-zero‖≤(Csource*Ccoef/Real.sqrt (A*B))*phaseSourceMajorant εsource
          (phaseNormalizedScales (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k))) := by
  obtain ⟨T0,kernels,s,u,K,Ccoef,normalizer,bounds,hgraph,hs,hs2,hu,hK,hCcoef,hm,hn,
    hbounds,hW,hd,hcoef,_heq,hfuture⟩ :=
    phase_actual_dual_tensor_source_factory ha hab hlen (DivisorProof.inputExponent_pos hεsource (by norm_num : (0:ℝ)<1)) f g hf hg hΦ hΦs hc hc1 hεkernel hκ hθ hR
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgb⟩ := rectangular_supported_profile_bounded g hg
  obtain ⟨Csource,hCsource,hsource⟩ := a03_actual_source_sqrt_superposition
    hinput hεsource hK hF hG f g hfb hgb bounds hbounds normalizer hm hW
  refine ⟨T0,kernels,s,u,Ccoef,Csource,normalizer,hgraph,hs,hs2,hu,hCcoef,hCsource,hm,hn,
    ⟨bounds 0,hbounds 0,fun ν i x => by simpa using hd 0 ν i x⟩,hW,hcoef,?_⟩
  filter_upwards [hfuture] with T hactual
  intro A B H hA hB hH k hk hactive σ hσ hroot v hv positive
  obtain ⟨hvalid,hadm⟩ := hactual A B H hA hB hH k hk hactive σ hσ hroot v hv positive
  let p := (⟨phaseActualNearTensorData T σ (bblrSixShifts (rawMomentShifts T σ) 1) v A B H k positive,hvalid⟩ :
    {p : A03NearTensorData // A03DualNearTensorValid T0 θ κ R p})
  let coeff := a03SixTensorCoefficient (kernels p) normalizer
  have hAp : 0<A := by linarith
  have hBp : 0<B := by linarith
  have hHp : 0<H := by linarith
  have h0 : ∀ ν i x, ‖a03SixTensorWeight normalizer ν i x‖≤bounds 0 := by
    intro ν i x
    simpa using hd 0 ν i x
  have hfinite := a03_actual_dual_tensor_finite_signed_source_reconstruction T A B H c εkernel σ (bblrSixShifts (rawMomentShifts T σ) 1) v k positive f g Φ hBp
    (kernels p) (hgraph p) normalizer hm hn (hcoef p).1 (hbounds 0) h0
  have htransport := a03Six_actual_normalized_source_integral positive T A B H f g k
    normalizer hW coeff hAp hBp hHp
  have hequality : (∫ ν, coeff ν*a03EndpointNormalizedSum positive T A B H f g k normalizer ν)=
      a03EndpointPhysicalTensorSum (a03ActualDualTensorNormalizedKernel Φ c εkernel)
        positive T A B H σ (bblrSixShifts (rawMomentShifts T σ) 1) v f g k := htransport.symm.trans hfinite
  obtain ⟨hdisc,hbound⟩ := hsource T A B H k coeff (hcoef p).1 hA hB hH hadm positive
  obtain ⟨hzero,hdiff⟩ := a03_actual_tensor_endpoint_difference_sqrt (kernels p) normalizer
    hm (hcoef p).1 (hbounds 0) h0 hW positive T A B H f g k hAp hBp hHp _ hequality hdisc
  have hmajor : 0≤phaseSourceMajorant εsource (phaseNormalizedScales
      (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k))) :=
    phase_source_majorant_nonneg _ _ (fun j => zero_le_one.trans ((hadm 0 (fun _ => false)).1 j))
  refine ⟨hvalid,hequality,hzero,hdiff,?_⟩
  rw [hdiff]
  calc
    _ ≤ (Csource*phaseSourceMajorant εsource (phaseNormalizedScales
        (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k))))/
          Real.sqrt (A*B)*Ccoef := hbound.trans
      (mul_le_mul_of_nonneg_left (hcoef p).2 (by positivity))
    _ = _ := by ring

end
end Sechstmoment
