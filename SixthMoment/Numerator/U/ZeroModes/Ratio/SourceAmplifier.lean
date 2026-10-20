import SixthMoment.Numerator.U.ZeroModes.Ratio.TensorFamily
import SixthMoment.Numerator.U.ZeroModes.SoftNativeReconstruction

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03SoftSixFourierSourceClasses (ε K : ℝ) (bounds : ℕ→ℝ)
    (normalizer : A03SixTensorSpace→ℝ) (T A B H : ℝ) (f g : ℝ→ℝ) (k : Fin 4→ℕ) : Prop :=
  ∀ ν : A03SixTensorSpace,∀ component : Fin 5→Bool,
    let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
    QuadraticAdmissible ε 1 K bounds (a03SoftSourceOrientedScales q)
      (a03SoftSourceOrientedAlpha q (boundaryActualAlpha T A f k) (a03SixActualBoundaryBeta T B g k ν))
      (a03SoftSourceOrientedBeta q (boundaryActualAlpha T A f k) (a03SixActualBoundaryBeta T B g k ν))
      (rectangularRealComponent (a03SoftSourceOrientedWeights q (a03SixTensorWeight normalizer ν)) component)

def a03SoftEndpointScaledDiscrepancy (positive : Bool) (T A B H : ℝ) (f g : ℝ → ℝ)
    (k : Fin 4 → ℕ) (normalizer : A03SixTensorSpace → ℝ) (ν : A03SixTensorSpace) : ℂ :=
  let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
  rectangularComplexDiscrepancy (a03SoftSourceOrientedSign q positive) (a03SoftSourceOrientedScales q)
    (a03SoftSourceOrientedAlpha q (a03EndpointScaledAlpha T A f k) (a03EndpointScaledBeta T B g k ν))
    (a03SoftSourceOrientedBeta q (a03EndpointScaledAlpha T A f k) (a03EndpointScaledBeta T B g k ν))
    (a03SoftSourceOrientedWeights q (a03SixTensorWeight normalizer ν))

theorem a03SoftEndpointScaledDiscrepancy_eq (positive : Bool) (T A B H : ℝ)
    (f g : ℝ → ℝ) (k : Fin 4 → ℕ) (normalizer : A03SixTensorSpace → ℝ)
    (ν : A03SixTensorSpace) :
    a03SoftEndpointScaledDiscrepancy positive T A B H f g k normalizer ν=
      ((Real.sqrt A : ℂ)*(Real.sqrt B : ℂ))*
        a03SoftEndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν := by
  let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
  unfold a03SoftEndpointScaledDiscrepancy a03SoftEndpointNormalizedDiscrepancy
    a03SoftEndpointNormalizedSum a03SoftEndpointNormalizedZeroMode
    a03SoftSourceOrientedAlpha a03SoftSourceOrientedBeta
  dsimp only
  change _=(_*_)*rectangularComplexDiscrepancy _ _ _ _ _
  split_ifs
  · exact rectangularComplexDiscrepancy_mul_coefficients
      (a03SoftSourceOrientedSign q positive) (a03SoftSourceOrientedScales q)
      (boundaryActualAlpha T A f k) (a03SixActualBoundaryBeta T B g k ν)
      (a03SoftSourceOrientedWeights q (a03SixTensorWeight normalizer ν))
      (Real.sqrt A : ℂ) (Real.sqrt B : ℂ)
  · have he := rectangularComplexDiscrepancy_mul_coefficients
      (a03SoftSourceOrientedSign q positive) (a03SoftSourceOrientedScales q)
      (a03SixActualBoundaryBeta T B g k ν) (boundaryActualAlpha T A f k)
      (a03SoftSourceOrientedWeights q (a03SixTensorWeight normalizer ν))
      (Real.sqrt B : ℂ) (Real.sqrt A : ℂ)
    rw [mul_comm (Real.sqrt B : ℂ) (Real.sqrt A : ℂ)] at he
    exact he

def a03SoftScaledSixFourierSourceClasses (ε K : ℝ) (bounds : ℕ → ℝ)
    (normalizer : A03SixTensorSpace → ℝ) (T A B H : ℝ) (f g : ℝ → ℝ)
    (k : Fin 4 → ℕ) : Prop :=
  ∀ ν : A03SixTensorSpace, ∀ component : Fin 5 → Bool,
    let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
    QuadraticAdmissible ε 1 K bounds (a03SoftSourceOrientedScales q)
      (a03SoftSourceOrientedAlpha q (a03EndpointScaledAlpha T A f k) (a03EndpointScaledBeta T B g k ν))
      (a03SoftSourceOrientedBeta q (a03EndpointScaledAlpha T A f k) (a03EndpointScaledBeta T B g k ν))
      (rectangularRealComponent (a03SoftSourceOrientedWeights q (a03SixTensorWeight normalizer ν)) component)

theorem a03SoftScaledSixFourierSourceClasses_of_actual
    {ε K F G : ℝ} (hε : 0≤ε) (hK : 1≤K) (hF : 0≤F) (hG : 0≤G)
    (T A B H : ℝ) (f g : ℝ → ℝ) (k : Fin 4 → ℕ)
    (hA : 2/3≤A) (hB : 2/3≤B) (hH : 2/3≤H)
    (hf : ∀ x, ‖f x‖≤F) (hg : ∀ x, ‖g x‖≤G)
    (bounds : ℕ → ℝ) (normalizer : A03SixTensorSpace → ℝ)
    (hadm : a03SoftSixFourierSourceClasses ε K bounds normalizer T A B H f g k) :
    a03SoftScaledSixFourierSourceClasses ε (max K (max F G)) bounds normalizer T A B H f g k := by
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
  have hcs := a03_soft_source_oriented_coefficient_supports q _ _ hAs hBs
  have hcb := a03_soft_source_oriented_coefficient_bounds q _ _ L ε hAb hBb
  rcases hadm ν component with ⟨hs,hm,hn,hh,hδ,hl,hr,ho,_hAs,_hBs,_hAb,_hBb,hW,hd⟩
  have hgeo : phaseSourceGeometry ε K (a03SoftSourceOrientedScales q) := by
    exact ⟨hs,hm,hn,hh,by simpa only [Real.rpow_one] using hδ,hl,hr,ho⟩
  rcases phase_source_geometry_mono _ hgeo hKL with ⟨hs',hm',hn',hh',hδ',hl',hr',ho'⟩
  exact ⟨hs',hm',hn',hh',by simpa only [Real.rpow_one] using hδ',hl',hr',ho',
    hcs.1,hcs.2,hcb.1,hcb.2,hW,hd⟩



theorem a03_soft_source_alpha_measurable {Ω : Type*} [MeasurableSpace Ω]
    (q : QuadraticScales) (α β : Ω→ℕ→ℂ)
    (hα : ∀ n,Measurable (fun ν => α ν n)) (hβ : ∀ n,Measurable (fun ν => β ν n)) (n : ℕ) :
    Measurable (fun ν => a03SoftSourceOrientedAlpha q (α ν) (β ν) n) := by
  unfold a03SoftSourceOrientedAlpha
  split_ifs
  · exact hα n
  · exact hβ n

theorem a03_soft_source_beta_measurable {Ω : Type*} [MeasurableSpace Ω]
    (q : QuadraticScales) (α β : Ω→ℕ→ℂ)
    (hα : ∀ n,Measurable (fun ν => α ν n)) (hβ : ∀ n,Measurable (fun ν => β ν n)) (n : ℕ) :
    Measurable (fun ν => a03SoftSourceOrientedBeta q (α ν) (β ν) n) := by
  unfold a03SoftSourceOrientedBeta
  split_ifs
  · exact hβ n
  · exact hα n

theorem a03_soft_source_weights_measurable {Ω : Type*} [MeasurableSpace Ω]
    (q : QuadraticScales) (W : Ω→Fin 5→ℝ→ℂ)
    (hW : ∀ i x,Measurable (fun ν => W ν i x)) (i : Fin 5) (x : ℝ) :
    Measurable (fun ν => a03SoftSourceOrientedWeights q (W ν) i x) := by
  unfold a03SoftSourceOrientedWeights
  split_ifs
  · exact hW i x
  · fin_cases i <;> simp only [phaseSideSwapWeights]
    all_goals first | exact hW 0 x | exact hW 1 x | exact hW 2 x | exact hW 3 x | exact hW 4 x

theorem a03_actual_soft_source_sqrt_superposition
    (hinput : SeparatedQuadraticInput) {ε K F G : ℝ} (hε : 0<ε) (hK : 1≤K)
    (hF : 0≤F) (hG : 0≤G) (f g : ℝ → ℝ)
    (hf : ∀ x, ‖f x‖≤F) (hg : ∀ x, ‖g x‖≤G)
    (bounds : ℕ → ℝ) (hbounds : ∀ j, 0≤bounds j)
    (normalizer : A03SixTensorSpace → ℝ) (hm : Measurable normalizer)
    (hW : ∀ ν j, RectangularComplexWeight (a03SixTensorWeight normalizer ν j)) :
    ∃ C : ℝ, 0≤C ∧ ∀ T A B H k
      (c : A03SixTensorSpace → ℂ), Integrable c →
      2/3≤A → 2/3≤B → 2/3≤H →
      a03SoftSixFourierSourceClasses (DivisorProof.inputExponent ε 1) K bounds normalizer T A B H f g k →
      ∀ positive : Bool,
      Integrable (fun ν => c ν*a03SoftEndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν) ∧
      ‖∫ ν, c ν*a03SoftEndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν‖ ≤
        (C*phaseSourceMajorant ε (a03SoftSourceOrientedScales
          (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k))))/
            Real.sqrt (A*B)*(∫ ν, ‖c ν‖) := by
  let L := max K (max F G)
  have hL : 1≤L := hK.trans (le_max_left _ _)
  obtain ⟨C,hC,hsource⟩ := phase_BBLRv1_integrable_component_source
    hinput hε (by norm_num : (0:ℝ)<1) hL bounds hbounds
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
  have hscaled := a03SoftScaledSixFourierSourceClasses_of_actual (DivisorProof.inputExponent_pos hε (by norm_num)).le hK hF hG
    T A B H f g k hA hB hH hf hg bounds normalizer hadm
  obtain ⟨hscaledInt,hbound⟩ := hsource A03SixTensorSpace volume (a03SoftSourceOrientedScales q)
    (fun ν => a03SoftSourceOrientedAlpha q (α ν) (β ν))
    (fun ν => a03SoftSourceOrientedBeta q (α ν) (β ν))
    (fun ν => a03SoftSourceOrientedWeights q (a03SixTensorWeight normalizer ν)) c hc
    (a03_soft_source_alpha_measurable q α β hα hβ)
    (a03_soft_source_beta_measurable q α β hα hβ)
    (a03_soft_source_weights_measurable q (a03SixTensorWeight normalizer)
      (a03SixTensorWeight_measurable normalizer hm))
    hscaled (fun ν => a03_soft_source_oriented_weights_complex q _ (hW ν)) (a03SoftSourceOrientedSign q positive)
  have heq : (∫ ν, c ν*a03SoftEndpointScaledDiscrepancy positive T A B H f g k normalizer ν)=
      ((Real.sqrt A : ℂ)*(Real.sqrt B : ℂ))*
        ∫ ν, c ν*a03SoftEndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν := by
    simp_rw [a03SoftEndpointScaledDiscrepancy_eq]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all volume fun ν => by ring
  change ‖∫ ν, c ν*a03SoftEndpointScaledDiscrepancy positive T A B H f g k normalizer ν‖≤
    (C*phaseSourceMajorant ε (a03SoftSourceOrientedScales q))*(∫ ν, ‖c ν‖) at hbound
  rw [heq,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg A),Real.norm_of_nonneg (Real.sqrt_nonneg B),
    ← Real.sqrt_mul hAp.le] at hbound
  have hconst : IsUnit ((Real.sqrt A : ℂ)*(Real.sqrt B : ℂ)) :=
    isUnit_iff_ne_zero.mpr (mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hAp).ne')
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hBp).ne'))
  have hdisc : Integrable (fun ν => c ν*a03SoftEndpointNormalizedDiscrepancy positive T A B H f g k normalizer ν) := by
    apply (integrable_const_mul_iff hconst _).mp
    apply hscaledInt.congr
    exact ae_of_all _ fun ν => by
      change c ν*a03SoftEndpointScaledDiscrepancy positive T A B H f g k normalizer ν=_
      rw [a03SoftEndpointScaledDiscrepancy_eq]
      ring
  refine ⟨hdisc,?_⟩
  have hsqrt : 0<Real.sqrt (A*B) := Real.sqrt_pos.mpr (mul_pos hAp hBp)
  calc
    _ ≤ ((C*phaseSourceMajorant ε (a03SoftSourceOrientedScales q))*(∫ ν, ‖c ν‖))/Real.sqrt (A*B) :=
      (le_div_iff₀ hsqrt).mpr (by simpa only [mul_comm] using hbound)
    _ = _ := by ring

end
end SixthMoment
