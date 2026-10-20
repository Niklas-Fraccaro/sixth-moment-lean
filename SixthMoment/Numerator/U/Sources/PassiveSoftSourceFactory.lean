import SixthMoment.Numerator.U.Sources.PassiveNativeSourceGeometry

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem a03Six_actual_passive_power_near_soft_source_admissibility {ι : Type*} {a b ε : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hε : 0<ε)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (kernels : ι → SchwartzMap A03SixTensorSpace ℂ)
    (hseminorm : ∀ p j : ℕ, ∃ C : ℝ, 0≤C ∧ ∀ i,
      SchwartzMap.seminorm ℂ p j (kernels i)≤C) :
    ∃ s u K C : ℝ, ∃ normalizer : A03SixTensorSpace → ℝ, ∃ bounds : ℕ → ℝ,
      0<s ∧ s<1/2 ∧ 0<u ∧ 1≤K ∧ 0≤C ∧ Measurable normalizer ∧
      (∀ ν, 0<normalizer ν) ∧ (∀ j, 0≤bounds j) ∧
      (∀ ν j, RectangularComplexWeight (a03SixTensorWeight normalizer ν j)) ∧
      (∀ j ν i x, ‖iteratedDeriv j (a03SixTensorWeight normalizer ν i) x‖≤bounds j) ∧
      (∀ i, Integrable (a03SixTensorCoefficient (kernels i) normalizer) ∧
        (∫ ν, ‖a03SixTensorCoefficient (kernels i) normalizer ν‖)≤C) ∧
      (∀ i (x : Fin 6 → ℝ), 0<x 0 →
        (∏ j : Fin 5, (rectangularSmoothBlockWeight (x j.succ):ℂ))*
          kernels i (a03SixTensorLogPoint x)=
          ∫ ν, a03SixTensorCoefficient (kernels i) normalizer ν*
            ((x 0:ℂ)^a03SixTensorExponent ν 0*
              ∏ j, a03SixTensorWeight normalizer ν j (x j.succ))) ∧
      ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 2/3≤A → 2/3≤B → 2/3≤H →
        ∀ k : Fin 4 → ℕ, k∈rectangularAFEProductScaleGrid (T^(2+u)) →
        A03ActualPassiveNearZeroBlock T A B H (T^(s-1)) f g k →
        let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
        q.M₁≤q.M₂*q.mass^ε → q.N₁≤q.N₂*q.mass^ε →
        ∀ ν : A03SixTensorSpace, ∀ component : Fin 5 → Bool,
        let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
        QuadraticAdmissible ε 1 K bounds (a03SoftSourceOrientedScales q)
          (a03SoftSourceOrientedAlpha q (boundaryActualAlpha T A f k) (a03SixActualBoundaryBeta T B g k ν))
          (a03SoftSourceOrientedBeta q (boundaryActualAlpha T A f k) (a03SixActualBoundaryBeta T B g k ν))
          (rectangularRealComponent (a03SoftSourceOrientedWeights q (a03SixTensorWeight normalizer ν)) component) := by
  obtain ⟨s,u,hs,hs2,hu,hgeometry⟩ := a03_actual_passive_power_near_soft_source_geometry ha hab hlen hε f g hf hg
  obtain ⟨normalizer,bounds,C,hm,hn,hbounds,hC,hW,hd,hCoeff,hExact⟩ :=
    a03SixTensor_uniform_separation kernels hseminorm
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgb⟩ := rectangular_supported_profile_bounded g hg
  let K : ℝ := max 32 (max F G)
  have hK32 : 32≤K := le_max_left _ _
  have hFK : F≤K := (le_max_left F G).trans (le_max_right _ _)
  have hGK : G≤K := (le_max_right F G).trans (le_max_right _ _)
  have hK : 0≤K := by linarith
  refine ⟨s,u,K,C,normalizer,bounds,hs,hs2,hu,by linarith,hC,hm,hn,hbounds,hW,hd,hCoeff,hExact,?_⟩
  filter_upwards [hgeometry] with T hgeometry
  intro A B H hA hB hH k hk hactive
  dsimp only
  intro hmsoft hnsoft ν component
  have hAp : 0<A := by linarith
  have hBp : 0<B := by linarith
  let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
  have hq : ∀ j, 1≤q.size j := boundaryActual_embedded_lower_bounds A B H k hA hB hH
  have hsgeo := phase_source_geometry_mono _ (hgeometry A B H hA hB hH k hk hactive hmsoft hnsoft) hK32
  have hAs := boundaryActual_alpha_support T A B H f k hAp
  have hBs := a03SixActualBoundaryBeta_support T A B H g k ν hBp
  have hAb : ∀ n : ℕ, ‖boundaryActualAlpha T A f k n‖≤K*q.A^ε := by
    intro n
    have hA1 : 1≤q.A := by simpa [QuadraticScales.size] using hq 0
    exact ((boundaryActual_alpha_norm T A f k hAp hF hfb n).trans hFK).trans
      (le_mul_of_one_le_right hK (Real.one_le_rpow hA1 hε.le))
  have hBb : ∀ n : ℕ, ‖a03SixActualBoundaryBeta T B g k ν n‖≤K*q.B^ε := by
    intro n
    have hB1 : 1≤q.B := by simpa [QuadraticScales.size] using hq 1
    exact ((a03SixActualBoundaryBeta_norm T B g k ν hBp hG hgb n).trans hGK).trans
      (le_mul_of_one_le_right hK (Real.one_le_rpow hB1 hε.le))
  have hcs := a03_soft_source_oriented_coefficient_supports q _ _ hAs hBs
  have hcb := a03_soft_source_oriented_coefficient_bounds q _ _ K ε hAb hBb
  have hmass := phase_source_mass_ge_one q hq
  have hpow : 1≤q.mass^ε := Real.one_le_rpow hmass hε.le
  have hwd : ∀ j i x, ‖iteratedDeriv j (a03SixTensorWeight normalizer ν i) x‖≤bounds j*q.mass^ε := by
    intro j i x
    exact (hd j ν i x).trans (le_mul_of_one_le_right (hbounds j) hpow)
  have hnd := a03_soft_source_oriented_weights_derivatives q _ ε bounds hwd
  exact phase_geometry_admissible_complex_components _ hsgeo _ _ hcs.1 hcs.2 hcb.1 hcb.2
    _ (a03_soft_source_oriented_weights_complex q _ (hW ν)) bounds hnd component

end
end SixthMoment
