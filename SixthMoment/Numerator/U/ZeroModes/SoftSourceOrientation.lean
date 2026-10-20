import SixthMoment.Numerator.U.Separation.ShapeActualPowerNear
import SixthMoment.Numerator.U.ZeroModes.SideOrientation

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def a03SoftSourceOrientedScales (q : QuadraticScales) : QuadraticScales :=
  if q.B*q.N₁≤q.A*q.M₁ then q else phaseSideSwapScales q

def a03SoftSourceOrientedAlpha (q : QuadraticScales) (α β : ℕ→ℂ) : ℕ→ℂ :=
  if q.B*q.N₁≤q.A*q.M₁ then α else β

def a03SoftSourceOrientedBeta (q : QuadraticScales) (α β : ℕ→ℂ) : ℕ→ℂ :=
  if q.B*q.N₁≤q.A*q.M₁ then β else α

def a03SoftSourceOrientedWeights (q : QuadraticScales) (W : Fin 5→ℝ→ℂ) : Fin 5→ℝ→ℂ :=
  if q.B*q.N₁≤q.A*q.M₁ then W else phaseSideSwapWeights W

def a03SoftSourceOrientedSign (q : QuadraticScales) (positive : Bool) : Bool :=
  if q.B*q.N₁≤q.A*q.M₁ then positive else !positive

theorem a03_soft_source_oriented_sum (q : QuadraticScales) (positive : Bool)
    (α β : ℕ→ℂ) (W : Fin 5→ℝ→ℂ) :
    rectangularComplexQuadraticSum (a03SoftSourceOrientedSign q positive)
      (a03SoftSourceOrientedScales q) (a03SoftSourceOrientedAlpha q α β)
      (a03SoftSourceOrientedBeta q α β) (a03SoftSourceOrientedWeights q W)=
      rectangularComplexQuadraticSum positive q α β W := by
  unfold a03SoftSourceOrientedSign a03SoftSourceOrientedScales
    a03SoftSourceOrientedAlpha a03SoftSourceOrientedBeta a03SoftSourceOrientedWeights
  split_ifs
  · rfl
  · exact phase_side_swap_quadratic_sum positive q α β W

theorem a03_soft_source_oriented_zero (q : QuadraticScales)
    (α β : ℕ→ℂ) (W : Fin 5→ℝ→ℂ) :
    rectangularComplexZeroMode (a03SoftSourceOrientedScales q)
      (a03SoftSourceOrientedAlpha q α β) (a03SoftSourceOrientedBeta q α β)
      (a03SoftSourceOrientedWeights q W)=rectangularComplexZeroMode q α β W := by
  unfold a03SoftSourceOrientedScales a03SoftSourceOrientedAlpha
    a03SoftSourceOrientedBeta a03SoftSourceOrientedWeights
  split_ifs
  · rfl
  · exact phase_side_swap_complex_zero_mode q α β W

theorem a03_soft_source_oriented_geometry {ε K : ℝ}
    (q : QuadraticScales) (hq : ∀ j,1≤q.size j)
    (hm : q.M₁≤q.M₂*q.mass^ε) (hn : q.N₁≤q.N₂*q.mass^ε)
    (hH : q.H≤K*(q.A*q.B)^(1/2+ε)) (hδ : q.A*q.B≤K*q.M*q.N)
    (h₁ : q.A*q.M≤K*q.B*q.N) (h₂ : q.B*q.N≤K*q.A*q.M) :
    phaseSourceGeometry ε K (a03SoftSourceOrientedScales q) := by
  unfold a03SoftSourceOrientedScales
  split_ifs with ho
  · exact ⟨hq,hm,hn,hH,hδ,h₁,h₂,ho⟩
  · have hqo : ∀ j,1≤(phaseSideSwapScales q).size j := by
      intro j
      fin_cases j <;> simp only [phaseSideSwapScales,QuadraticScales.size]
      all_goals first | exact hq 0 | exact hq 1 | exact hq 2 | exact hq 3 | exact hq 4 | exact hq 5 | exact hq 6
    refine ⟨hqo,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [phase_side_swap_mass]; exact hn
    · rw [phase_side_swap_mass]; exact hm
    · simpa only [phaseSideSwapScales,mul_comm] using hH
    · simpa [phaseSideSwapScales,QuadraticScales.M,QuadraticScales.N,mul_comm,mul_left_comm,mul_assoc] using hδ
    · exact h₂
    · exact h₁
    · exact le_of_lt (lt_of_not_ge ho)

theorem a03_actual_power_near_soft_source_geometry {a b ε : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hε : 0<ε)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∃ s u : ℝ, 0<s ∧ s<1/2 ∧ 0<u ∧ ∀ᶠ T : ℝ in atTop,
      ∀ A B H : ℝ, 2/3≤A → 2/3≤B → 2/3≤H → ∀ k : Fin 4 → ℕ,
      k∈rectangularAFEProductScaleGrid (T^(2+u)) →
      phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
      let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
      q.M₁≤q.M₂*q.mass^ε → q.N₁≤q.N₂*q.mass^ε →
      phaseSourceGeometry ε 32 (a03SoftSourceOrientedScales q) := by
  obtain ⟨ρ,hρ,hρT⟩ := phase_actual_amplifier_product_lengths f g hf hg
  obtain ⟨s,u,hs,hs2,hu,hsu,hslen⟩ := phase_source_auxiliary_exponents ha hab hlen hρ hε
  refine ⟨s,u,hs,hs2,hu,?_⟩
  have hηsmall : ∀ᶠ T : ℝ in atTop, T^(s-1)≤1/2 :=
    ((tendsto_order.1 (tendsto_rpow_neg_atTop (show 0<1-s by linarith))).2
      (1/2) (by norm_num)).mono (fun _ h => by simpa only [neg_sub] using h.le)
  filter_upwards [hρT,phase_near_nontrivial_uniform hslen,hηsmall,
    eventually_ge_atTop (1:ℝ)] with T hρT hnontriv hηsmall hT
  intro A B H hA hB hH k hk hactive
  dsimp only
  intro hmsoft hnsoft
  have hAp : 0<A := by linarith
  have hBp : 0<B := by linarith
  have hHp : 0<H := by linarith
  obtain ⟨p,q0,h,n,positive,hpa,hqb,hw,hh,hrel,hnear⟩ := hactive
  let q := phaseActualScales A B H k
  let tuple := rectangularAFESourceTuple p q0 n h
  have hqp := boundaryActual_scales_pos A B H k hAp hBp hHp
  have hq : ∀ j, 0≤q.size j := fun j => (hqp j).le
  have htuple := phase_actual_source_tuple_support T A B H f g hAp hBp hHp k n p q0 h hpa hqb hw hh
  have htuplepos := phase_actual_source_tuple_positive T A B H f g hAp hBp hHp k n p q0 h hpa hqb hw hh
  have hAB := hρT A B hAp hBp p q0 hpa hqb
  have hABp : 0<q.A*q.B := mul_pos hAp hBp
  have hMN : q.M*q.N≤T^(2+u) := by
    have h := (Finset.mem_filter.mp hk).2
    simpa [q,phaseActualScales,QuadraticScales.M,QuadraticScales.N,Fin.prod_univ_four,mul_assoc] using h
  have hgapshape := phase_near_H_from_product_cutoff hT hε.le hsu.le q hq hAB.1 hMN tuple htuple hnear
  have hnontrivial := hnontriv q hq hABp hAB.2 tuple htuple (htuplepos 6) hnear
  have hcompare := phase_active_near_scales_comparable q hq tuple htuple htuplepos positive hrel hηsmall hnear
  let q' := boundaryEmbeddedScales (boundaryActualFlags k) q
  have hq' : ∀ j, 1≤q'.size j := boundaryActual_embedded_lower_bounds A B H k hA hB hH
  have hH' : q'.H≤32*(q'.A*q'.B)^(1/2+ε) := by
    simpa only [show (4:ℝ)*8=32 by norm_num] using boundaryEmbedded_gap_shape (boundaryActualFlags k) q
      (by norm_num : (0:ℝ)≤8) hε.le hABp hgapshape
  have hn' : q'.A*q'.B≤32*q'.M*q'.N := by
    have h := boundaryEmbedded_nontrivial_range (boundaryActualFlags k) q hnontrivial
    have hp : 0≤q'.M*q'.N := by
      have hM₁ := hq' 2; have hM₂ := hq' 3; have hN₁ := hq' 4; have hN₂ := hq' 5
      norm_num [QuadraticScales.size] at hM₁ hM₂ hN₁ hN₂
      unfold QuadraticScales.M QuadraticScales.N
      positivity
    exact h.trans (by nlinarith)
  have hcomp' := boundaryEmbedded_comparability (boundaryActualFlags k) q hcompare.1 hcompare.2
  exact a03_soft_source_oriented_geometry q' hq' hmsoft hnsoft hH' hn'
    (by simpa [mul_assoc] using hcomp'.1) (by simpa [mul_assoc] using hcomp'.2)

theorem a03_soft_source_oriented_coefficient_supports (q : QuadraticScales) (α β : ℕ→ℂ)
    (hα : ∀ n : ℕ,(n:ℝ)∉Icc q.A (2*q.A) → α n=0)
    (hβ : ∀ n : ℕ,(n:ℝ)∉Icc q.B (2*q.B) → β n=0) :
    (∀ n : ℕ,(n:ℝ)∉Icc (a03SoftSourceOrientedScales q).A (2*(a03SoftSourceOrientedScales q).A) →
      a03SoftSourceOrientedAlpha q α β n=0) ∧
    (∀ n : ℕ,(n:ℝ)∉Icc (a03SoftSourceOrientedScales q).B (2*(a03SoftSourceOrientedScales q).B) →
      a03SoftSourceOrientedBeta q α β n=0) := by
  unfold a03SoftSourceOrientedScales a03SoftSourceOrientedAlpha a03SoftSourceOrientedBeta
  split_ifs
  · exact ⟨hα,hβ⟩
  · exact ⟨hβ,hα⟩

theorem a03_soft_source_oriented_coefficient_bounds (q : QuadraticScales) (α β : ℕ→ℂ)
    (K ε : ℝ) (hα : ∀ n : ℕ,‖α n‖≤K*q.A^ε) (hβ : ∀ n : ℕ,‖β n‖≤K*q.B^ε) :
    (∀ n : ℕ,‖a03SoftSourceOrientedAlpha q α β n‖≤K*(a03SoftSourceOrientedScales q).A^ε) ∧
    (∀ n : ℕ,‖a03SoftSourceOrientedBeta q α β n‖≤K*(a03SoftSourceOrientedScales q).B^ε) := by
  unfold a03SoftSourceOrientedScales a03SoftSourceOrientedAlpha a03SoftSourceOrientedBeta
  split_ifs
  · exact ⟨hα,hβ⟩
  · exact ⟨hβ,hα⟩

theorem a03_soft_source_oriented_weights_complex (q : QuadraticScales) (W : Fin 5→ℝ→ℂ)
    (hW : ∀ i,RectangularComplexWeight (W i)) :
    ∀ i,RectangularComplexWeight (a03SoftSourceOrientedWeights q W i) := by
  unfold a03SoftSourceOrientedWeights
  split_ifs
  · exact hW
  · intro i
    fin_cases i <;> simp only [phaseSideSwapWeights]
    all_goals first | exact hW 0 | exact hW 1 | exact hW 2 | exact hW 3 | exact hW 4

theorem a03_soft_source_oriented_weights_derivatives (q : QuadraticScales) (W : Fin 5→ℝ→ℂ)
    (ε : ℝ) (bounds : ℕ→ℝ)
    (hd : ∀ j i x,‖iteratedDeriv j (W i) x‖≤bounds j*q.mass^ε) :
    ∀ j i x,‖iteratedDeriv j (a03SoftSourceOrientedWeights q W i) x‖≤
      bounds j*(a03SoftSourceOrientedScales q).mass^ε := by
  unfold a03SoftSourceOrientedWeights a03SoftSourceOrientedScales
  split_ifs
  · exact hd
  · rw [phase_side_swap_mass]
    intro j i x
    fin_cases i <;> simp only [phaseSideSwapWeights]
    all_goals first | exact hd j 0 x | exact hd j 1 x | exact hd j 2 x | exact hd j 3 x | exact hd j 4 x

end
end SixthMoment
