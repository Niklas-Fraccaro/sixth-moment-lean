import Sechstmoment.Numerator.U.Sources.Weights.Admissibility

namespace Sechstmoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def phaseSourceGeometry (ε K : ℝ) (q : QuadraticScales) : Prop :=
  (∀ j, 1≤q.size j) ∧ q.M₁≤q.M₂*q.mass^ε ∧ q.N₁≤q.N₂*q.mass^ε ∧
    q.H≤K*(q.A*q.B)^(1/2+ε) ∧ q.A*q.B≤K*q.M*q.N ∧
    q.A*q.M≤K*q.B*q.N ∧ q.B*q.N≤K*q.A*q.M ∧ q.B*q.N₁≤q.A*q.M₁

def phaseActualActiveNearBlock (T A B H η : ℝ) (f g : ℝ → ℝ) (k : Fin 4 → ℕ) : Prop :=
  ∃ a b h : ℕ, ∃ n : Fin 4 → ℕ, ∃ positive : Bool,
    phaseActualAmplifierCoefficient T f A a≠0 ∧
    phaseActualAmplifierCoefficient T g B b≠0 ∧ rectangularAFESmoothWeight k n≠0 ∧
    rectangularSmoothBlockWeight ((h:ℝ)/H)≠0 ∧
    signedQuadraticRelation positive (rectangularAFESourceTuple a b n h) ∧
    rectangularNearRelation η (rectangularAFESourceTuple a b n h)

theorem phase_normalized_geometry {ε K : ℝ} (hε : 0≤ε)
    (q : QuadraticScales) (hq : ∀ j, 1≤q.size j)
    (hH : q.H≤K*(q.A*q.B)^(1/2+ε)) (hδ : q.A*q.B≤K*q.M*q.N)
    (h₁ : q.A*q.M≤K*q.B*q.N) (h₂ : q.B*q.N≤K*q.A*q.M) :
    phaseSourceGeometry ε K (phaseNormalizedScales q) := by
  have hs := phase_normalized_scale_bounds q hq
  have hi := phase_normalized_invariants q
  have hc := phase_normalized_comparability q (by simpa [mul_assoc] using h₁)
    (by simpa [mul_assoc] using h₂)
  have hm : 1≤(phaseNormalizedScales q).mass^ε :=
    Real.one_le_rpow (phase_source_mass_ge_one _ hs.1) hε
  have hm₂ : 0≤(phaseNormalizedScales q).M₂ := by
    have h := hs.1 3
    norm_num [QuadraticScales.size] at h
    linarith
  have hn₂ : 0≤(phaseNormalizedScales q).N₂ := by
    have h := hs.1 5
    norm_num [QuadraticScales.size] at h
    linarith
  refine ⟨hs.1,hs.2.1.trans (le_mul_of_one_le_right hm₂ hm),
    hs.2.2.1.trans (le_mul_of_one_le_right hn₂ hm),?_,?_,?_,?_,hs.2.2.2⟩
  · rw [hi.1,hi.2.2.1]
    exact hH
  · rw [hi.1]
    simpa [mul_assoc,hi.2.1] using hδ
  · simpa [mul_assoc] using hc.1
  · simpa [mul_assoc] using hc.2

/-- All structural source hypotheses hold on the full small-power near
range. The genuine profile support and retained grid provide every bound;
the result does not restrict the relative gap to log(T)/T. -/
theorem phase_actual_power_near_source_geometry {a b ε : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hε : 0<ε)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∃ s u : ℝ, 0<s ∧ s<1/2 ∧ 0<u ∧ ∀ᶠ T : ℝ in atTop,
      ∀ A B H : ℝ, 2/3≤A → 2/3≤B → 2/3≤H → ∀ k : Fin 4 → ℕ,
      k∈rectangularAFEProductScaleGrid (T^(2+u)) →
      phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
      phaseSourceGeometry ε 32 (phaseNormalizedScales
        (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k))) := by
  obtain ⟨ρ,hρ,hρT⟩ := phase_actual_amplifier_product_lengths f g hf hg
  obtain ⟨s,u,hs,hs2,hu,hsu,hslen⟩ := phase_source_auxiliary_exponents ha hab hlen hρ hε
  refine ⟨s,u,hs,hs2,hu,?_⟩
  have hηsmall : ∀ᶠ T : ℝ in atTop, T^(s-1)≤1/2 :=
    ((tendsto_order.1 (tendsto_rpow_neg_atTop (show 0<1-s by linarith))).2
      (1/2) (by norm_num)).mono (fun _ h => by simpa only [neg_sub] using h.le)
  filter_upwards [hρT,phase_near_nontrivial_uniform hslen,hηsmall,
    eventually_ge_atTop (1:ℝ)] with T hρT hnontriv hηsmall hT
  intro A B H hA hB hH k hk hactive
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
  exact phase_normalized_geometry hε.le q' hq' hH' hn'
    (by simpa [mul_assoc] using hcomp'.1) (by simpa [mul_assoc] using hcomp'.2)

/-- The source constant may be enlarged uniformly. -/
theorem phase_source_geometry_mono {ε K L : ℝ} (q : QuadraticScales)
    (h : phaseSourceGeometry ε K q) (hKL : K≤L) : phaseSourceGeometry ε L q := by
  rcases h with ⟨hs,hm,hn,hh,hδ,hl,hr,ho⟩
  have hA := hs 0; have hB := hs 1; have hM₁ := hs 2; have hM₂ := hs 3
  have hN₁ := hs 4; have hN₂ := hs 5
  norm_num [QuadraticScales.size] at hA hB hM₁ hM₂ hN₁ hN₂
  have hpAB : 0≤q.A*q.B := by positivity
  have hA0 : 0≤q.A := by linarith
  have hB0 : 0≤q.B := by linarith
  have hpM : 0≤q.M := by unfold QuadraticScales.M; positivity
  have hpN : 0≤q.N := by unfold QuadraticScales.N; positivity
  refine ⟨hs,hm,hn,hh.trans (mul_le_mul_of_nonneg_right hKL (Real.rpow_nonneg hpAB _)),
    hδ.trans ?_,hl.trans ?_,hr.trans ?_,ho⟩
  all_goals nlinarith [mul_le_mul_of_nonneg_right hKL (mul_nonneg hpM hpN),
    mul_le_mul_of_nonneg_right hKL (mul_nonneg hB0 hpN),
    mul_le_mul_of_nonneg_right hKL (mul_nonneg hA0 hpM)]

theorem phase_geometry_admissible_complex_components {ε K : ℝ}
    (q : QuadraticScales) (h : phaseSourceGeometry ε K q) (A B : ℕ → ℂ)
    (hAs : ∀ n : ℕ, (n:ℝ)∉Icc q.A (2*q.A) → A n=0)
    (hBs : ∀ n : ℕ, (n:ℝ)∉Icc q.B (2*q.B) → B n=0)
    (hAb : ∀ n : ℕ, ‖A n‖≤K*q.A^ε) (hBb : ∀ n : ℕ, ‖B n‖≤K*q.B^ε)
    (W : Fin 5 → ℝ → ℂ) (hW : ∀ i, RectangularComplexWeight (W i))
    (bounds : ℕ → ℝ) (hd : ∀ j i x, ‖iteratedDeriv j (W i) x‖≤bounds j*q.mass^ε)
    (component : Fin 5 → Bool) :
    QuadraticAdmissible ε 1 K bounds q A B (rectangularRealComponent W component) := by
  rcases h with ⟨hs,hm,hn,hh,hδ,hl,hr,ho⟩
  refine ⟨hs,hm,hn,hh,by simpa only [Real.rpow_one] using hδ,hl,hr,ho,hAs,hBs,hAb,hBb,
    rectangular_component_smooth _ hW component,?_⟩
  intro j i x
  exact (rectangular_component_derivative_norm_le _ hW component j i x).trans (hd j i x)

end
end Sechstmoment
