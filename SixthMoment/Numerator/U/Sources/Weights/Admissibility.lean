import SixthMoment.Numerator.U.Separation.LogarithmicGapMass
import SixthMoment.Numerator.U.Separation.ShapeAuxiliaryRange
import SixthMoment.Numerator.U.Separation.UnitShapeTransport
import SixthMoment.Numerator.U.Sources.Weights.NormalizedData
import SixthMoment.Numerator.U.Sources.Weights.Support

namespace SixthMoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def phaseActualActiveLogBlock (T A B H : ℝ) (f g : ℝ → ℝ) (k : Fin 4 → ℕ) (r : ℝ) : Prop :=
  ∃ a b h : ℕ, ∃ n : Fin 4 → ℕ, ∃ positive : Bool,
    phaseActualAmplifierCoefficient T f A a≠0 ∧
    phaseActualAmplifierCoefficient T g B b≠0 ∧ rectangularAFESmoothWeight k n≠0 ∧
    rectangularSmoothBlockWeight ((h:ℝ)/H)≠0 ∧
    signedQuadraticRelation positive (rectangularAFESourceTuple a b n h) ∧
    |rectangularGapSign positive*(h:ℝ)/((b:ℝ)*(n 2+1)*(n 3+1))|≤r

theorem phase_logarithmic_gap_power_near {s τ : ℝ} (hs : 0<s) (hτ : 0≤τ) :
    ∀ᶠ T : ℝ in atTop, ∀ r : ℝ, 0≤r → r≤1/2 → T*r≤τ*Real.log T →
      ∀ n : Fin 7 → ℕ, (∀ j, 0<n j) → ∀ positive : Bool,
      signedQuadraticRelation positive n →
      |rectangularGapSign positive*(n 6:ℝ)/((n 1:ℝ)*n 4*n 5)|≤r →
      rectangularNearRelation (T^(s-1)) n := by
  have hl := ((log_pow_isLittleO_rpow 1 hs).const_mul_left (2*τ)).bound
    (by norm_num : (0:ℝ)<1)
  filter_upwards [hl,eventually_ge_atTop (1:ℝ)] with T hlog hT
  intro r hr hr2 hTr n hp positive hrel hx
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hln : 0≤Real.log T := Real.log_nonneg hT
  have hnonneg : 0≤2*τ*Real.log T := by positivity
  have hbound : 2*τ*Real.log T≤T^s := by
    simpa only [pow_one,Real.norm_eq_abs,abs_of_nonneg hnonneg,
      abs_of_nonneg (Real.rpow_nonneg hTp.le _),one_mul] using hlog
  have hwidth : 2*r≤T^(s-1) := by
    rw [Real.rpow_sub hTp,Real.rpow_one]
    apply (le_div_iff₀ hTp).mpr
    nlinarith
  have hQ : 0<rectangularNearRightProduct n := by
    unfold rectangularNearRightProduct
    exact_mod_cast Nat.mul_pos (Nat.mul_pos (hp 1) (hp 4)) (hp 5)
  have hsign : |rectangularGapSign positive|=1 := by
    cases positive <;> norm_num [rectangularGapSign]
  have hgap : (n 6:ℝ)≤r*rectangularNearRightProduct n := by
    change |rectangularGapSign positive*(n 6:ℝ)/rectangularNearRightProduct n|≤r at hx
    rw [abs_div,abs_mul,hsign,one_mul,abs_of_nonneg (Nat.cast_nonneg _),abs_of_pos hQ] at hx
    exact (div_le_iff₀ hQ).mp hx
  have hn := phase_signed_relative_gap_near positive n hQ hr hr2 hrel hgap
  exact hn.trans (mul_le_mul_of_nonneg_right hwidth (Real.sqrt_nonneg _))

theorem phase_actual_logarithmic_source_admissibility {a b ε κ θ τ : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2)
    (hε : 0<ε) (hκ : 0≤κ) (hθ : 0≤θ) (hτ : 0≤τ)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∃ s u K : ℝ, ∃ bounds : ℕ → ℝ, 0<s ∧ s<1/2 ∧ 0<u ∧ 1≤K ∧
      (∀ j, 0≤bounds j) ∧ ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ,
      2/3≤A → 2/3≤B → 2/3≤H → ∀ k : Fin 4 → ℕ,
      k∈rectangularAFEProductScaleGrid (T^(2+u)) →
      ∀ r : ℝ, 0≤r → r≤1/2 → T*r≤τ*Real.log T →
      phaseActualActiveLogBlock T A B H f g k r → ∀ l : ℕ, (l:ℝ)≤κ*Real.log T →
      ∀ α : MomentShifts, (∀ i, ‖α i‖≤1/4) → ∀ c : ℝ, 0≤c → c≤1 →
      ∀ v : ℝ, |v|≤θ*Real.log T → ∀ component : Fin 5 → Bool,
      QuadraticAdmissible ε 1 K bounds
        (phaseNormalizedScales (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)))
        (phaseNormalizedAlpha (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k))
          (boundaryActualAlpha T A f k) (boundaryActualBeta T A B H g k l))
        (phaseNormalizedBeta (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k))
          (boundaryActualAlpha T A f k) (boundaryActualBeta T A B H g k l))
        (rectangularRealComponent (phaseNormalizedWeights
          (boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k))
          (phaseFiveWeights α ((c:ℂ)+(v:ℂ)*I) l)) component) := by
  obtain ⟨ρ,hρ,hρT⟩ := phase_actual_amplifier_product_lengths f g hf hg
  obtain ⟨s,u,hs,hs2,hu,hsu,hslen⟩ := phase_source_auxiliary_exponents ha hab hlen hρ hε
  obtain ⟨F,G,hF,hG,hFG⟩ := boundaryActual_coefficient_families f g hf hg
  obtain ⟨bounds,hbounds,hderiv⟩ := phaseFiveWeights_logarithmic_active_mass_bounds hε hκ hθ hτ
  let K : ℝ := max 32 (max F G)
  have hK32 : 32≤K := le_max_left _ _
  have hFK : F≤K := (le_max_left F G).trans (le_max_right _ _)
  have hGK : G≤K := (le_max_right F G).trans (le_max_right _ _)
  have hK : 0≤K := by linarith
  refine ⟨s,u,K,bounds,hs,hs2,hu,by linarith,hbounds,?_⟩
  have hηsmall : ∀ᶠ T : ℝ in atTop, T^(s-1)≤1/2 :=
    ((tendsto_order.1 (tendsto_rpow_neg_atTop (show 0<1-s by linarith))).2
      (1/2) (by norm_num)).mono (fun _ h => by simpa only [neg_sub] using h.le)
  filter_upwards [hρT,hderiv,phase_near_nontrivial_uniform hslen,
    phase_logarithmic_gap_power_near hs hτ,hηsmall,eventually_ge_atTop (1:ℝ)]
    with T hρT hderiv hnontriv hlognear hηsmall hT
  intro A B H hA hB hH k hk r hr hr2 hTr hactive l hl α hα c hc hc1 v hv component
  have hAp : 0<A := by linarith
  have hBp : 0<B := by linarith
  have hHp : 0<H := by linarith
  obtain ⟨p,q0,h,n,positive,hpa,hqb,hw,hh,hrel,hgap⟩ := hactive
  let q := phaseActualScales A B H k
  let tuple := rectangularAFESourceTuple p q0 n h
  have hqp := boundaryActual_scales_pos A B H k hAp hBp hHp
  have hq : ∀ j, 0≤q.size j := fun j => (hqp j).le
  have htuple := phase_actual_source_tuple_support T A B H f g hAp hBp hHp k n p q0 h hpa hqb hw hh
  have htuplepos := phase_actual_source_tuple_positive T A B H f g hAp hBp hHp k n p q0 h hpa hqb hw hh
  have htupleidx := phase_actual_source_tuple_index T A B H f g hAp hBp hHp k n p q0 h hpa hqb hw hh
  have hx : |rectangularGapSign positive*(tuple 6:ℝ)/((tuple 1:ℝ)*tuple 4*tuple 5)|≤r := by
    simpa [tuple,rectangularAFESourceTuple] using hgap
  have hnear := hlognear r hr hr2 hTr tuple htuplepos positive hrel hx
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
  have hH' : q'.H≤K*(q'.A*q'.B)^(1/2+ε) := by
    have h := boundaryEmbedded_gap_shape (boundaryActualFlags k) q (by norm_num : (0:ℝ)≤8) hε.le hABp hgapshape
    have hA' := hq' 0; have hB' := hq' 1
    norm_num [QuadraticScales.size] at hA' hB'
    have hAB' : 0≤q'.A*q'.B := by positivity
    exact h.trans (mul_le_mul_of_nonneg_right (show (4:ℝ)*8≤K by norm_num; exact hK32)
      (Real.rpow_nonneg hAB' _))
  have hn' : q'.A*q'.B≤K*q'.M*q'.N := by
    have h := boundaryEmbedded_nontrivial_range (boundaryActualFlags k) q hnontrivial
    have hp : 0≤q'.M*q'.N := by
      have hM₁ := hq' 2; have hM₂ := hq' 3; have hN₁ := hq' 4; have hN₂ := hq' 5
      norm_num [QuadraticScales.size] at hM₁ hM₂ hN₁ hN₂
      unfold QuadraticScales.M QuadraticScales.N
      positivity
    exact h.trans (by have := mul_le_mul_of_nonneg_right (show (4:ℝ)≤K by linarith) hp; simpa [mul_assoc] using this)
  have hcomp' := boundaryEmbedded_comparability (boundaryActualFlags k) q hcompare.1 hcompare.2
  have hA'b : ∀ m : ℕ, ‖boundaryActualAlpha T A f k m‖≤K*q'.A^ε := by
    intro m
    have hA' : 1≤q'.A := by simpa [QuadraticScales.size] using hq' 0
    exact ((hFG T A B H hAp hBp k l m).1.trans hFK).trans
      (le_mul_of_one_le_right hK (Real.one_le_rpow hA' hε.le))
  have hB'b : ∀ m : ℕ, ‖boundaryActualBeta T A B H g k l m‖≤K*q'.B^ε := by
    intro m
    have hB' : 1≤q'.B := by simpa [QuadraticScales.size] using hq' 1
    exact ((hFG T A B H hAp hBp k l m).2.trans hGK).trans
      (le_mul_of_one_le_right hK (Real.one_le_rpow hB' hε.le))
  have hd := hderiv r hr hr2 hTr q hq ⟨tuple,htupleidx,positive,hrel,hx⟩ l hl α hα c hc hc1 v hv
  have hmass : 0≤q.mass := by
    unfold q phaseActualScales QuadraticScales.mass QuadraticScales.M QuadraticScales.N
    have h0 := boundaryActual_scale_pos (k 0); have h1 := boundaryActual_scale_pos (k 1)
    have h2 := boundaryActual_scale_pos (k 2); have h3 := boundaryActual_scale_pos (k 3)
    positivity
  have hd' := boundaryEmbedded_derivative_bounds (boundaryActualFlags k) q _ hε.le hmass bounds hbounds hd
  apply phase_normalized_source_admissible hε.le q' hq' hH' hn'
    (hcomp'.1.trans ?_) (hcomp'.2.trans ?_) _ _
    (boundaryActual_alpha_support T A B H f k hAp)
    (boundaryActual_beta_support T A B H g k hBp l) hA'b hB'b
    _ (phaseFiveWeights_complexWeight α _ l) bounds hd' component
  · have hp : 0≤q'.B*q'.N := by
      have h := hq' 1; have h1 := hq' 4; have h2 := hq' 5
      norm_num [QuadraticScales.size] at h h1 h2
      unfold QuadraticScales.N
      positivity
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right hK32 hp
  · have hp : 0≤q'.A*q'.M := by
      have h := hq' 0; have h1 := hq' 2; have h2 := hq' 3
      norm_num [QuadraticScales.size] at h h1 h2
      unfold QuadraticScales.M
      positivity
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right hK32 hp

end
end SixthMoment
