import Sechstmoment.Numerator.U.Separation.SeparatedBlock

namespace Sechstmoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem phase_signed_relative_gap_near (positive : Bool) (n : Fin 7 → ℕ)
    (hQ : 0<rectangularNearRightProduct n) {r : ℝ} (hr : 0≤r) (hr2 : r≤1/2)
    (hrel : signedQuadraticRelation positive n)
    (hgap : (n 6:ℝ)≤r*rectangularNearRightProduct n) : rectangularNearRelation (2*r) n := by
  let P := rectangularNearLeftProduct n
  let Q := rectangularNearRightProduct n
  have hPQ : |P-Q|=(n 6:ℝ) := rectangular_signed_relation_abs_gap positive n hrel
  have hP : 0≤P := by dsimp [P,rectangularNearLeftProduct]; positivity
  have hPQ0 : 0≤P*Q := mul_nonneg hP hQ.le
  have hlower : Q/2≤P := by
    have he := le_abs_self (Q-P)
    rw [abs_sub_comm,hPQ] at he
    have hb := mul_le_mul_of_nonneg_right hr2 hQ.le
    change (n 6:ℝ)≤r*Q at hgap
    linarith
  have hroot : Q/2≤Real.sqrt (P*Q) := by
    have hmul := mul_le_mul_of_nonneg_right hlower hQ.le
    have hsq := Real.sq_sqrt hPQ0
    have hn := Real.sqrt_nonneg (P*Q)
    nlinarith
  unfold rectangularNearRelation
  rw [rectangular_near_tuple_mass]
  change (n 6:ℝ)≤(2*r)*Real.sqrt (P*Q)
  have he := mul_le_mul_of_nonneg_left hroot hr
  change (n 6:ℝ)≤r*Q at hgap
  nlinarith

private theorem logarithmic_ratio_sqrt_small {θ : ℝ} (hθ : 0≤θ) :
    ∀ᶠ T : ℝ in atTop, ∀ r : ℝ, 0≤r → T*r≤θ*Real.log T →
      2*r≤1/(8*Real.sqrt T) := by
  have hl := ((log_pow_isLittleO_rpow 1 (by norm_num : (0:ℝ)<1/2)).const_mul_left
    (16*θ)).bound (by norm_num : (0:ℝ)<1)
  filter_upwards [hl,eventually_ge_atTop (1:ℝ)] with T hlog hT
  intro r hr hTr
  have hTpos : 0<T := zero_lt_one.trans_le hT
  have hlogpos : 0≤Real.log T := Real.log_nonneg hT
  have hnonneg : 0≤16*θ*Real.log T := mul_nonneg (mul_nonneg (by norm_num) hθ) hlogpos
  have he : 16*θ*Real.log T≤Real.sqrt T := by
    simpa only [pow_one,Real.norm_eq_abs,abs_of_nonneg hnonneg,
      abs_of_nonneg (Real.rpow_nonneg hTpos.le _),one_mul,Real.sqrt_eq_rpow] using hlog
  have hb : 16*T*r≤Real.sqrt T := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg T)
  have hsq := Real.sq_sqrt hTpos.le
  have he' : (16*r*Real.sqrt T)*T≤1*T := by nlinarith
  have hc := (mul_le_mul_iff_left₀ hTpos).mp (by simpa only [mul_comm] using he')
  apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<8) (Real.sqrt_pos.mpr hTpos))).mpr
  nlinarith

theorem phase_logarithmic_signed_source_mass {θ : ℝ} (hθ : 0≤θ) :
    ∀ᶠ T : ℝ in atTop, ∀ r : ℝ, 0≤r → r≤1/2 → T*r≤θ*Real.log T →
      ∀ q : QuadraticScales, (∀ j, 0≤q.size j) → ∀ n : Fin 7 → ℕ,
      n∈quadraticIndexSet q → ∀ positive : Bool, signedQuadraticRelation positive n →
      |rectangularGapSign positive*(n 6:ℝ)/((n 1:ℝ)*n 4*n 5)|≤r → T≤q.mass := by
  filter_upwards [logarithmic_ratio_sqrt_small hθ,eventually_gt_atTop (0:ℝ)] with T hm hT
  intro r hr hr2 hTr q hq n hn positive hrel hx
  have hp (j : Fin 7) : 0<n j := by
    have hj := (Fintype.mem_piFinset.mp hn) j
    exact lt_of_lt_of_le (by norm_num : 0<1) (Finset.mem_Icc.mp hj).1
  have hQ : 0<rectangularNearRightProduct n := by
    unfold rectangularNearRightProduct
    exact_mod_cast Nat.mul_pos (Nat.mul_pos (hp 1) (hp 4)) (hp 5)
  have hsign : |rectangularGapSign positive|=1 := by
    cases positive <;> norm_num [rectangularGapSign]
  have hgap : (n 6:ℝ)≤r*rectangularNearRightProduct n := by
    change |rectangularGapSign positive*(n 6:ℝ)/rectangularNearRightProduct n|≤r at hx
    rw [abs_div,abs_mul,hsign,one_mul,abs_of_nonneg (Nat.cast_nonneg _),abs_of_pos hQ] at hx
    exact (div_le_iff₀ hQ).mp hx
  exact rectangular_near_source_mass_lower hT (by positivity) (hm r hr hTr) q hq n hn (hp 6)
    (phase_signed_relative_gap_near positive n hQ hr hr2 hrel hgap)

theorem phaseFiveWeights_logarithmic_active_mass_bounds {ε κ θ τ : ℝ}
    (hε : 0<ε) (hκ : 0≤κ) (hθ : 0≤θ) (hτ : 0≤τ) :
    ∃ B : ℕ → ℝ, (∀ j, 0≤B j) ∧ ∀ᶠ T : ℝ in atTop,
      ∀ r : ℝ, 0≤r → r≤1/2 → T*r≤τ*Real.log T →
      ∀ q : QuadraticScales, (∀ j, 0≤q.size j) →
      (∃ n : Fin 7 → ℕ, n∈quadraticIndexSet q ∧ ∃ positive : Bool,
        signedQuadraticRelation positive n ∧
        |rectangularGapSign positive*(n 6:ℝ)/((n 1:ℝ)*n 4*n 5)|≤r) →
      ∀ k : ℕ, (k:ℝ)≤κ*Real.log T → ∀ α : MomentShifts, (∀ i, ‖α i‖≤1/4) →
      ∀ c : ℝ, 0≤c → c≤1 → ∀ v : ℝ, |v|≤θ*Real.log T → ∀ j i x,
      ‖iteratedDeriv j (phaseFiveWeights α ((c:ℂ)+(v:ℂ)*I) k i) x‖≤B j*q.mass^ε := by
  obtain ⟨B,hB,hb⟩ := phaseFiveWeights_uniform_logarithmic_derivative_bounds hε hκ hθ
  refine ⟨B,hB,?_⟩
  filter_upwards [phase_logarithmic_signed_source_mass hτ,eventually_ge_atTop (1:ℝ)] with T hm hT
  intro r hr hr2 hTr q hq hactive k hk α hα c hc hc1 v hv j i x
  obtain ⟨n,hn,positive,hrel,hx⟩ := hactive
  have hmass := hm r hr hr2 hTr q hq n hn positive hrel hx
  exact (hb T hT k hk α hα c hc hc1 v hv j i x).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (zero_le_one.trans hT) hmass hε.le) (hB j))

end
end Sechstmoment
