import SixthMoment.Numerator.U.Separation.NearMellinWeights

namespace SixthMoment
open Complex Real Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

private theorem positive_mellin_derivative_bounds :
    ∃ B : ℕ → ℝ, (∀ j, 0≤B j) ∧ ∀ j (k : ℕ), ∀ x : ℝ,
      ‖iteratedDeriv j (rectangularMellinBlockWeight (k:ℂ)) x‖≤B j*(1+(k:ℝ))^j*(2:ℝ)^k := by
  obtain ⟨C,hC,hb⟩ := rectangularSmoothBlockWeight_derivative_bounds
  let B : ℕ → ℝ := fun j => ∑ i∈Finset.range (j+1),
    (j.choose i : ℝ)*C i*((j-i:ℕ)+1 : ℝ)^(j-i)
  have hB (j : ℕ) : 0≤B j := by
    dsimp [B]
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC i)) (by positivity)
  refine ⟨B,hB,?_⟩
  intro j k x
  by_cases hx : x∈Icc (1:ℝ) 2
  · have hxpos : 0<x := zero_lt_one.trans_le hx.1
    have hpow (n : ℕ) : ‖(x:ℂ)^((k:ℂ)-(n:ℂ))‖≤(2:ℝ)^k := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
      simp only [Complex.sub_re,Complex.natCast_re]
      calc
        _ ≤ x^(k:ℝ) := Real.rpow_le_rpow_of_exponent_le hx.1
          (sub_le_self _ (Nat.cast_nonneg n))
        _ = x^k := Real.rpow_natCast x k
        _ ≤ (2:ℝ)^k := pow_le_pow_left₀ hxpos.le hx.2 k
    have hp (i : ℕ) (_hi : i∈Finset.range (j+1)) :
        ‖(j.choose i : ℂ)*((iteratedDeriv i rectangularSmoothBlockWeight x : ℝ) : ℂ)*
          (mellinFallingCoefficient (j-i) (k:ℂ)*(x:ℂ)^((k:ℂ)-((j-i:ℕ):ℂ)))‖≤
        ((j.choose i : ℝ)*C i*((j-i:ℕ)+1 : ℝ)^(j-i))*(1+(k:ℝ))^j*(2:ℝ)^k := by
      rw [norm_mul,norm_mul,norm_mul,Complex.norm_natCast,Complex.norm_real]
      calc
        _ ≤ ((j.choose i : ℝ)*C i)*
            ((((j-i:ℕ):ℝ)+1)^(j-i)*(1+(k:ℝ))^(j-i)*(2:ℝ)^k) := by
          gcongr
          · exact mul_nonneg (Nat.cast_nonneg _) (hC i)
          · exact hb i x
          · simpa only [Complex.norm_natCast] using mellinFallingCoefficient_norm_le (j-i) (k:ℂ)
          · exact hpow (j-i)
        _ ≤ ((j.choose i : ℝ)*C i)*
            ((((j-i:ℕ):ℝ)+1)^(j-i)*(1+(k:ℝ))^j*(2:ℝ)^k) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg _) (hC i))
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg k : (0:ℝ)≤k)]) (Nat.sub_le j i)
        _ = _ := by ring
    rw [rectangularMellinBlockWeight_derivative_pos (k:ℂ) j hxpos]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum hp).trans_eq (by
      rw [← Finset.sum_mul,← Finset.sum_mul]))
  · have hz : iteratedDeriv j (rectangularMellinBlockWeight (k:ℂ)) x=0 := by
      by_contra h
      exact hx (rectangularMellinBlockWeight_iteratedDeriv_tsupport (k:ℂ) j (subset_tsupport _ h))
    rw [hz,norm_zero]
    exact mul_nonneg (mul_nonneg (hB j) (by positivity)) (by positivity)


def phaseGapWeight (k : ℕ) (x : ℝ) : ℂ :=
  ((2:ℂ)^k)⁻¹*rectangularMellinBlockWeight (k:ℂ) x

theorem phaseGapWeight_eq (k : ℕ) (x : ℝ) :
    phaseGapWeight k x=(rectangularSmoothBlockWeight x:ℂ)*((x/2:ℝ):ℂ)^k := by
  unfold phaseGapWeight rectangularMellinBlockWeight
  simp only [Complex.cpow_natCast,Complex.ofReal_div,Complex.ofReal_ofNat,div_pow]
  ring

theorem phaseGapWeight_complexWeight (k : ℕ) : RectangularComplexWeight (phaseGapWeight k) := by
  have h := rectangularMellinBlockWeight_complexWeight (k:ℂ)
  refine ⟨contDiff_const.mul h.1,?_⟩
  apply closure_minimal
  · intro x hx
    apply h.2
    apply subset_tsupport
    intro hz
    exact hx (by simp [phaseGapWeight,hz])
  · exact isClosed_Icc

theorem phaseGapWeight_polynomial_derivative_bounds :
    ∃ B : ℕ → ℝ, (∀ j, 0≤B j) ∧ ∀ j k x,
      ‖iteratedDeriv j (phaseGapWeight k) x‖≤B j*(1+(k:ℝ))^j := by
  obtain ⟨B,hB,hb⟩ := positive_mellin_derivative_bounds
  refine ⟨B,hB,?_⟩
  intro j k x
  unfold phaseGapWeight
  rw [iteratedDeriv_const_mul_field,norm_mul,norm_inv,norm_pow]
  norm_num only [Complex.norm_ofNat]
  calc
    _ ≤ ((2:ℝ)^k)⁻¹*(B j*(1+(k:ℝ))^j*(2:ℝ)^k) :=
      mul_le_mul_of_nonneg_left (hb j k x) (by positivity)
    _ = _ := by field_simp

theorem phaseGapWeight_uniform_logarithmic_derivative_bounds
    {ε κ : ℝ} (hε : 0<ε) (hκ : 0≤κ) :
    ∃ B : ℕ → ℝ, (∀ j, 0≤B j) ∧ ∀ T : ℝ, 1≤T → ∀ k : ℕ,
      (k:ℝ)≤κ*Real.log T → ∀ j x, ‖iteratedDeriv j (phaseGapWeight k) x‖≤B j*T^ε := by
  obtain ⟨C,hC,hb⟩ := phaseGapWeight_polynomial_derivative_bounds
  let B : ℕ → ℝ := fun j => C j*(1+κ)^j*((j.factorial:ℝ)/ε^j*Real.exp ε)
  refine ⟨B,fun j => by dsimp [B]; have hj := hC j; positivity,?_⟩
  intro T hT k hk j x
  have hL : 0≤Real.log T := Real.log_nonneg hT
  have hn : 1+(k:ℝ)≤(1+κ)*(1+Real.log T) := by nlinarith
  calc
    _ ≤ C j*(1+(k:ℝ))^j := hb j k x
    _ ≤ C j*((1+κ)*(1+Real.log T))^j :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hn j) (hC j)
    _ = (C j*(1+κ)^j)*(1+Real.log T)^j := by rw [mul_pow]; ring
    _ ≤ (C j*(1+κ)^j)*(((j.factorial:ℝ)/ε^j*Real.exp ε)*T^ε) :=
      mul_le_mul_of_nonneg_left (logarithmic_power_le_rpow hε hT j)
        (mul_nonneg (hC j) (by positivity))
    _ = _ := by dsimp [B]; ring

def phaseFiveWeights (α : MomentShifts) (z : ℂ) (k : ℕ) : Fin 5 → ℝ → ℂ :=
  ![phaseGapWeight k,rectangularActualMellinBlockWeight α z 0,
    rectangularActualMellinBlockWeight α z 1,
    rectangularMellinBlockWeight (-(1/2+α 2+z)-(k:ℂ)),
    rectangularMellinBlockWeight (-(1/2+α 3+z)-(k:ℂ))]

theorem phaseFiveWeights_complexWeight (α : MomentShifts) (z : ℂ) (k : ℕ) (i : Fin 5) :
    RectangularComplexWeight (phaseFiveWeights α z k i) := by
  fin_cases i <;> dsimp only [phaseFiveWeights]
  · exact phaseGapWeight_complexWeight k
  · exact rectangularActualMellinBlockWeight_complexWeight α z 0
  · exact rectangularActualMellinBlockWeight_complexWeight α z 1
  · exact rectangularMellinBlockWeight_complexWeight _
  · exact rectangularMellinBlockWeight_complexWeight _

theorem phaseFiveWeights_uniform_logarithmic_derivative_bounds
    {ε κ θ : ℝ} (hε : 0<ε) (hκ : 0≤κ) (hθ : 0≤θ) :
    ∃ B : ℕ → ℝ, (∀ j, 0≤B j) ∧ ∀ T : ℝ, 1≤T → ∀ k : ℕ,
      (k:ℝ)≤κ*Real.log T → ∀ α : MomentShifts, (∀ i, ‖α i‖≤1/4) →
      ∀ c : ℝ, 0≤c → c≤1 → ∀ v : ℝ, |v|≤θ*Real.log T → ∀ j i x,
      ‖iteratedDeriv j (phaseFiveWeights α ((c:ℂ)+(v:ℂ)*I) k i) x‖≤B j*T^ε := by
  obtain ⟨B₀,hB₀,hb₀⟩ := phaseGapWeight_uniform_logarithmic_derivative_bounds hε hκ
  obtain ⟨B₁,hB₁,hb₁⟩ := rectangularMellinBlockWeight_uniform_logarithmic_bounds hε (add_nonneg hθ hκ)
  refine ⟨fun j => B₀ j+B₁ j,fun j => add_nonneg (hB₀ j) (hB₁ j),?_⟩
  intro T hT k hk α hα c hc hc1 v hv j i x
  have hL : 0≤Real.log T := Real.log_nonneg hT
  have hbase (l : Fin 4) : (-(1/2+α l+((c:ℂ)+(v:ℂ)*I))).re≤0 ∧
      ‖-(1/2+α l+((c:ℂ)+(v:ℂ)*I))‖≤2+(θ+κ)*Real.log T := by
    have he := actualMellinExponent_small_strip (hα l) hc hc1 v
    exact ⟨he.1,he.2.trans (by nlinarith)⟩
  have hshift (l : Fin 4) : (-(1/2+α l+((c:ℂ)+(v:ℂ)*I))-(k:ℂ)).re≤0 ∧
      ‖-(1/2+α l+((c:ℂ)+(v:ℂ)*I))-(k:ℂ)‖≤2+(θ+κ)*Real.log T := by
    have he := actualMellinExponent_small_strip (hα l) hc hc1 v
    constructor
    · simp only [Complex.sub_re,Complex.natCast_re]
      linarith [(Nat.cast_nonneg k : (0:ℝ)≤k)]
    · have hn := norm_sub_le (-(1/2+α l+((c:ℂ)+(v:ℂ)*I))) (k:ℂ)
      simp only [Complex.norm_natCast] at hn
      nlinarith
  have hs₀ : B₀ j*T^ε≤(B₀ j+B₁ j)*T^ε :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hB₁ j)) (by positivity)
  have hs₁ : B₁ j*T^ε≤(B₀ j+B₁ j)*T^ε :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hB₀ j)) (by positivity)
  fin_cases i <;> dsimp only [phaseFiveWeights]
  · exact (hb₀ T hT k hk j x).trans hs₀
  · exact (hb₁ T hT _ (hbase 0).1 (hbase 0).2 j x).trans hs₁
  · exact (hb₁ T hT _ (hbase 1).1 (hbase 1).2 j x).trans hs₁
  · exact (hb₁ T hT _ (hshift 2).1 (hshift 2).2 j x).trans hs₁
  · exact (hb₁ T hT _ (hshift 3).1 (hshift 3).2 j x).trans hs₁

theorem phaseFiveWeights_near_mass_derivative_bounds
    {s ε κ θ : ℝ} (hs : s<1/2) (hε : 0<ε) (hκ : 0≤κ) (hθ : 0≤θ) :
    ∃ B : ℕ → ℝ, (∀ j, 0≤B j) ∧ ∀ᶠ T : ℝ in atTop,
      ∀ q : Source.QuadraticScales, (∀ j, 0≤q.size j) →
      (∃ n : Fin 7 → ℕ, n∈Source.quadraticIndexSet q ∧ 0<n 6 ∧
        rectangularNearRelation (T^(s-1)) n) → ∀ k : ℕ,
      (k:ℝ)≤κ*Real.log T → ∀ α : MomentShifts, (∀ i, ‖α i‖≤1/4) →
      ∀ c : ℝ, 0≤c → c≤1 → ∀ v : ℝ, |v|≤θ*Real.log T → ∀ j i x,
      ‖iteratedDeriv j (phaseFiveWeights α ((c:ℂ)+(v:ℂ)*I) k i) x‖≤B j*q.mass^ε := by
  obtain ⟨B,hB,hb⟩ := phaseFiveWeights_uniform_logarithmic_derivative_bounds hε hκ hθ
  refine ⟨B,hB,?_⟩
  filter_upwards [rectangular_near_power_mass_lower hs,eventually_ge_atTop (1:ℝ)] with T hm hT
  intro q hq hactive k hk α hα c hc hc1 v hv j i x
  obtain ⟨n,hn,hh,hne⟩ := hactive
  have he := Real.rpow_le_rpow (zero_le_one.trans hT) (hm q hq n hn hh hne) hε.le
  exact (hb T hT k hk α hα c hc hc1 v hv j i x).trans
    (mul_le_mul_of_nonneg_left he (hB j))

end
end SixthMoment
