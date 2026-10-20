import Sechstmoment.Numerator.U.Separation.MellinWeights


namespace Sechstmoment
open Complex Real Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem logarithmic_power_le_rpow {κ T : ℝ} (hκ : 0<κ) (hT : 1≤T) (j : ℕ) :
    (1+Real.log T)^j≤((j.factorial : ℝ)/κ^j*Real.exp κ)*T^κ := by
  have ht : 0<T := zero_lt_one.trans_le hT
  have hL : 0≤Real.log T := Real.log_nonneg hT
  have hf : 0<(j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hp := (div_le_iff₀ hf).mp
    (Real.pow_div_factorial_le_exp (κ*(1+Real.log T)) (by positivity) j)
  rw [mul_pow] at hp
  have he : Real.exp (κ*(1+Real.log T))=Real.exp κ*T^κ := by
    rw [show κ*(1+Real.log T)=κ+Real.log T*κ by ring,Real.exp_add,
      Real.rpow_def_of_pos ht]
  calc
    _ ≤ Real.exp (κ*(1+Real.log T))*(j.factorial : ℝ)/κ^j :=
      (le_div_iff₀ (pow_pos hκ j)).mpr (by simpa only [mul_comm] using hp)
    _ = _ := by rw [he]; ring

theorem rectangularMellinBlockWeight_uniform_logarithmic_bounds
    {κ θ : ℝ} (hκ : 0<κ) (hθ : 0≤θ) :
    ∃ B : ℕ → ℝ, (∀ j, 0≤B j) ∧ ∀ T : ℝ, 1≤T → ∀ s : ℂ,
      s.re≤0 → ‖s‖≤2+θ*Real.log T → ∀ j x,
      ‖iteratedDeriv j (rectangularMellinBlockWeight s) x‖≤B j*T^κ := by
  obtain ⟨C,hC,hb⟩ := rectangularMellinBlockWeight_polynomial_derivative_bounds
  let B : ℕ → ℝ := fun j => C j*(3+θ)^j*((j.factorial : ℝ)/κ^j*Real.exp κ)
  have hB (j : ℕ) : 0≤B j := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (hC j) (by positivity)) (by positivity)
  refine ⟨B,hB,?_⟩
  intro T hT s hs hn j x
  have hL : 0≤Real.log T := Real.log_nonneg hT
  have hbase : 1+‖s‖≤(3+θ)*(1+Real.log T) := by nlinarith
  calc
    _ ≤ C j*(1+‖s‖)^j := hb j s hs x
    _ ≤ C j*((3+θ)*(1+Real.log T))^j :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase j) (hC j)
    _ = (C j*(3+θ)^j)*(1+Real.log T)^j := by rw [mul_pow]; ring
    _ ≤ (C j*(3+θ)^j)*(((j.factorial : ℝ)/κ^j*Real.exp κ)*T^κ) :=
      mul_le_mul_of_nonneg_left (logarithmic_power_le_rpow hκ hT j)
        (mul_nonneg (hC j) (by positivity))
    _ = _ := by dsimp [B]; ring

def rectangularActualMellinBlockWeight (α : MomentShifts) (z : ℂ) (j : Fin 4) : ℝ → ℂ :=
  rectangularMellinBlockWeight (-(1/2+α j+z))

theorem rectangularActualMellinBlockWeight_complexWeight
    (α : MomentShifts) (z : ℂ) (j : Fin 4) :
    RectangularComplexWeight (rectangularActualMellinBlockWeight α z j) :=
  rectangularMellinBlockWeight_complexWeight _

theorem actualMellinExponent_small_strip {α : ℂ} (hα : ‖α‖≤1/4)
    {c : ℝ} (hc : 0≤c) (hc1 : c≤1) (v : ℝ) :
    (-(1/2+α+((c:ℂ)+(v:ℂ)*I))).re≤0 ∧
      ‖-(1/2+α+((c:ℂ)+(v:ℂ)*I))‖≤2+|v| := by
  constructor
  · have hr := (abs_le.mp ((Complex.abs_re_le_norm α).trans hα)).1
    norm_num [Complex.add_re, Complex.mul_re, Complex.div_re]
    linarith
  · rw [norm_neg]
    have hz : ‖(c:ℂ)+(v:ℂ)*I‖≤c+|v| := by
      have h := norm_add_le (c:ℂ) ((v:ℂ)*I)
      simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one,
        abs_of_nonneg hc] using h
    calc
      _ ≤ (‖(1/2:ℂ)‖+‖α‖)+‖(c:ℂ)+(v:ℂ)*I‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (1/2+1/4)+(c+|v|) := by
        norm_num
        exact add_le_add (by linarith) hz
      _ ≤ _ := by linarith

theorem rectangularActualMellinBlockWeight_uniform_logarithmic_derivative_bounds
    {κ θ : ℝ} (hκ : 0<κ) (hθ : 0≤θ) :
    ∃ B : ℕ → ℝ, (∀ j, 0≤B j) ∧ ∀ T : ℝ, 1≤T → ∀ α : MomentShifts,
      (∀ i, ‖α i‖≤1/4) → ∀ c : ℝ, 0≤c → c≤1 → ∀ v : ℝ,
      |v|≤θ*Real.log T → ∀ j i x,
      ‖iteratedDeriv j (rectangularActualMellinBlockWeight α ((c:ℂ)+(v:ℂ)*I) i) x‖≤B j*T^κ := by
  obtain ⟨B,hB,hb⟩ := rectangularMellinBlockWeight_uniform_logarithmic_bounds hκ hθ
  refine ⟨B,hB,?_⟩
  intro T hT α hα c hc hc1 v hv j i x
  have he := actualMellinExponent_small_strip (hα i) hc hc1 v
  exact hb T hT _ he.1 (he.2.trans (by linarith)) j x

theorem rectangularActualMellinBlockWeight_derivative_mass_bounds
    {d ε θ : ℝ} (hd : 0<d) (hε : 0<ε) (hθ : 0≤θ) :
    ∃ B : ℕ → ℝ, (∀ j, 0≤B j) ∧ ∀ T mass : ℝ, 1≤T → T^d≤mass →
      ∀ α : MomentShifts, (∀ i, ‖α i‖≤1/4) →
      ∀ c : ℝ, 0≤c → c≤1 → ∀ v : ℝ, |v|≤θ*Real.log T → ∀ j i x,
      ‖iteratedDeriv j (rectangularActualMellinBlockWeight α ((c:ℂ)+(v:ℂ)*I) i) x‖≤B j*mass^ε := by
  obtain ⟨B,hB,hb⟩ := rectangularActualMellinBlockWeight_uniform_logarithmic_derivative_bounds
    (mul_pos hd hε) hθ
  refine ⟨B,hB,?_⟩
  intro T mass hT hm α hα c hc hc1 v hv j i x
  have ht : 0≤T := zero_le_one.trans hT
  have he : T^(d*ε)≤mass^ε := by
    rw [Real.rpow_mul ht]
    exact Real.rpow_le_rpow (Real.rpow_nonneg ht d) hm hε.le
  exact (hb T hT α hα c hc hc1 v hv j i x).trans
    (mul_le_mul_of_nonneg_left he (hB j))

end
end Sechstmoment
