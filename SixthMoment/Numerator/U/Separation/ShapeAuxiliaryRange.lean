import SixthMoment.Numerator.U.Separation.ShapeNearSupport

namespace SixthMoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem phase_near_H_from_product_cutoff {T ρ ε s u : ℝ} (hT : 1 ≤ T)
    (hε : 0 ≤ ε) (hexp : s+u/2 ≤ ρ*ε) (q : QuadraticScales)
    (hq : ∀ j, 0 ≤ q.size j) (hAB : T^ρ ≤ q.A*q.B)
    (hMN : q.M*q.N ≤ T^(2+u)) (n : Fin 7 → ℕ)
    (hn : ∀ j, (n j:ℝ) ∈ Icc (q.size j) (2*q.size j))
    (hne : rectangularNearRelation (T^(s-1)) n) :
    q.H ≤ 8*(q.A*q.B)^(1/2+ε) := by
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hABp : 0 < q.A*q.B := (Real.rpow_pos_of_pos hTp ρ).trans_le hAB
  have hM : 0 ≤ q.M := by
    unfold QuadraticScales.M
    have h₁ := hq 2; have h₂ := hq 3
    norm_num [QuadraticScales.size] at h₁ h₂
    positivity
  have hN : 0 ≤ q.N := by
    unfold QuadraticScales.N
    have h₁ := hq 4; have h₂ := hq 5
    norm_num [QuadraticScales.size] at h₁ h₂
    positivity
  have hs : Real.sqrt (q.M*q.N) ≤ T^(1+u/2) := by
    rw [Real.sqrt_eq_rpow]
    calc
      _ ≤ (T^(2+u))^(1/2:ℝ) := Real.rpow_le_rpow (mul_nonneg hM hN) hMN (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hTp.le]; congr 1; ring
  have he : T^(s-1)*Real.sqrt (q.M*q.N) ≤ (q.A*q.B)^ε := by
    calc
      _ ≤ T^(s-1)*T^(1+u/2) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = T^(s+u/2) := by rw [← Real.rpow_add hTp]; congr 1; ring
      _ ≤ T^(ρ*ε) := Real.rpow_le_rpow_of_exponent_le hT hexp
      _ = (T^ρ)^ε := Real.rpow_mul hTp.le ρ ε
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hAB hε
  have hg := phase_active_near_gap_scale_bound q hq n hn
    (Real.rpow_nonneg hTp.le (s-1)) hne
  have hm : Real.sqrt q.mass = Real.sqrt (q.A*q.B)*Real.sqrt (q.M*q.N) := by
    unfold QuadraticScales.mass
    rw [show q.A*q.B*q.M*q.N=(q.A*q.B)*(q.M*q.N) by ring,
      Real.sqrt_mul hABp.le]
  rw [hm] at hg
  calc
    q.H ≤ 8*T^(s-1)*(Real.sqrt (q.A*q.B)*Real.sqrt (q.M*q.N)) := hg
    _ = 8*Real.sqrt (q.A*q.B)*(T^(s-1)*Real.sqrt (q.M*q.N)) := by ring
    _ ≤ 8*Real.sqrt (q.A*q.B)*(q.A*q.B)^ε :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hABp]

theorem phase_near_nontrivial_uniform {d s : ℝ} (hexp : d+s < 1) :
    ∀ᶠ T : ℝ in atTop, ∀ q : QuadraticScales, (∀ j, 0 ≤ q.size j) →
      0 < q.A*q.B → q.A*q.B ≤ T^d → ∀ n : Fin 7 → ℕ,
      (∀ j, (n j:ℝ) ∈ Icc (q.size j) (2*q.size j)) → 0 < n 6 →
      rectangularNearRelation (T^(s-1)) n → q.A*q.B ≤ q.M*q.N := by
  have ht : Tendsto (fun T : ℝ => T^(d+s-1)) atTop (𝓝 0) := by
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (show 0 < -(d+s-1) by linarith)
  have hb : ∀ᶠ T : ℝ in atTop, T^(d+s-1) ≤ 1/8 :=
    ((tendsto_order.1 ht).2 (1/8) (by norm_num)).mono (fun _ h => h.le)
  filter_upwards [hb, eventually_gt_atTop (0:ℝ)] with T hsmall hT
  intro q hq hAB hab n hn hh hne
  apply phase_active_near_nontrivial_range q hq hAB n hn hh
    (Real.rpow_nonneg hT.le _) ?_ hne
  have hs := mul_le_mul_of_nonneg_left hab (Real.rpow_nonneg hT.le (s-1))
  have he : T^(s-1)*T^d=T^(d+s-1) := by rw [← Real.rpow_add hT]; congr 1; ring
  rw [he] at hs
  nlinarith

theorem phase_source_auxiliary_exponents {a b ρ ε : ℝ}
    (_ha : 0 ≤ a) (hab : a ≤ b) (hlen : 3*a+5*b < 2)
    (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ s u : ℝ, 0 < s ∧ s < 1/2 ∧ 0 < u ∧
      s+u/2 < ρ*ε ∧ a+b+s < 1 := by
  have hd : a+b < 1/2 := by linarith
  let e : ℝ := min (ρ*ε/4) (1/8)
  have he : 0 < e := lt_min (by positivity) (by norm_num)
  have h₁ : e ≤ ρ*ε/4 := min_le_left _ _
  have h₂ : e ≤ 1/8 := min_le_right _ _
  refine ⟨e,e,he,by linarith,he,by nlinarith [mul_pos hρ hε],by linarith⟩

end
end SixthMoment
