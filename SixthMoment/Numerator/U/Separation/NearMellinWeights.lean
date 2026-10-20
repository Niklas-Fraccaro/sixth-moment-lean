import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import SixthMoment.Numerator.U.Reconstruction.RectangularNearUnitExclusion
import SixthMoment.Numerator.U.Separation.LogarithmicMellinWeights


namespace SixthMoment
open Source Real Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem rectangular_source_tuple_mass_le (q : QuadraticScales)
    (hq : ∀ j, 0≤q.size j) (n : Fin 7 → ℕ) (hn : n∈quadraticIndexSet q) :
    (n 0 : ℝ)*n 1*n 2*n 3*n 4*n 5≤64*q.mass := by
  have hb (j : Fin 6) : (n j.castSucc : ℝ)≤2*q.size j.castSucc := by
    have hh := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hn j.castSucc)).2
    exact (Nat.cast_le.mpr hh).trans
      (Nat.floor_le (mul_nonneg (by norm_num) (hq j.castSucc)))
  have hp := Finset.prod_le_prod₀
    (s := Finset.univ)
    (f := fun j : Fin 6 => (n j.castSucc : ℝ))
    (g := fun j : Fin 6 => 2*q.size j.castSucc)
    (fun _ _ => by positivity) (fun j _ => hb j)
  calc
    _ = ∏ j : Fin 6, (n j.castSucc : ℝ) := by simp [Fin.prod_univ_six]
    _ ≤ ∏ j : Fin 6, 2*q.size j.castSucc := hp
    _ = _ := by
      simp [Fin.prod_univ_six, QuadraticScales.size, QuadraticScales.mass,
        QuadraticScales.M, QuadraticScales.N]
      ring

theorem rectangular_near_source_mass_lower {T η : ℝ} (hT : 0<T) (_hη0 : 0≤η)
    (hη : η≤1/(8*Real.sqrt T)) (q : QuadraticScales) (hq : ∀ j, 0≤q.size j)
    (n : Fin 7 → ℕ) (hn : n∈quadraticIndexSet q) (hh : 0<n 6)
    (hne : rectangularNearRelation η n) : T≤q.mass := by
  let P : ℝ := (n 0 : ℝ)*n 1*n 2*n 3*n 4*n 5
  have hP : 0≤P := by dsimp [P]; positivity
  have hp := rectangular_source_tuple_mass_le q hq n hn
  have hgap : (1:ℝ)≤n 6 := by exact_mod_cast Nat.succ_le_iff.mpr hh
  have hs : 1≤η*Real.sqrt P := hgap.trans hne
  have hdiv : 1≤Real.sqrt P/(8*Real.sqrt T) := hs.trans (by
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using
      mul_le_mul_of_nonneg_right hη (Real.sqrt_nonneg P))
  have hden : 0<8*Real.sqrt T := mul_pos (by norm_num) (Real.sqrt_pos.mpr hT)
  have hroot : 8*Real.sqrt T≤Real.sqrt P := by
    simpa only [one_mul] using (le_div_iff₀ hden).mp hdiv
  have hsq := pow_le_pow_left₀ (by positivity : 0≤8*Real.sqrt T) hroot 2
  rw [mul_pow, Real.sq_sqrt hT.le, Real.sq_sqrt hP] at hsq
  norm_num at hsq
  dsimp [P] at hsq
  linarith

theorem rectangular_near_power_mass_lower {s : ℝ} (hs : s<1/2) :
    ∀ᶠ T : ℝ in atTop, ∀ q : QuadraticScales, (∀ j, 0≤q.size j) →
      ∀ n : Fin 7 → ℕ, n∈quadraticIndexSet q → 0<n 6 →
        rectangularNearRelation (T^(s-1)) n → T≤q.mass := by
  have ht : Tendsto (fun T : ℝ => 8*T^(s-1/2)) atTop (𝓝 0) := by
    simpa only [neg_sub, mul_zero] using
      (tendsto_rpow_neg_atTop (by linarith : 0<1/2-s)).const_mul 8
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    eventually_gt_atTop (0:ℝ)] with T he hT
  intro q hq n hn hh hne
  apply rectangular_near_source_mass_lower hT (Real.rpow_nonneg hT.le _) _ q hq n hn hh hne
  apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<8) (Real.sqrt_pos.mpr hT))).mpr
  calc
    T^(s-1)*(8*Real.sqrt T) = 8*(T^(s-1)*T^(1/2:ℝ)) := by rw [Real.sqrt_eq_rpow]; ring
    _ = 8*T^(s-1/2) := by rw [← Real.rpow_add hT]; congr 1; ring
    _ ≤ 1 := he.le

theorem rectangularActualMellinBlockWeight_near_mass_derivative_bounds
    {s ε θ : ℝ} (hs : s<1/2) (hε : 0<ε) (hθ : 0≤θ) :
    ∃ B : ℕ → ℝ, (∀ j, 0≤B j) ∧ ∀ᶠ T : ℝ in atTop,
      ∀ q : QuadraticScales, (∀ j, 0≤q.size j) →
      (∃ n : Fin 7 → ℕ, n∈quadraticIndexSet q ∧ 0<n 6 ∧
        rectangularNearRelation (T^(s-1)) n) →
      ∀ α : MomentShifts, (∀ i, ‖α i‖≤1/4) →
      ∀ c : ℝ, 0≤c → c≤1 → ∀ v : ℝ, |v|≤θ*Real.log T → ∀ j i x,
      ‖iteratedDeriv j (rectangularActualMellinBlockWeight α ((c:ℂ)+(v:ℂ)*Complex.I) i) x‖≤
        B j*q.mass^ε := by
  obtain ⟨B,hB,hb⟩ := rectangularActualMellinBlockWeight_derivative_mass_bounds
    (by norm_num : (0:ℝ)<1) hε hθ
  refine ⟨B,hB,?_⟩
  filter_upwards [rectangular_near_power_mass_lower hs, eventually_ge_atTop (1:ℝ)] with T hm hT
  intro q hq hactive α hα c hc hc1 v hv j i x
  obtain ⟨n,hn,hh,hne⟩ := hactive
  exact hb T q.mass hT (by simpa using hm q hq n hn hh hne) α hα c hc hc1 v hv j i x

end
end SixthMoment
