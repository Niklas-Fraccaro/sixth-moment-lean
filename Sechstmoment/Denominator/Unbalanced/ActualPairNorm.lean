import Sechstmoment.Denominator.Unbalanced.CenteringPower

/-! A common actual zeta-pair bound is derived from the closed D02
Gaussian expansion. Conjugation then bounds the two negative generators. -/
namespace Sechstmoment
open Complex Real Filter Set Source
open scoped Topology BigOperators ComplexConjugate
noncomputable section
set_option maxHeartbeats 1000000

theorem d04MixedGenerators_uniform_norm {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1/4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc T (2*T),
      ∀ σ : Fin 2 → ℂ, (∀ i, ‖σ i‖ ≤ R) →
        ‖zetaCPlus T t (σ 0)*zetaCMinus T t (σ 1)‖ ≤ C*t^(1/2+2*ε) := by
  obtain ⟨K,hK,herr⟩ := d02ZetaPair_gaussian_window_error hR hε hε1
  obtain ⟨G,hG,hmass⟩ := d02ActualGaussianPair_uniform_norm hε hε1
  let B := secondDualBoxConstant R
  have hB : 0 ≤ B := (Real.exp_pos _).le
  refine ⟨K+Real.exp R*(G+B*G), by positivity, ?_⟩
  filter_upwards [herr, d02RawSecondMomentShifts_eventually_small (R:=R) hε,
    eventually_ge_atTop (1:ℝ), Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (1:ℝ))] with T he hsmall hT hL
  intro t ht σ hσ
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have htp : 0 < t := hTp.trans_le ht.1
  have ht1 : 1 ≤ t := hT.trans ht.1
  have hτ : t/T ∈ Icc (1:ℝ) 2 :=
    ⟨(le_div_iff₀ hTp).mpr (by simpa using ht.1), (div_le_iff₀ hTp).mpr ht.2⟩
  have hpow := secondDualPower_normalized_box_norm_le hTp hR hL hτ σ hσ
  rw [show T*(t/T)=t by field_simp] at hpow
  have ha := hsmall σ hσ
  have hb := d02DualSecondMomentShifts_norm_le ha
  have hmain : ‖d02CenteredGaussianPair T t σ‖ ≤
      Real.exp R*(G+B*G)*t^(1/2+2*ε) := by
    unfold d02CenteredGaussianPair
    rw [norm_mul]
    have hin : ‖d02ActualGaussianPair t (rawSecondMomentShifts T σ)+
        secondDualPower t (rawSecondMomentShifts T σ)*d02ActualGaussianPair t
          (d02DualSecondMomentShifts (rawSecondMomentShifts T σ))‖ ≤
        (G+B*G)*t^(1/2+2*ε) := by
      apply (norm_add_le _ _).trans
      rw [norm_mul]
      exact (add_le_add (hmass t htp _ ha)
        (mul_le_mul hpow (hmass t htp _ hb) (norm_nonneg _) hB)).trans_eq (by ring)
    exact (mul_le_mul (d02ZetaCentering_norm_le σ hσ) hin (norm_nonneg _)
      (Real.exp_pos _).le).trans_eq (by ring)
  have hlo : t^(-1/2+2*ε) ≤ t^(1/2+2*ε) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
  have hn := norm_add_le
    (zetaCPlus T t (σ 0)*zetaCMinus T t (σ 1)-d02CenteredGaussianPair T t σ)
    (d02CenteredGaussianPair T t σ)
  simp only [sub_add_cancel] at hn
  exact hn.trans ((add_le_add ((he t ht σ hσ).trans
    (mul_le_mul_of_nonneg_left hlo hK)) hmain).trans_eq (by ring))

theorem d04Generators_conjugate (T t : ℝ) (z : ℂ) :
    zetaCPlus T t (conj z) = conj (zetaCMinus T t z) := by
  have h2 : conj (2 : ℂ)=2 := map_ofNat _ _
  have hs : conj (1-criticalLinePoint t)=criticalLinePoint t := by
    rw [criticalLinePoint_one_sub]
    exact star_star _
  unfold zetaCPlus zetaCMinus shiftedZetaGenerator
  rw [map_mul, ← Complex.exp_conj, ← riemannZeta_conj]
  simp only [map_div₀, map_add, hs, conj_ofReal, h2]

theorem d04NegativeGenerators_uniform_norm {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1/4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc T (2*T),
      ∀ σ : Fin 2 → ℂ, (∀ i, ‖σ i‖ ≤ R) →
        ‖zetaCMinus T t (-σ 0)*zetaCMinus T t (σ 1)‖ ≤ C*t^(1/2+2*ε) := by
  obtain ⟨C,hC,h⟩ := d04MixedGenerators_uniform_norm hR hε hε1
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T hT
  intro t ht σ hσ
  have hsquare (z : ℂ) (hz : ‖z‖ ≤ R) :
      ‖zetaCMinus T t z‖^2 ≤ C*t^(1/2+2*ε) := by
    have hv : ∀ i : Fin 2, ‖(![conj z,z] : Fin 2 → ℂ) i‖ ≤ R := by
      intro i
      fin_cases i <;> simpa using hz
    have hh := hT t ht ![conj z,z] hv
    simpa [d04Generators_conjugate, norm_mul, sq] using hh
  have ha := hsquare (-σ 0) (by simpa using hσ 0)
  have hb := hsquare (σ 1) (hσ 1)
  rw [norm_mul]
  nlinarith [sq_nonneg (‖zetaCMinus T t (-σ 0)‖-‖zetaCMinus T t (σ 1)‖)]

end
end Sechstmoment
