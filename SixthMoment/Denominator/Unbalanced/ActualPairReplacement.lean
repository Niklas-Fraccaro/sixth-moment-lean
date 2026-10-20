import SixthMoment.Denominator.Unbalanced.ActualPairNorm

namespace SixthMoment
open Complex Real Filter Set Source
open scoped Topology BigOperators
noncomputable section
set_option maxHeartbeats 1000000

def d04ActualUnbalancedPair (T t : ℝ) (σ : Fin 2 → ℂ) : ℂ :=
  (criticalChi t)⁻¹*zetaCPlus T t (σ 0)*zetaCMinus T t (σ 1)

theorem d04NegativeGenerators_eq_centered (T t : ℝ) (σ : Fin 2 → ℂ) :
    zetaCMinus T t (-σ 0)*zetaCMinus T t (σ 1) =
      Complex.exp ((-σ 0+σ 1)/2)*
        (riemannZeta (d04NegativeZetaArguments T t σ 0)*
          riemannZeta (d04NegativeZetaArguments T t σ 1)) := by
  unfold zetaCMinus shiftedZetaGenerator d04NegativeZetaArguments
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_div]
  rw [show (-σ 0+σ 1)/2=(-σ 0)/2+σ 1/2 by ring, Complex.exp_add]
  rw [show 1-criticalLinePoint t + -(σ 0/(Real.log T:ℂ)) =
    1-criticalLinePoint t-σ 0/(Real.log T:ℂ) by ring]
  ring

theorem d04ActualUnbalancedPair_eq_centered {T : ℝ}
    (hL : 0 < Real.log T) (t : ℝ) (σ : Fin 2 → ℂ)
    (hσ : ‖σ 0‖ < Real.log T/2) :
    d04ActualUnbalancedPair T t σ = centeringFactor T t (σ 0)*
      (zetaCMinus T t (-σ 0)*zetaCMinus T t (σ 1)) := by
  have hs := centeringShift_mem_strip hL t (σ 0) (by linarith)
  unfold d04ActualUnbalancedPair
  rw [centering_generator_functional_equation T t (σ 0) hs.1 hs.2, mul_assoc]

theorem d04ActualPair_oneSided_uniform_error_of_raw {R ε K : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1/4) (hK : 0 ≤ K)
    (hraw : ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc T (2*T),
      ∀ σ : Fin 2 → ℂ, (∀ i, ‖σ i‖ ≤ R) →
        ‖riemannZeta (d04NegativeZetaArguments T t σ 0)*
            riemannZeta (d04NegativeZetaArguments T t σ 1)-
          d04OneSidedRawSeries (T^3) (d04NegativeZetaArguments T t σ 0)
            (d04NegativeZetaArguments T t σ 1)‖ ≤ K*T^(-1+ε)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc T (2*T),
      ∀ σ : Fin 2 → ℂ, (∀ i, ‖σ i‖ ≤ R) →
        ‖d04ActualUnbalancedPair T t σ-
          d04CenteringPurePower T t (σ 0)*d04OneSidedCenteredPair T t σ‖ ≤
          C*T^(-1/2+2*ε) := by
  obtain ⟨G,hG,hg⟩ := d04NegativeGenerators_uniform_norm hR hε hε1
  obtain ⟨D,hD,hd⟩ := d04CenteringPower_uniform_error hR
  let c : ℝ := 1/2+2*ε
  have hc0 : 0 ≤ c := by dsimp [c]; linarith
  have hc1 : c ≤ 1 := by dsimp [c]; linarith
  refine ⟨2*D*G+2*Real.exp R*K, by positivity, ?_⟩
  filter_upwards [hg,hd,hraw,d04CenteringPurePower_uniform_norm (R:=R),
    eventually_gt_atTop (1:ℝ), eventually_centering_disk R] with T hgT hdT hrT hpT hT hLT
  intro t ht σ hσ
  have hTp : 0 < T := zero_lt_one.trans hT
  have htp : 0 < t := hTp.trans_le ht.1
  have hτ : t/T ∈ Icc (1:ℝ) 2 :=
    ⟨(le_div_iff₀ hTp).mpr (by simpa using ht.1), (div_le_iff₀ hTp).mpr ht.2⟩
  have htEq : T*(t/T)=t := by field_simp
  have hp := hpT (t/T) hτ (σ 0) (hσ 0)
  rw [htEq] at hp
  have hn : t^c ≤ 2*T^c := by
    calc
      _ ≤ (2*T)^c := Real.rpow_le_rpow htp.le ht.2 hc0
      _ = 2^c*T^c := Real.mul_rpow (by norm_num) hTp.le
      _ ≤ 2*T^c := by
        gcongr
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hc1
  have hgn : ‖zetaCMinus T t (-σ 0)*zetaCMinus T t (σ 1)‖ ≤ 2*G*T^c :=
    (hgT t ht σ hσ).trans ((mul_le_mul_of_nonneg_left hn hG).trans_eq (by ring))
  have hecenter := d02ZetaCentering_norm_le (![-σ 0,σ 1] : Fin 2 → ℂ)
    (by
      intro i
      fin_cases i
      · simpa using hσ 0
      · simpa using hσ 1)
  have herr : ‖zetaCMinus T t (-σ 0)*zetaCMinus T t (σ 1)-
      d04OneSidedCenteredPair T t σ‖ ≤ Real.exp R*K*T^(c-1) := by
    rw [d04NegativeGenerators_eq_centered, d04OneSidedCenteredPair, ← mul_sub, norm_mul]
    have hlo : T^(-1+ε) ≤ T^(c-1) :=
      Real.rpow_le_rpow_of_exponent_le hT.le (by dsimp [c]; linarith)
    exact (mul_le_mul hecenter ((hrT t ht σ hσ).trans
      (mul_le_mul_of_nonneg_left hlo hK)) (norm_nonneg _) (Real.exp_pos _).le).trans_eq (by ring)
  have heq : d04ActualUnbalancedPair T t σ-
      d04CenteringPurePower T t (σ 0)*d04OneSidedCenteredPair T t σ =
      (centeringFactor T t (σ 0)-d04CenteringPurePower T t (σ 0))*
        (zetaCMinus T t (-σ 0)*zetaCMinus T t (σ 1))+
      d04CenteringPurePower T t (σ 0)*
        (zetaCMinus T t (-σ 0)*zetaCMinus T t (σ 1)-d04OneSidedCenteredPair T t σ) := by
    rw [d04ActualUnbalancedPair_eq_centered hLT.1 t σ (by linarith [hσ 0,hLT.2])]
    ring
  rw [heq]
  apply (norm_add_le _ _).trans
  simp only [norm_mul]
  have hbound := add_le_add
    (mul_le_mul (hdT t ht (σ 0) (hσ 0)) hgn (norm_nonneg _) (by positivity : 0≤D/T))
    (mul_le_mul hp herr (norm_nonneg _) (by norm_num : (0:ℝ)≤2))
  rw [norm_mul] at hbound
  apply hbound.trans_eq
  have he : T^c/T = T^(c-1) := by
    rw [Real.rpow_sub hTp, Real.rpow_one]
  calc
    D/T*(2*G*T^c)+2*(Real.exp R*K*T^(c-1)) =
        2*D*G*(T^c/T)+2*Real.exp R*K*T^(c-1) := by ring
    _ = (2*D*G+2*Real.exp R*K)*T^(-1/2+2*ε) := by
      rw [he,show c-1=-1/2+2*ε by dsimp [c]; ring]
      ring

end
end SixthMoment
