import Sechstmoment.Arithmetic.Watt.Aggregate

namespace DivisorProof
namespace Watt41
open Real MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 4000000

def highTerm (p : WattScales) (A : ℝ) (γ : ℕ → ℕ → ℝ → ℝ → ℂ) (positive : Bool)
    (h k r s t : ℕ) : ℂ := ∑' l : ℤ, (1-cutoff A l)*completedTerm p γ positive h k r s t l

theorem highTerm_bound {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ E : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hg : ∀ i j, 0 ≤ g i j) (hV : 0 < p.V) (hE : 1 ≤ E) (positive : Bool)
    (h k r : ℕ) {s t : ℕ} (hs : 0 < s) (ht : 0 < t)
    (hsS : (s : ℝ) ≤ p.S) (htP : (t : ℝ) ≤ p.P) (J : ℕ) :
    ‖highTerm p (dualLength p E) γ positive h k r s t‖ ≤
      ((2 : ℝ)^J*fourierDecayConstant (gammaProfileBounds g) (J+2)*((s*t : ℕ) : ℝ)^2/
        (p.V*E^J))*inverseSquareMass := by
  have hEp : 0 < E := by linarith
  have hSp : 0 < p.S := lt_of_lt_of_le (by exact_mod_cast hs) hsS
  have hPp : 0 < p.P := lt_of_lt_of_le (by exact_mod_cast ht) htP
  have hcp : (0 : ℝ) < (s*t : ℕ) := by exact_mod_cast Nat.mul_pos hs ht
  have hA := dualLength_pos hSp hPp hV hEp
  let F : ℤ → ℂ := fun l => (1-cutoff (dualLength p E) l)*completedTerm p γ positive h k r s t l
  have hdecay (l : ℤ) : ‖F l‖ ≤ (p.V/(s*t : ℕ))*
      (fourierDecayConstant (gammaProfileBounds g) (J+2)*(s*t : ℕ))/
        (1+|(l : ℝ)| * (p.V/(s*t : ℕ)))^(J+2) := by
    calc
      _ ≤ ‖completedTerm p γ positive h k r s t l‖ := by
        dsimp only [F]
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (one_sub_cutoff_norm _ _)
      _ ≤ _ := completedTerm_decay hw hg hV positive h k r hs ht (J+2) l
  have htail := (fourier_tail_bound
    (mul_nonneg (fourierDecayConstant_nonneg (gammaProfileBounds_nonneg hg) (J+2)) hcp.le)
    (div_pos hV hcp) (by positivity : 0 ≤ dualLength p E/2) J hdecay).2
  have heq : highTerm p (dualLength p E) γ positive h k r s t =
      ∑' l : ℤ, if dualLength p E/2 < |(l : ℝ)| then F l else 0 := by
    apply tsum_congr
    intro l
    by_cases hl : dualLength p E/2 < |(l : ℝ)|
    · exact (ite_eq_left hl).symm
    · simp only [F,ite_eq_right hl,cutoff_one hA (not_lt.mp hl),sub_self,zero_mul]
  rw [heq]
  apply htail.trans
  apply mul_le_mul_of_nonneg_right _ inverseSquareMass_nonneg
  have hscale := dualLength_frequency_scale hV hEp.le hs ht hsS htP
  have hpow : (E/2)^J ≤ (1+(dualLength p E/2)*(p.V/(s*t : ℕ)))^J := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  calc
    _ ≤ (fourierDecayConstant (gammaProfileBounds g) (J+2)*(s*t : ℕ))/
        ((p.V/(s*t : ℕ))*(E/2)^J) :=
      div_le_div_of_nonneg_left
        (mul_nonneg (fourierDecayConstant_nonneg (gammaProfileBounds_nonneg hg) _) hcp.le)
        (by positivity) (mul_le_mul_of_nonneg_left hpow (div_pos hV hcp).le)
    _ = _ := by
      rw [div_pow]
      field_simp [hV.ne',hEp.ne',hcp.ne']

theorem aggregate_const_mul (p : WattScales) (a bc : ℕ → ℂ) (u₀ u₁ : ℝ → ℂ)
    (F : ℕ → ℕ → ℕ → ℕ → ℕ → ℂ) (z : ℂ) :
    aggregate p a bc u₀ u₁ (fun h k r s t => z*F h k r s t) = z*aggregate p a bc u₀ u₁ F := by
  unfold aggregate
  simp only [mul_sum]
  apply sum_congr rfl
  intro rs _
  apply sum_congr rfl
  intro t _
  apply sum_congr rfl
  intro h _
  apply sum_congr rfl
  intro k _
  ring

theorem highSum_eq_aggregate {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ A : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hA : 0 < A) (positive : Bool) : highSum p A positive a bc u₀ u₁ γ =
      aggregate p a bc u₀ u₁ (highTerm p A γ positive) := by
  unfold highSum highTerm
  simp_rw [frequencySum_eq_aggregate,← aggregate_const_mul]
  apply aggregate_tsum
  intro h k r s t hs ht
  exact smooth_tail_summable (completedTerm_summable hw positive h k r hs ht) hA


theorem tail_global_bound {η : ℝ} (hη : 0 < η)
    (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (g : ℕ → ℕ → ℝ) (hg : ∀ i j, 0 ≤ g i j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : WattScales) (Δ : ℝ) (a bc : ℕ → ℂ) (u₀ u₁ : ℝ → ℂ)
      (γ : ℕ → ℕ → ℝ → ℝ → ℂ), (∀ n, 1 ≤ p.size n) → 0 < Δ → Δ ≤ 1 →
      WattWeightData b g p Δ a bc u₀ u₁ γ → ∀ positive : Bool,
      ‖highSum p (dualLength p (p.product^η)) positive a bc u₀ u₁ γ‖ ≤ C*wattMajorant p Δ η := by
  obtain ⟨J,hJ⟩ := exists_nat_ge (3/η)
  have hJ' : 3 ≤ η*(J : ℝ) := by
    have hj := (div_le_iff₀ hη).mp hJ
    nlinarith
  let D := (2 : ℝ)^J*fourierDecayConstant (gammaProfileBounds g) (J+2)*inverseSquareMass
  let C := b 0^2*D
  have hD : 0 ≤ D := mul_nonneg
    (mul_nonneg (by positivity) (fourierDecayConstant_nonneg (gammaProfileBounds_nonneg hg) _))
    inverseSquareMass_nonneg
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg _) hD
  refine ⟨C,hC,?_⟩
  intro p Δ a bc u₀ u₁ γ hp hΔ hΔ₁ hw positive
  have hH : 0 < p.H := lt_of_lt_of_le zero_lt_one (hp 0)
  have hK : 0 < p.C := lt_of_lt_of_le zero_lt_one (hp 1)
  have hR : 0 < p.R := lt_of_lt_of_le zero_lt_one (hp 2)
  have hS : 0 < p.S := lt_of_lt_of_le zero_lt_one (hp 3)
  have hV : 0 < p.V := lt_of_lt_of_le zero_lt_one (hp 4)
  have hP : 0 < p.P := lt_of_lt_of_le zero_lt_one (hp 5)
  have hT : 1 ≤ p.product := product_ge_one hp
  let E := p.product^η
  have hE : 1 ≤ E := Real.one_le_rpow hT hη.le
  have hEp : 0 < E := by linarith
  have hA := dualLength_pos hS hP hV hEp
  let B := D*(p.S*p.P)^2/(p.V*E^J)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hSP : p.S*p.P ≤ p.product := by
    have hRV : 1 ≤ p.R*p.V := one_le_mul_of_one_le_of_one_le (hp 2) (hp 4)
    unfold WattScales.product
    nlinarith [mul_le_mul_of_nonneg_right hRV (mul_pos hS hP).le]
  have hnorm : ‖highSum p (dualLength p E) positive a bc u₀ u₁ γ‖ ≤
      p.R*p.S*p.P*(p.H*p.C*(b 0^2*B)) := by
    rw [highSum_eq_aggregate hw hA]
    apply aggregate_fibre_bound hp a bc u₀ u₁ _ hw.alpha_bound hw.beta_bound (by positivity)
    intro rs hrs t ht
    have hs := mem_dyadicRange.mp (mem_product.mp (mem_filter.mp hrs).1).2
    change 1 ≤ rs.2 ∧ p.S/2 ≤ (rs.2 : ℝ) ∧ (rs.2 : ℝ) ≤ p.S at hs
    have htp := mem_positiveRange.mp (mem_filter.mp ht).1
    have hterm (h k : ℕ) : ‖highTerm p (dualLength p E) γ positive h k rs.1 rs.2 t‖ ≤ B := by
      apply (highTerm_bound hw hg hV hE positive h k rs.1 hs.1 htp.1 hs.2.2 htp.2 J).trans
      have hc : ((rs.2*t : ℕ) : ℝ) ≤ p.S*p.P := by
        simpa only [Nat.cast_mul] using mul_le_mul hs.2.2 htp.2 (Nat.cast_nonneg t) hS.le
      calc
        _ = D*((rs.2*t : ℕ) : ℝ)^2/(p.V*E^J) := by dsimp [D]; ring
        _ ≤ _ := by dsimp [B]; gcongr
    have hhk : ‖∑ h ∈ positiveRange p.H, ∑ k ∈ positiveRange p.C,
        u₀ h*u₁ k*highTerm p (dualLength p E) γ positive h k rs.1 rs.2 t‖ ≤
          p.H*(p.C*(b 0^2*B)) := by
      apply norm_sum_le_scale _ _ (card_positiveRange_le hH.le) (by positivity)
      intro h hh
      apply norm_sum_le_scale _ _ (card_positiveRange_le hK.le) (by positivity)
      intro k hk
      rw [norm_mul]
      exact mul_le_mul
        (weight_zero_order_bound hw (mem_positiveRange.mp hh).1 (mem_positiveRange.mp hk).1 (hb 0))
        (hterm h k) (norm_nonneg _) (sq_nonneg _)
    exact hhk.trans_eq (by ring)
  have heq : p.R*p.S*p.P*(p.H*p.C*(b 0^2*B)) =
      C*(p.H*p.C*p.R)*((p.S*p.P)^3/(p.V*E^J)) := by dsimp [C,B]; ring
  rw [heq] at hnorm
  have hpow : (p.S*p.P)^3 ≤ E^J := by
    calc
      _ ≤ p.product^3 := pow_le_pow_left₀ (mul_pos hS hP).le hSP 3
      _ = p.product^(3 : ℝ) := by exact_mod_cast (Real.rpow_natCast p.product 3).symm
      _ ≤ p.product^(η*(J : ℝ)) := Real.rpow_le_rpow_of_exponent_le hT hJ'
      _ = E^J := Real.rpow_mul_natCast (zero_le_one.trans hT) η J
  have hratio : (p.S*p.P)^3/(p.V*E^J) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < p.V*E^J)).mpr
    exact hpow.trans (le_mul_of_one_le_left (by positivity) (hp 4))
  have hbase : p.H*p.C*p.R ≤ core p Δ :=
    (le_mul_of_one_le_right (by positivity) (hp 4)).trans (core_ge_HCRV hp hΔ hΔ₁)
  have hcore : 0 ≤ core p Δ := (by positivity : 0 ≤ p.H*p.C*p.R).trans hbase
  have hloss : 1 ≤ (totalSize p)^(20*η) := Real.one_le_rpow (totalSize_ge_one hp) (by positivity)
  rw [wattMajorant_eq_core]
  calc
    _ ≤ C*(p.H*p.C*p.R)*1 := hnorm.trans (mul_le_mul_of_nonneg_left hratio (by positivity))
    _ ≤ C*core p Δ := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hbase hC
    _ ≤ C*core p Δ*(totalSize p)^(20*η) := le_mul_of_one_le_right (mul_nonneg hC hcore) hloss
    _ = _ := by ring

end
end Watt41
end DivisorProof
