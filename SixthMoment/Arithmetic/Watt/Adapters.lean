import SixthMoment.Arithmetic.QuadraticDivisor.Reduction.BlockSums
import SixthMoment.Arithmetic.Watt.Statement


namespace DivisorProof
open Real Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 1600000

namespace Watt41

def weightedSum (q : Scales) (σ : ℤ) (a b : ℕ → ℂ)
    (α β w : ℝ → ℂ) (f : ℕ → ℕ → ℝ → ℝ) : ℂ :=
  ∑ rs ∈ pairRange q, a rs.1*b rs.2*innerSum q σ α β w f rs.1 rs.2

theorem norm_weightedSum_le_U (q : Scales) (σ : ℤ) (a b : ℕ → ℂ)
    (α β w : ℝ → ℂ) (f : ℕ → ℕ → ℝ → ℝ)
    (ha : ∀ r, ‖a r‖ ≤ 1) (hb : ∀ s, ‖b s‖ ≤ 1) :
    ‖weightedSum q σ a b α β w f‖ ≤ U q σ α β w f := by
  unfold weightedSum U
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro rs _
  rw [norm_mul, norm_mul]
  have hab : ‖a rs.1‖*‖b rs.2‖ ≤ 1 := by
    calc _ ≤ 1*1 := mul_le_mul (ha _) (hb _) (norm_nonneg _) (by norm_num)
         _ = 1 := by ring
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hab
    (norm_nonneg (innerSum q σ α β w f rs.1 rs.2))

theorem Scales.X_sq {q : Scales}
    (hH : 0 < q.H) (hK : 0 < q.K) (hL : 0 < q.L) (hR : 0 ≤ q.R) :
    q.X^2 = q.R*q.S^2*q.P^2/(q.H*q.K*q.L) := by
  unfold Scales.X
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  ring

def completedScales (p : WattScales) (L : ℝ) : Scales :=
  ⟨p.H,p.C,L,p.P,p.R,p.S⟩

theorem completedScales_Q (p : WattScales) (L : ℝ) :
    (completedScales p L).Q = p.R*p.S := rfl

theorem completedScales_X_sq {p : WattScales} {L : ℝ}
    (hH : 0 < p.H) (hC : 0 < p.C) (hR : 0 ≤ p.R) (hV : 0 < p.V) (hL : 0 < L)
    (hprod : 0 ≤ p.product) :
    (completedScales p L).X^2 = p.X^2*(p.S*p.P/(p.V*L)) := by
  rw [Scales.X_sq hH hC hL hR]
  have hX : p.X^2 = p.product/(p.H*p.C) :=
    Real.sq_sqrt (div_nonneg hprod (by positivity))
  rw [hX]
  dsimp [completedScales, WattScales.product]
  field_simp [hH.ne',hC.ne',hV.ne',hL.ne']

theorem completedScales_sizes {p : WattScales} {L : ℝ}
    (hp : ∀ i, 1 ≤ p.size i) (hL : 1 ≤ L) :
    ∀ i, 1 ≤ (completedScales p L).size i := by
  intro i
  fin_cases i
  · exact hp 0
  · exact hp 1
  · exact hL
  · exact hp 5
  · exact hp 2
  · exact hp 3

theorem completedScales_size_conditions {p : WattScales} {L : ℝ}
    (hfirst : p.H^2*p.C ≤ (p.R*p.S)^2) (hsecond : L ≤ (p.R*p.S)^2) :
    max ((completedScales p L).H^2*(completedScales p L).K) L ≤
      (completedScales p L).Q^2 := max_le hfirst hsecond

theorem completedScales_last_ratio {p : WattScales} {L : ℝ}
    (hH : 0 < p.H) (hC : 0 < p.C) (hR : 0 < p.R) (hS : 0 < p.S)
    (hV : 0 < p.V) (hP : 0 < p.P) (hL : 0 < L) :
    (completedScales p L).H^2*(completedScales p L).K*L*
        (completedScales p L).X^2/(completedScales p L).Q^4 =
      p.H^2*p.C*p.P*p.X^2/(p.R^4*p.S^3*p.V) := by
  have hprod : 0 ≤ p.product := by unfold WattScales.product; positivity
  rw [completedScales_X_sq hH hC hR.le hV hL hprod]
  dsimp [completedScales, Scales.Q]
  field_simp

theorem positiveRange_eq_empty_of_lt_one {A : ℝ} (hA : A < 1) :
    positiveRange A = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨hn, hbound⟩ := mem_positiveRange.mp hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

end Watt41

theorem Watt41.weighted (hWatt : Watt41) {ε : ℝ} (hε : 0 < ε)
    (b fbound : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (hf : ∀ j, 0 ≤ fbound j) :
    ∃ C X₀ : ℝ, 0 ≤ C ∧ 1 ≤ X₀ ∧
      ∀ (q : Watt41.Scales) (δ : ℝ) (σ : ℤ) (a bcoeff : ℕ → ℂ)
        (α β w : ℝ → ℂ) (f : ℕ → ℕ → ℝ → ℝ),
        (∀ i, 1 ≤ q.size i) → 0 < δ → (σ = -1 ∨ σ = 1) →
        Watt41.WeightData b fbound q δ α β w f →
        (∀ r, ‖a r‖ ≤ 1) → (∀ s, ‖bcoeff s‖ ≤ 1) →
        max (q.H^2*q.K) q.L ≤ q.Q^2 → X₀ ≤ q.X →
        ‖Watt41.weightedSum q σ a bcoeff α β w f‖ ≤ C*Watt41.majorant q δ ε := by
  obtain ⟨C,X₀,hC,hX₀,hbound⟩ := hWatt ε hε b hb fbound hf
  refine ⟨C,X₀,hC,hX₀,?_⟩
  intro q δ σ a bcoeff α β w f hsize hδ hσ hweights ha hbcoeff hnum hlarge
  exact (Watt41.norm_weightedSum_le_U q σ a bcoeff α β w f ha hbcoeff).trans
    (hbound q δ σ α β w f hsize hδ hσ hweights hnum hlarge)

end
end DivisorProof
