import Sechstmoment.Denominator.Balanced.NormalizedHeightBudget
import Sechstmoment.Denominator.Unbalanced.FiniteMainTerm

/-! The literal four-profile coefficient mass closes the one-sided
off-diagonal estimate uniformly over compact normalized shift boxes. -/
namespace Sechstmoment
open Complex Real Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

def d04OneSidedModelOffDiagonal (T : ℝ) (a : Fin 4 → ℝ)
    (ρ : Fin 4 → ℝ → ℝ) (σ : Fin 2 → ℂ) (τ : ℂ) (Φ : ℝ → ℂ) : ℂ :=
  ∑ h∈d04ProfileBox T a, ∑' n : ℕ × ℕ,
    if d04OneSidedModelDiagonal h n then 0 else
      d04OneSidedModelCoefficient T ρ σ h n *
        a03ProfileTimeFourier (a03ProfileProduct Φ (fun y : ℝ => (y : ℂ)^τ)) T
          (d04OneSidedModelFrequency h n)

theorem d04_oneSided_model_offDiagonal_uniform_power_bound {Φ : ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc (1 : ℝ) 2)
    (a : Fin 4 → ℝ) (ha : ∀ j, 0≤a j) (haP : a 0+a 1+a 2<1)
    {R R' F : ℝ} (hR : 0≤R) (hR' : 0≤R') (hF : 0≤F) (A : ℝ) :
    ∃ D : ℝ, 0≤D ∧ ∀ T : ℝ, 1<T → 1≤Real.log T → 2*R≤Real.log T →
      ∀ (ρ : Fin 4 → ℝ → ℝ) (σ : Fin 2 → ℂ) (τ : ℂ),
      (∀ j x, |ρ j x|≤F) → (∀ j, ‖σ j‖≤R) → ‖τ‖≤R' →
      ‖d04OneSidedModelOffDiagonal T a ρ σ τ Φ‖ ≤ D*T^(-A) := by
  let P : ℝ := a 0+a 1+a 2
  let S : ℝ := ∑ j,a j
  have hP : 0≤P := by dsimp [P]; linarith [ha 0,ha 1,ha 2]
  obtain ⟨N,hN⟩ := d04_oneSided_offDiagonal_exists_order haP (S/2) A
  obtain ⟨D₀,hD₀,hd⟩ := d04_exponential_offDiagonal_timePower_uniform_bound hΦ hΦs hP hR' N
  let C : ℝ := D₀*Real.exp R*F^4*2^4
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro T hT hL hRL ρ σ τ hρ hσ hτ
  have ht : 0<T := zero_lt_one.trans hT
  have hl : 0<Real.log T := zero_lt_one.trans_le hL
  let v : (Fin 4 → ℕ) → ℂ := fun h => ∑' n : ℕ × ℕ,
    if d04OneSidedModelDiagonal h n then 0 else
      d04OneSidedModelCoefficient T ρ σ h n *
        a03ProfileTimeFourier (a03ProfileProduct Φ (fun y : ℝ => (y : ℂ)^τ)) T
          (d04OneSidedModelFrequency h n)
  have hv (h : Fin 4 → ℕ) (hh : h∈d04ProfileBox T a) :
      ‖v h‖ ≤ (D₀*Real.exp R*T^(7-(1-P)*(N : ℝ)))*‖d04ProfileCoefficient T ρ h‖ := by
    have hc (n : ℕ × ℕ) : ‖d04OneSidedModelCoefficient T ρ σ h n‖ ≤
        (‖d04ProfileCoefficient T ρ h‖*Real.exp R)*d04ExponentialPairWeight T n := by
      unfold d04OneSidedModelCoefficient
      rw [norm_mul]
      have hn := mul_le_mul_of_nonneg_left
        (d04_oneSided_pair_coefficient_norm_le ht hR hl hRL σ hσ n)
        (norm_nonneg (d04ProfileCoefficient T ρ h))
      simpa only [mul_assoc] using hn
    have hb := (hd T hT.le (d04ProfileH h) (d04ProfileK h)
      (d04ProfileH_pos h) (d04ProfileK_pos h) (d04ProfileH_cap ht a h hh)
      τ hτ (‖d04ProfileCoefficient T ρ h‖*Real.exp R) (by positivity) _ hc).2
    simpa only [v,d04OneSidedModelDiagonal,d04OneSidedModelFrequency,mul_assoc,
      mul_left_comm,mul_comm] using hb
  have hm := d04ProfileCoefficient_mass_le ht hF a ρ hρ
  unfold d04OneSidedModelOffDiagonal
  calc
    _ ≤ ∑ h∈d04ProfileBox T a, ‖v h‖ := norm_sum_le _ _
    _ ≤ ∑ h∈d04ProfileBox T a,
        (D₀*Real.exp R*T^(7-(1-P)*(N : ℝ)))*‖d04ProfileCoefficient T ρ h‖ :=
      Finset.sum_le_sum hv
    _ = (D₀*Real.exp R*T^(7-(1-P)*(N : ℝ)))*
        ∑ h∈d04ProfileBox T a, ‖d04ProfileCoefficient T ρ h‖ := (Finset.mul_sum ..).symm
    _ ≤ (D₀*Real.exp R*T^(7-(1-P)*(N : ℝ)))*(F^4*2^4*T^(S/2)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = C*T^(7+S/2-(1-P)*(N : ℝ)) := by
      dsimp [C]
      rw [show 7+S/2-(1-P)*(N : ℝ)=(7-(1-P)*(N : ℝ))+S/2 by ring,
        Real.rpow_add ht]
      ring
    _ ≤ C*T^(-A) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT.le hN) hC

end
end Sechstmoment
