import Sechstmoment.Arithmetic.Watt.CurveWeights
import Sechstmoment.Arithmetic.Watt.WeightBounds


namespace DivisorProof
namespace Watt41
open Real Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 2000000

theorem weightedBlock_original_support (u : ℝ → ℂ) (A : ℝ) (j : ℕ) :
    tsupport (weightedBlock u A j) ⊆ tsupport u := by
  apply closure_minimal _ (isClosed_tsupport u)
  intro x hx
  apply subset_tsupport
  intro hz
  exact hx (by simp only [weightedBlock,hz,zero_mul])

def oscillatoryBlock (u : ℝ → ℂ) (A : ℝ) (j : ℕ) (y t : ℝ) : ℂ :=
  weightedBlock u A j t*ePhase (y*t)

theorem oscillatoryBlock_smooth {u : ℝ → ℂ} (hu : ContDiff ℝ ∞ u)
    (A : ℝ) (j : ℕ) (y : ℝ) : ContDiff ℝ ∞ (oscillatoryBlock u A j y) := by
  apply (weightedBlock_smooth hu A j).mul
  unfold ePhase
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    (contDiff_const.mul contDiff_id))).cexp

theorem oscillatoryBlock_support {u : ℝ → ℂ} {A : ℝ} (hA : 0 < A)
    (hu : tsupport u ⊆ Icc (1/2) A) (j : ℕ) (y : ℝ) :
    tsupport (oscillatoryBlock u A j y) ⊆ Icc (blockScale A j/2) (blockScale A j) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  apply weightedBlock_support hA hu j
  apply subset_tsupport
  intro hz
  exact ht (by simp only [oscillatoryBlock,hz,zero_mul])

theorem delta_shrink_power {δ Δ x : ℝ} (hδ : 0 < δ) (hδΔ : δ ≤ Δ)
    (hx : 0 < x) (j : ℕ) : (Δ*x)^(-(j : ℝ)) ≤ (δ*x)^(-(j : ℝ)) :=
  Real.rpow_le_rpow_of_nonpos (mul_pos hδ hx)
    (mul_le_mul_of_nonneg_right hδΔ hx.le) (neg_nonpos.mpr (Nat.cast_nonneg j))

theorem frequency_cost_le_delta_power {Δ E x : ℝ} (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1)
    (hE : 1 ≤ E) (hx : 0 < x) (j : ℕ) :
    E^j*x^(-(j : ℝ)) ≤ (Δ/E*x)^(-(j : ℝ)) := by
  have hEp : 0 < E := by linarith
  rw [inverse_scale_derivative_identity hEp hx]
  apply delta_shrink_power (div_pos hΔ hEp) _ hx j
  simpa only [one_div] using div_le_div_of_nonneg_right hΔ₁ hEp.le

theorem oscillatoryBlock_derivative_data (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) :
    ∃ b : ℕ → ℝ, (∀ j, 0 ≤ b j) ∧
      ∀ (u : ℝ → ℂ) (A E y : ℝ), ContDiff ℝ ∞ u → 0 < A → 1 ≤ E →
        tsupport u ⊆ Icc (1/2) A → A*|y| ≤ 4*E →
        (∀ j x, 0 < x → ‖iteratedDeriv j u x‖ ≤ a j*x^(-(j : ℝ))) →
        ∀ k j x, 0 < x →
          ‖iteratedDeriv j (oscillatoryBlock u A k y) x‖ ≤ b j*E^j*x^(-(j : ℝ)) := by
  obtain ⟨c,hc,hcder⟩ := weightedBlock_derivative_data a ha
  let b := oscillatoryDerivativeBound c 2
  have hb (j : ℕ) : 0 ≤ b j := derivativeProductBound_nonneg hc
    (fun j => pow_nonneg (by positivity : 0 ≤ 4*Real.pi*2) j) j
  refine ⟨b,hb,?_⟩
  intro u A E y hu hA hE hs hy hdu k j x hx
  have hdc : ∀ j x, 0 < x →
      ‖iteratedDeriv j (weightedBlock u A k) x‖ ≤ c j*x^(-(j : ℝ)) := by
    intro j x hx
    simpa only [one_mul] using hcder u A 1 hu hA zero_lt_one le_rfl
      (by simpa only [one_mul] using hdu) k j x hx
  apply oscillatory_profile_derivative (weightedBlock_smooth hu A k)
    (L := A/2) (K := 2) (E := E) (x := y) (by positivity) (by norm_num) hE
    (by nlinarith) _ hc hdc j hx
  simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
    (weightedBlock_original_support u A k).trans hs

def blockScales (p : WattScales) (A : ℝ) (i j k : ℕ) : Scales :=
  ⟨blockScale p.H i,blockScale p.C j,blockScale A k,p.P,p.R,p.S⟩

theorem completedBlock_inner_data (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ (g : ℕ → ℕ → ℝ) (p : WattScales) (Δ E A y : ℝ) (a bc : ℕ → ℂ)
        (u₀ u₁ : ℝ → ℂ) (γ : ℕ → ℕ → ℝ → ℝ → ℂ),
        WattWeightData b g p Δ a bc u₀ u₁ γ →
        0 < p.H → 0 < p.C → 0 < Δ → Δ ≤ 1 → 1 ≤ E → 0 < A → A*|y| ≤ 4*E →
        ∀ i j k : ℕ,
          InnerWeightData B (blockScales p A i j k) (Δ/E)
            (weightedBlock u₀ p.H i) (weightedBlock u₁ p.C j)
            (oscillatoryBlock (positiveFrequencyProfile (A/2)) A k y) := by
  obtain ⟨c,hc,hcder⟩ := weightedBlock_derivative_data b hb
  obtain ⟨aω,haω,haωder⟩ := positiveFrequencyProfile_derivative_bounds
  obtain ⟨d,hd,hdder⟩ := oscillatoryBlock_derivative_data aω haω
  refine ⟨fun j => c j+d j,fun j => add_nonneg (hc j) (hd j),?_⟩
  intro g p Δ E A y a bc u₀ u₁ γ hw hH hC hΔ hΔ₁ hE hA hy i j k
  have hEp : 0 < E := by linarith
  have hδ : 0 < Δ/E := div_pos hΔ hEp
  have hδΔ : Δ/E ≤ Δ := div_le_self hΔ.le hE
  have hωs : tsupport (positiveFrequencyProfile (A/2)) ⊆ Icc (1/2) A := by
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
      positiveFrequencyProfile_support (by positivity : 0 < A/2)
  have hd₀ : ∀ j x, 0 < x → ‖iteratedDeriv j u₀ x‖ ≤ b j*(Δ*x)^(-(j : ℝ)) := by
    intro j x hx
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hw.derivatives j x hx)
  have hd₁ : ∀ j x, 0 < x → ‖iteratedDeriv j u₁ x‖ ≤ b j*(Δ*x)^(-(j : ℝ)) := by
    intro j x hx
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans (hw.derivatives j x hx)
  refine ⟨weightedBlock_smooth hw.smooth₀ _ _,weightedBlock_smooth hw.smooth₁ _ _,
    oscillatoryBlock_smooth (positiveFrequencyProfile_smooth _) A k y,
    weightedBlock_support hH hw.support₀ i,weightedBlock_support hC hw.support₁ j,
    oscillatoryBlock_support hA hωs k y,?_,?_,?_⟩
  · intro n x hx
    apply (hcder u₀ p.H Δ hw.smooth₀ hH hΔ hΔ₁ hd₀ i n x hx).trans
    calc
      _ ≤ c n*(Δ/E*x)^(-(n : ℝ)) :=
        mul_le_mul_of_nonneg_left (delta_shrink_power hδ hδΔ hx n) (hc n)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hd n)) (Real.rpow_nonneg (by positivity) _)
  · intro n x hx
    apply (hcder u₁ p.C Δ hw.smooth₁ hC hΔ hΔ₁ hd₁ j n x hx).trans
    calc
      _ ≤ c n*(Δ/E*x)^(-(n : ℝ)) :=
        mul_le_mul_of_nonneg_left (delta_shrink_power hδ hδΔ hx n) (hc n)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hd n)) (Real.rpow_nonneg (by positivity) _)
  · intro n x hx
    have hω := hdder (positiveFrequencyProfile (A/2)) A E y (positiveFrequencyProfile_smooth _)
      hA hE hωs hy (haωder _ (by positivity)) k n x hx
    apply hω.trans
    calc
      _ = d n*(E^n*x^(-(n : ℝ))) := by ring
      _ ≤ d n*(Δ/E*x)^(-(n : ℝ)) :=
        mul_le_mul_of_nonneg_left (frequency_cost_le_delta_power hΔ hΔ₁ hE hx n) (hd n)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hc n)) (Real.rpow_nonneg (by positivity) _)

end
end Watt41
end DivisorProof
