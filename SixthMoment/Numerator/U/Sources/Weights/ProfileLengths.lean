import Mathlib.Topology.Order.Compact
import SixthMoment.Numerator.U.Separation.ActualAmplifierCoefficients

namespace SixthMoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem phase_profile_positive_lower_endpoint {a : ℝ} (f : ℝ → ℝ)
    (hf : SmoothInteriorProfile a f) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ x : ℝ, f x ≠ 0 → ν ≤ x := by
  by_cases hs : (tsupport f).Nonempty
  · obtain ⟨ν, hν⟩ := hf.2.1.exists_isLeast hs
    exact ⟨ν, (hf.2.2 hν.1).1, fun x hx => hν.2 (subset_tsupport f hx)⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx
    exact (hs ⟨x, subset_tsupport f hx⟩).elim

theorem phase_actual_nonzero_amplifier_lengths {a : ℝ} (f : ℝ → ℝ)
    (hf : SmoothInteriorProfile a f) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ T A : ℝ, 1 < T → 0 < A → ∀ n : ℕ,
      phaseActualAmplifierCoefficient T f A n ≠ 0 →
      T^ν ≤ 2*A ∧ A ≤ T^a := by
  obtain ⟨ν, hν, hfν⟩ := phase_profile_positive_lower_endpoint f hf
  refine ⟨ν, hν, ?_⟩
  intro T A hT hA n hn
  have hns : (n:ℝ) ∈ Icc A (2*A) := by
    by_contra h
    exact hn (phaseActualAmplifierCoefficient_support T f hA n h)
  have hfn : f (Real.log (n:ℝ)/Real.log T) ≠ 0 := by
    intro h
    apply hn
    simp only [phaseActualAmplifierCoefficient, h, Complex.ofReal_zero, mul_zero, zero_mul]
  have hnpos : 0 < (n:ℝ) := hA.trans_le hns.1
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hlower : ν*Real.log T ≤ Real.log (n:ℝ) :=
    (le_div_iff₀ hlog).mp (hfν _ hfn)
  have hupper : Real.log (n:ℝ) ≤ a*Real.log T :=
    (div_le_iff₀ hlog).mp (hf.2.2 (subset_tsupport f hfn)).2.le
  exact ⟨((Real.rpow_le_iff_le_log (zero_lt_one.trans hT) hnpos).mpr hlower).trans hns.2,
    hns.1.trans (Real.le_rpow_of_log_le (zero_lt_one.trans hT) hupper)⟩

theorem phase_actual_amplifier_product_lengths {a b : ℝ} (f g : ℝ → ℝ)
     (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
     ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℝ, 0 < A → 0 < B →
       ∀ m n : ℕ, phaseActualAmplifierCoefficient T f A m ≠ 0 →
       phaseActualAmplifierCoefficient T g B n ≠ 0 →
       T^ρ ≤ A*B ∧ A*B ≤ T^(a+b) := by
   obtain ⟨ν,hν,hfν⟩ := phase_actual_nonzero_amplifier_lengths f hf
   obtain ⟨μ,hμ,hgμ⟩ := phase_actual_nonzero_amplifier_lengths g hg
   let ρ : ℝ := (ν+μ)/2
   have hρ : 0 < ρ := by dsimp [ρ]; linarith
   refine ⟨ρ,hρ,?_⟩
   have ht : ∀ᶠ T : ℝ in atTop, 4 ≤ T^ρ := (tendsto_rpow_atTop hρ).eventually_ge_atTop 4
   filter_upwards [ht,eventually_gt_atTop (1:ℝ)] with T hfour hT
   intro A B hA hB m n hm hn
   have hf' := hfν T A hT hA m hm
   have hg' := hgμ T B hT hB n hn
   have hTp : 0 < T := zero_lt_one.trans hT
   have hp := mul_le_mul hf'.1 hg'.1 (Real.rpow_nonneg hTp.le μ) (by positivity : 0≤2*A)
   have he : T^ν*T^μ=(T^ρ)^2 := by
     rw [← Real.rpow_add hTp,← Real.rpow_natCast (T^ρ) 2,← Real.rpow_mul hTp.le]
     congr 1
     dsimp [ρ]
     ring
   rw [he] at hp
   have hupper := mul_le_mul hf'.2 hg'.2 hB.le (Real.rpow_nonneg hTp.le a)
   rw [← Real.rpow_add hTp] at hupper
   exact ⟨by nlinarith,hupper⟩

end
end SixthMoment
