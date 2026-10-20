import SixthMoment.Numerator.U.Separation.ActualSeparatedGap
import SixthMoment.Numerator.U.Separation.PhaseCoefficientBounds

namespace SixthMoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem phaseActualAmplifierCoefficient_support (T : ℝ) (f : ℝ → ℝ)
    {A : ℝ} (hA : 0<A) :
    ∀ a : ℕ, (a:ℝ)∉Icc A (2*A) → phaseActualAmplifierCoefficient T f A a=0 := by
  intro a ha
  have hw : rectangularSmoothBlockWeight ((a:ℝ)/A)=0 := by
    by_contra hn
    have hs := rectangularSmoothBlockWeight_tsupport (subset_tsupport _ hn)
    apply ha
    constructor
    · have he := (le_div_iff₀ hA).mp hs.1
      simpa only [one_mul] using he
    · exact (div_le_iff₀ hA).mp hs.2
  simp only [phaseActualAmplifierCoefficient,hw,Complex.ofReal_zero,zero_mul]

theorem phaseActualAmplifierCoefficient_norm_le (T : ℝ) (f : ℝ → ℝ)
    {A F : ℝ} (_hA : 0<A) (hF : 0≤F) (hf : ∀ x, ‖f x‖≤F) (a : ℕ) :
    ‖phaseActualAmplifierCoefficient T f A a‖≤F := by
  by_cases ha : a=0
  · subst a
    have hw : rectangularSmoothBlockWeight ((0:ℝ)/A)=0 := by
      rw [zero_div]
      exact rectangularSmoothBlockWeight_zero_le (by norm_num)
    simp only [phaseActualAmplifierCoefficient,Nat.cast_zero,hw,Complex.ofReal_zero,zero_mul,norm_zero]
    exact hF
  · have hap : 0<(a:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero ha
    have ha1 : 1≤(a:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ha
    have hp : ‖(a:ℂ)^(-(1/2:ℂ))‖≤1 := by
      have h := Complex.norm_cpow_eq_rpow_re_of_pos hap (-(1/2:ℂ))
      push_cast at h
      rw [h]
      calc
        _ ≤ (a:ℝ)^(0:ℝ) := Real.rpow_le_rpow_of_exponent_le ha1 (by norm_num)
        _ = _ := Real.rpow_zero _
    unfold phaseActualAmplifierCoefficient
    rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real]
    rw [Real.norm_eq_abs,abs_of_nonneg (rectangularSmoothBlockWeight_nonneg _)]
    calc
      _ ≤ (1*F)*1 := by
        gcongr
        · exact rectangularSmoothBlockWeight_le_one _
        · exact hf _
      _ = _ := by ring

theorem phaseActualAmplifierCoefficient_uniform {a : ℝ} (f : ℝ → ℝ)
    (hf : SmoothInteriorProfile a f) :
    ∃ F : ℝ, 0≤F ∧ ∀ T A : ℝ, 0<A →
      (∀ n : ℕ, (n:ℝ)∉Icc A (2*A) → phaseActualAmplifierCoefficient T f A n=0) ∧
      (∀ n : ℕ, ‖phaseActualAmplifierCoefficient T f A n‖≤F) := by
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  exact ⟨F,hF,fun T A hA => ⟨phaseActualAmplifierCoefficient_support T f hA,
    phaseActualAmplifierCoefficient_norm_le T f hA hF hfb⟩⟩

theorem phaseActualAdjustedBeta_uniform {b : ℝ} (g : ℝ → ℝ)
    (hg : SmoothInteriorProfile b g) :
    ∃ F : ℝ, 0≤F ∧ ∀ T : ℝ, ∀ q : QuadraticScales, 0<q.B → ∀ k : ℕ,
      (∀ n : ℕ, (n:ℝ)∉Icc q.B (2*q.B) →
        phaseAdjustedBeta q (phaseActualAmplifierCoefficient T g q.B) k n=0) ∧
      (∀ n : ℕ, ‖phaseAdjustedBeta q (phaseActualAmplifierCoefficient T g q.B) k n‖≤F) := by
  obtain ⟨F,hF,hfb⟩ := phaseActualAmplifierCoefficient_uniform g hg
  refine ⟨F,hF,?_⟩
  intro T q hB k
  have hs := (hfb T q.B hB).1
  refine ⟨phaseAdjustedBeta_support q _ hs k,?_⟩
  intro n
  exact (phaseAdjustedBeta_norm_le q hB _ hs k n).trans ((hfb T q.B hB).2 n)

end
end SixthMoment
