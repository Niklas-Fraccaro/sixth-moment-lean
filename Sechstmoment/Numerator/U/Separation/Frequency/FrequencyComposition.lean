import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Sechstmoment.Numerator.U.Separation.Frequency.Composition

namespace Sechstmoment
open Set
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

theorem phase_frequency_decay_one_add {ξ v A B : ℝ} (hv : 0 ≤ v) (n : ℕ)
    (h₀ : v ≤ A) (hₙ : |ξ|^n*v ≤ B) :
    (1+|ξ|)^n*v ≤ 2^n*(A+B) := by
  have hp : (1+|ξ|)^n ≤ (2:ℝ)^n*(1+|ξ|^n) := by
    apply (add_pow_le (by norm_num : (0:ℝ) ≤ 1) (abs_nonneg ξ) n).trans
    rw [one_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.sub_le n 1)) (by positivity)
  calc
    _ ≤ (2:ℝ)^n*(1+|ξ|^n)*v := mul_le_mul_of_nonneg_right hp hv
    _ = 2^n*(v+|ξ|^n*v) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add h₀ hₙ) (by positivity)

def phaseFrequencyCompositionBudget (C : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i∈Finset.range (n+1), (C i 0+C i n)

def phaseSymbolCompositionBudget (B : ℕ → ℝ) (n : ℕ) : ℝ :=
  1+∑ i∈Finset.range (n+1), B i

theorem phase_frequency_composition_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {g : ℝ → ℂ} {s : Set E}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hs : UniqueDiffOn ℝ s) {x : E} (hx : x∈s)
    (C : ℕ → ℕ → ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (B : ℕ → ℝ) (hB : ∀ i, 0 ≤ B i)
    {D R L : ℝ} (hD : 0 ≤ D) (hR : 1 ≤ R) (hL : 0 ≤ L)
    (hfreq : R ≤ L*(1+|f x|))
    (hdecay : ∀ i j, |f x|^j*‖iteratedDeriv i g (f x)‖ ≤ C i j*D)
    (hsymbol : ∀ i, 1 ≤ i → ‖iteratedFDerivWithin ℝ i f s x‖ ≤ B i*R)
    (n : ℕ) :
    ‖iteratedFDerivWithin ℝ n (g ∘ f) s x‖ ≤
      ((n.factorial:ℝ)*(2^n*L^n*phaseFrequencyCompositionBudget C n)*
        (phaseSymbolCompositionBudget B n)^n)*D := by
  have hbudget : 0 ≤ phaseFrequencyCompositionBudget C n := by
    unfold phaseFrequencyCompositionBudget
    apply Finset.sum_nonneg
    intro i _
    exact add_nonneg (hC i 0) (hC i n)
  have hsymbolbudget : 1 ≤ phaseSymbolCompositionBudget B n := by
    dsimp [phaseSymbolCompositionBudget]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hB i))
  have hb (i : ℕ) (hi : i ≤ n) : B i ≤ phaseSymbolCompositionBudget B n := by
    have hmem : i∈Finset.range (n+1) := Finset.mem_range.mpr (by omega)
    have hsingle := Finset.single_le_sum (fun j _ => hB j) hmem
    dsimp [phaseSymbolCompositionBudget]
    linarith
  have hc (i : ℕ) (hi : i ≤ n) : C i 0+C i n ≤ phaseFrequencyCompositionBudget C n := by
    unfold phaseFrequencyCompositionBudget
    exact Finset.single_le_sum (fun j _ => add_nonneg (hC j 0) (hC j n))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  have houter (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i g univ (f x)‖ ≤
        ((2^n*L^n*phaseFrequencyCompositionBudget C n)*D)/R^n := by
    rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    apply (le_div_iff₀ (pow_pos (zero_lt_one.trans_le hR) n)).mpr
    have h₀ : ‖iteratedDeriv i g (f x)‖ ≤ C i 0*D := by
      simpa only [pow_zero, one_mul] using hdecay i 0
    have hp := phase_frequency_decay_one_add (ξ := f x)
      (norm_nonneg (iteratedDeriv i g (f x))) n h₀ (hdecay i n)
    calc
      _ ≤ ‖iteratedDeriv i g (f x)‖*(L*(1+|f x|))^n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hfreq n) (norm_nonneg _)
      _ = L^n*((1+|f x|)^n*‖iteratedDeriv i g (f x)‖) := by rw [mul_pow]; ring
      _ ≤ L^n*(2^n*(C i 0*D+C i n*D)) :=
        mul_le_mul_of_nonneg_left hp (pow_nonneg hL n)
      _ ≤ L^n*(2^n*(phaseFrequencyCompositionBudget C n*D)) := by
        rw [← add_mul]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hc i hi) hD) (by positivity))
          (pow_nonneg hL n)
      _ = _ := by ring
  have hinner (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i f s x‖ ≤
        (phaseSymbolCompositionBudget B n*R)^i := by
    apply phase_linear_derivative_growth_to_geometric hR hsymbolbudget hi
    exact (hsymbol i hi).trans (mul_le_mul_of_nonneg_right (hb i hin) (by linarith))
  have h := phase_composition_frequency_cancellation_on hf hg.contDiffOn hs
    uniqueDiffOn_univ (mapsTo_univ _ _) n hx (zero_lt_one.trans_le hR) houter hinner
  exact h.trans_eq (by ring)

end
end Sechstmoment
