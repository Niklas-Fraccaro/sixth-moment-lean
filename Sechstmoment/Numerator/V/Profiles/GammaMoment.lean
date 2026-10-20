import Sechstmoment.Arithmetic.Euler.Remainder.Factorization
import Sechstmoment.Numerator.V.Profiles.ProfileProduct


namespace Sechstmoment.Source.NoDPHarmonic
open Real Complex MeasureTheory Set Polynomial NoDPGlobalRest
open scoped BigOperators Topology
noncomputable section

theorem divisorLogWeight_le_rpow {ρ : ℝ} (hρ : 0 < ρ) {d e : ℕ}
    (hd : 1 ≤ d) (he : 1 ≤ e) :
    divisorLogWeight d e ≤ (1+1/ρ)*pairWeight ρ (d,e) := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast Nat.zero_lt_of_lt hd
  have he0 : (0:ℝ) < e := by exact_mod_cast Nat.zero_lt_of_lt he
  have hde : (1:ℝ) ≤ (d:ℝ)*e := by
    exact_mod_cast (show 1 ≤ d*e by simpa only [one_mul] using Nat.mul_le_mul hd he)
  have hlog := Real.log_le_rpow_div (le_of_lt (mul_pos hd0 he0)) hρ
  have hpow : 1 ≤ ((d:ℝ)*e)^ρ := Real.one_le_rpow hde hρ.le
  rw [Real.log_mul hd0.ne' he0.ne'] at hlog
  unfold divisorLogWeight pairWeight
  rw [Nat.cast_mul]
  calc
    _ = 1+(Real.log d+Real.log e) := by ring
    _ ≤ ((d:ℝ)*e)^ρ + ((d:ℝ)*e)^ρ/ρ := add_le_add hpow hlog
    _ = _ := by ring

theorem gammaAt_log_pointwise (i : Fin 4) (s : Fin 4 → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (n : ℕ × ℕ) :
    ‖gammaAt i s n‖*divisorLogWeight n.1 n.2 ≤
      (1+1/ρ)*(‖gammaAt i s n‖*pairWeight ρ n) := by
  rcases n with ⟨d,e⟩
  by_cases hd : d = 0
  · subst d
    simp only [gammaAt,gamma_zero_left,norm_zero,zero_mul,mul_zero,le_refl]
  by_cases he : e = 0
  · subst e
    simp only [gammaAt,gamma_zero_right,norm_zero,zero_mul,mul_zero,le_refl]
  calc
    _ ≤ ‖gammaAt i s (d,e)‖*((1+1/ρ)*pairWeight ρ (d,e)) :=
      mul_le_mul_of_nonneg_left (divisorLogWeight_le_rpow hρ
        (Nat.one_le_iff_ne_zero.mpr hd) (Nat.one_le_iff_ne_zero.mpr he)) (norm_nonneg _)
    _ = _ := by ring

theorem divisorLogWeight_nonneg (d e : ℕ) : 0 ≤ divisorLogWeight d e := by
  have hl (n : ℕ) : 0 ≤ Real.log n := by
    by_cases hn : n = 0
    · simp [hn]
    · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  unfold divisorLogWeight
  linarith [hl d,hl e]

theorem gammaAt_log_summable (i : Fin 4) (s : Fin 4 → ℂ) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) :
    Summable (fun n : ℕ × ℕ => ‖gammaAt i s n‖*divisorLogWeight n.1 n.2) :=
  ((gammaAt_weighted_summable i s ρ hρ0.le hρ hs).mul_left (1+1/ρ)).of_nonneg_of_le
    (fun n => mul_nonneg (norm_nonneg (gammaAt i s n)) (divisorLogWeight_nonneg n.1 n.2))
    (gammaAt_log_pointwise i s hρ0)

theorem gammaAt_log_bound (i : Fin 4) (s : Fin 4 → ℂ) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) :
    (∑' n : ℕ × ℕ, ‖gammaAt i s n‖*divisorLogWeight n.1 n.2) ≤
      (1+1/ρ)*globalBound ρ := by
  calc
    _ ≤ ∑' n : ℕ × ℕ, (1+1/ρ)*(‖gammaAt i s n‖*pairWeight ρ n) :=
      (gammaAt_log_summable i s hρ0 hρ hs).tsum_le_tsum (gammaAt_log_pointwise i s hρ0)
        ((gammaAt_weighted_summable i s ρ hρ0.le hρ hs).mul_left _)
    _ = (1+1/ρ)*(∑' n : ℕ × ℕ, ‖gammaAt i s n‖*pairWeight ρ n) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (gammaAt_weighted_bound i s ρ hρ0.le hρ hs) (by positivity)

end
end Sechstmoment.Source.NoDPHarmonic
