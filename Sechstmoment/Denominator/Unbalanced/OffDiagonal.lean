import Sechstmoment.Denominator.Unbalanced.Expansion.Mass
import Sechstmoment.Numerator.U.Separation.TimePowerProfileFourier

/-! The one-sided off-diagonal has an arithmetic gap depending only on
the three positive profile lengths. This gap holds for the entire infinite
exponentially smoothed pair, including every noncomparable pair. -/
namespace Sechstmoment
open Complex Real Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

theorem d04_nat_log_ratio_gap {T P : ℝ} (hT : 1 ≤ T) (hP : 0 ≤ P)
    {A B : ℕ} (hA : 0 < A) (hB : 0 < B) (hne : A ≠ B)
    (hcap : (B : ℝ) ≤ T ^ P) :
    (1 / 4 : ℝ) * T ^ (1 - P) ≤
      |T * Real.log ((A : ℝ) / (B : ℝ))| := by
  have ht : 0 < T := zero_lt_one.trans_le hT
  have ha : 0 < (A : ℝ) := by exact_mod_cast hA
  have hb : 0 < (B : ℝ) := by exact_mod_cast hB
  have htp : 0 < T ^ P := Real.rpow_pos_of_pos ht _
  have hbound : 1 / (4 * T ^ P) ≤ |Real.log ((A : ℝ) / (B : ℝ))| := by
    by_cases hcomp : (A : ℝ) ≤ 2 * (B : ℝ)
    · have hroot : Real.sqrt ((A : ℝ) * (B : ℝ)) ≤ 2 * T ^ P := by
        have hsq := Real.sq_sqrt (mul_pos ha hb).le
        have hprod : (A : ℝ) * (B : ℝ) ≤ 2 * (B : ℝ) ^ (2 : ℕ) := by
          nlinarith
        have hb2 : (B : ℝ) ^ (2 : ℕ) ≤ (T ^ P) ^ (2 : ℕ) :=
          pow_le_pow_left₀ hb.le hcap _
        nlinarith [Real.sqrt_nonneg ((A : ℝ) * (B : ℝ))]
      have hrootp : 0 < 2 * Real.sqrt ((A : ℝ) * (B : ℝ)) := by positivity
      exact (one_div_le_one_div_of_le hrootp (by linarith)).trans
        (d02_nat_log_ratio_separation hA hB hne)
    · have hratio : (2 : ℝ) ≤ (A : ℝ) / (B : ℝ) :=
        (le_div_iff₀ hb).2 (le_of_lt (lt_of_not_ge hcomp))
      have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at hh ⊢
        exact hh
      have hpow : 1 ≤ T ^ P := Real.one_le_rpow hT hP
      have hsmall : 1 / (4 * T ^ P) ≤ (1 / 2 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      exact hsmall.trans (hhalf.trans ((Real.log_le_log (by norm_num) hratio).trans
        (le_abs_self _)))
  have hh := mul_le_mul_of_nonneg_left hbound ht.le
  rw [abs_mul, abs_of_pos ht]
  apply le_trans _ hh
  rw [Real.rpow_sub ht, Real.rpow_one]
  field_simp
  norm_num

/-- Fixed-profile integration by parts works for the complete infinite
exponential series. The coefficient premise is a pointwise literal majorant,
not an off-diagonal error estimate. -/
theorem d04_exponential_offDiagonal_fourier_bound {Φ : ℝ → ℂ}
    (hΦK : HasCompactSupport Φ) (hΦ : ContDiff ℝ ∞ Φ)
    {P : ℝ} (hP : 0 ≤ P) (N : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ T : ℝ, 1 ≤ T → ∀ H K : ℕ,
      0 < H → 0 < K → (H : ℝ) ≤ T ^ P → ∀ C : ℝ, 0 ≤ C →
      ∀ c : ℕ × ℕ → ℂ,
      (∀ n, ‖c n‖ ≤ C * d04ExponentialPairWeight T n) →
      Summable (fun n : ℕ × ℕ =>
        if (n.1 + 1) * (n.2 + 1) * K = H then 0 else
          c n * a03ProfileTimeFourier Φ T
            (Real.log ((((n.1 + 1) * (n.2 + 1) * K : ℕ) : ℝ) / (H : ℝ)))) ∧
      ‖∑' n : ℕ × ℕ,
        if (n.1 + 1) * (n.2 + 1) * K = H then 0 else
          c n * a03ProfileTimeFourier Φ T
            (Real.log ((((n.1 + 1) * (n.2 + 1) * K : ℕ) : ℝ) / (H : ℝ)))‖ ≤
        D * C * T ^ (7 - (1 - P) * (N : ℝ)) := by
  obtain ⟨D₀, hD₀, hd⟩ := a03_profile_scaled_time_decay hΦK hΦ N
  refine ⟨9 * 4 ^ N * D₀, by positivity, ?_⟩
  intro T hT H K hH hK hHcap C hC c hc
  have ht : 0 < T := zero_lt_one.trans_le hT
  let ℓ : ℕ × ℕ → ℝ := fun n =>
    Real.log ((((n.1 + 1) * (n.2 + 1) * K : ℕ) : ℝ) / (H : ℝ))
  let v : ℕ × ℕ → ℂ := fun n =>
    if (n.1 + 1) * (n.2 + 1) * K = H then 0 else c n * a03ProfileTimeFourier Φ T (ℓ n)
  let B : ℝ := 4 ^ N * D₀ * T ^ (1 - (1 - P) * (N : ℝ))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hv (n : ℕ × ℕ) : ‖v n‖ ≤ B * ‖c n‖ := by
    dsimp [v]
    split_ifs with hne
    · simp only [norm_zero]
      positivity
    · have hfloor := d04_nat_log_ratio_gap hT hP
        (Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) hK) hH hne hHcap
      have hlower : 0 < T * |ℓ n| := by
        have hh := (by positivity : (0 : ℝ) < (1 / 4 : ℝ) * T ^ (1 - P)).trans_le hfloor
        simpa only [abs_mul, abs_of_pos ht] using hh
      have hlne : ℓ n ≠ 0 := by
        intro hz
        simp only [hz, abs_zero, mul_zero] at hlower
        exact lt_irrefl 0 hlower
      have hfreq : ((1 / 4 : ℝ) * T ^ (1 - P)) ^ N ≤ (T * |ℓ n|) ^ N := by
        apply pow_le_pow_left₀ (by positivity)
        simpa only [abs_mul, abs_of_pos ht] using hfloor
      have htime : ‖a03ProfileTimeFourier Φ T (ℓ n)‖ ≤ B := by
        calc
          _ ≤ D₀ * T / (T * |ℓ n|) ^ N := hd T ht (ℓ n) hlne
          _ ≤ D₀ * T / ((1 / 4 : ℝ) * T ^ (1 - P)) ^ N :=
            div_le_div_of_nonneg_left (mul_nonneg hD₀ ht.le) (by positivity) hfreq
          _ = B := by
            dsimp [B]
            have hpT : (T ^ (1 - P)) ^ N = T ^ ((1 - P) * (N : ℝ)) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
            rw [mul_pow, one_div_pow, hpT, div_mul_eq_mul_div, one_mul,
              div_div_eq_mul_div, Real.rpow_sub ht, Real.rpow_one]
            ring
      rw [norm_mul]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left htime (norm_nonneg (c n))
  obtain ⟨hs, hm⟩ := d04_exponential_coefficient_mass hT hC c hc
  have hvs : Summable (fun n => ‖v n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg (v n)) hv (hs.mul_left B)
  refine ⟨hvs.of_norm, ?_⟩
  calc
    _ ≤ ∑' n, ‖v n‖ := norm_tsum_le_tsum_norm hvs
    _ ≤ ∑' n, B * ‖c n‖ := hvs.tsum_le_tsum hv (hs.mul_left B)
    _ = B * ∑' n, ‖c n‖ := tsum_mul_left
    _ ≤ B * (9 * C * T ^ (6 : ℕ)) := mul_le_mul_of_nonneg_left hm hB
    _ = _ := by
      dsimp [B]
      have hpTotal : T ^ (7 - (1 - P) * (N : ℝ)) =
          T ^ (1 - (1 - P) * (N : ℝ)) * T ^ (6 : ℕ) := by
        rw [show 7 - (1 - P) * (N : ℝ) = (1 - (1 - P) * (N : ℝ)) + 6 by ring,
          Real.rpow_add ht]
        norm_num
      rw [hpTotal]
      ring

/-- The condition on the three row lengths, `P < 1`, is precisely what
permits an arbitrary integration-by-parts order. -/
theorem d04_oneSided_offDiagonal_exists_order {P : ℝ} (hP : P < 1)
    (Q A : ℝ) : ∃ N : ℕ, 7 + Q - (1 - P) * (N : ℝ) ≤ -A := by
  have hp : 0 < 1 - P := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((7 + Q + A) / (1 - P))
  refine ⟨N, ?_⟩
  have hh := (div_lt_iff₀ hp).1 hN
  linarith

theorem d04_exponential_offDiagonal_arbitrary_power {Φ : ℝ → ℂ}
    (hΦK : HasCompactSupport Φ) (hΦ : ContDiff ℝ ∞ Φ)
    {P : ℝ} (hP0 : 0 ≤ P) (hP1 : P < 1) (Q A : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ T : ℝ, 1 ≤ T → ∀ H K : ℕ,
      0 < H → 0 < K → (H : ℝ) ≤ T ^ P → ∀ C : ℝ, 0 ≤ C →
      ∀ c : ℕ × ℕ → ℂ,
      (∀ n, ‖c n‖ ≤ C * T ^ Q * d04ExponentialPairWeight T n) →
      ‖∑' n : ℕ × ℕ,
        if (n.1 + 1) * (n.2 + 1) * K = H then 0 else
          c n * a03ProfileTimeFourier Φ T
            (Real.log ((((n.1 + 1) * (n.2 + 1) * K : ℕ) : ℝ) / (H : ℝ)))‖ ≤
        D * C * T ^ (-A) := by
  obtain ⟨N, hN⟩ := d04_oneSided_offDiagonal_exists_order hP1 Q A
  obtain ⟨D, hD, hd⟩ := d04_exponential_offDiagonal_fourier_bound hΦK hΦ hP0 N
  refine ⟨D, hD, ?_⟩
  intro T hT H K hH hK hcap C hC c hc
  have ht : 0 < T := zero_lt_one.trans_le hT
  have hz := (hd T hT H K hH hK hcap (C * T ^ Q)
    (mul_nonneg hC (Real.rpow_nonneg ht.le _)) c hc).2
  calc
    _ ≤ D * (C * T ^ Q) * T ^ (7 - (1 - P) * (N : ℝ)) := hz
    _ = D * C * T ^ (7 + Q - (1 - P) * (N : ℝ)) := by
      rw [show 7 + Q - (1 - P) * (N : ℝ) = Q + (7 - (1 - P) * (N : ℝ)) by ring,
        Real.rpow_add ht]
      ring
    _ ≤ D * C * T ^ (-A) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT hN) (mul_nonneg hD hC)

theorem d04_exponential_offDiagonal_sum_bound {T C B : ℝ}
    (hT : 1 ≤ T) (hC : 0 ≤ C) (hB : 0 ≤ B) (H K : ℕ)
    (F : ℝ → ℂ) (c : ℕ × ℕ → ℂ)
    (hc : ∀ n, ‖c n‖ ≤ C * d04ExponentialPairWeight T n)
    (hb : ∀ n : ℕ × ℕ, (n.1+1)*(n.2+1)*K ≠ H →
      ‖a03ProfileTimeFourier F T
        (Real.log ((((n.1+1)*(n.2+1)*K : ℕ) : ℝ)/(H : ℝ)))‖ ≤ B) :
    Summable (fun n : ℕ × ℕ => if (n.1+1)*(n.2+1)*K = H then 0 else
      c n * a03ProfileTimeFourier F T
        (Real.log ((((n.1+1)*(n.2+1)*K : ℕ) : ℝ)/(H : ℝ)))) ∧
    ‖∑' n : ℕ × ℕ, if (n.1+1)*(n.2+1)*K = H then 0 else
      c n * a03ProfileTimeFourier F T
        (Real.log ((((n.1+1)*(n.2+1)*K : ℕ) : ℝ)/(H : ℝ)))‖ ≤
      9 * C * B * T ^ (6 : ℕ) := by
  let v : ℕ × ℕ → ℂ := fun n => if (n.1+1)*(n.2+1)*K = H then 0 else
    c n * a03ProfileTimeFourier F T
      (Real.log ((((n.1+1)*(n.2+1)*K : ℕ) : ℝ)/(H : ℝ)))
  obtain ⟨hs, hm⟩ := d04_exponential_coefficient_mass hT hC c hc
  have hv (n : ℕ × ℕ) : ‖v n‖ ≤ B * ‖c n‖ := by
    dsimp [v]
    split_ifs with hn
    · simp only [norm_zero]; positivity
    · rw [norm_mul]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb n hn) (norm_nonneg (c n))
  have hvs := Summable.of_nonneg_of_le (fun n => norm_nonneg (v n)) hv (hs.mul_left B)
  refine ⟨hvs.of_norm, ?_⟩
  calc
    _ ≤ ∑' n, ‖v n‖ := norm_tsum_le_tsum_norm hvs
    _ ≤ ∑' n, B * ‖c n‖ := hvs.tsum_le_tsum hv (hs.mul_left B)
    _ = B * ∑' n, ‖c n‖ := tsum_mul_left
    _ ≤ B * (9 * C * T ^ (6 : ℕ)) := mul_le_mul_of_nonneg_left hm hB
    _ = _ := by ring

/-- Uniform PI for the actual normalized-time complex power retained by
the shifted single-chi leading term. -/
theorem d04_exponential_offDiagonal_timePower_uniform_bound {Φ : ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc (1 : ℝ) 2)
    {P R : ℝ} (hP : 0 ≤ P) (hR : 0 ≤ R) (N : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ T : ℝ, 1 ≤ T → ∀ H K : ℕ,
      0 < H → 0 < K → (H : ℝ) ≤ T ^ P → ∀ τ : ℂ, ‖τ‖ ≤ R →
      ∀ C : ℝ, 0 ≤ C → ∀ c : ℕ × ℕ → ℂ,
      (∀ n, ‖c n‖ ≤ C * d04ExponentialPairWeight T n) →
      Summable (fun n : ℕ × ℕ =>
        if (n.1+1)*(n.2+1)*K = H then 0 else c n *
          a03ProfileTimeFourier (a03ProfileProduct Φ (fun y : ℝ => (y : ℂ)^τ)) T
            (Real.log ((((n.1+1)*(n.2+1)*K : ℕ) : ℝ)/(H : ℝ)))) ∧
      ‖∑' n : ℕ × ℕ, if (n.1+1)*(n.2+1)*K = H then 0 else c n *
        a03ProfileTimeFourier (a03ProfileProduct Φ (fun y : ℝ => (y : ℂ)^τ)) T
          (Real.log ((((n.1+1)*(n.2+1)*K : ℕ) : ℝ)/(H : ℝ)))‖ ≤
        D * C * T ^ (7 - (1-P)*(N : ℝ)) := by
  obtain ⟨D₀, hD₀, hd⟩ := a03TimePowerProfile_fourier_decay hΦ hΦs hR N
  let D₁ : ℝ := D₀ * (1+R)^N
  have hD₁ : 0 ≤ D₁ := by dsimp [D₁]; positivity
  refine ⟨9 * 4^N * D₁, by positivity, ?_⟩
  intro T hT H K hH hK hcap τ hτ C hC c hc
  have ht : 0 < T := zero_lt_one.trans_le hT
  let B : ℝ := 4^N * D₁ * T ^ (1-(1-P)*(N : ℝ))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (n : ℕ × ℕ) (hn : (n.1+1)*(n.2+1)*K ≠ H) :
      ‖a03ProfileTimeFourier (a03ProfileProduct Φ (fun y : ℝ => (y : ℂ)^τ)) T
        (Real.log ((((n.1+1)*(n.2+1)*K : ℕ) : ℝ)/(H : ℝ)))‖ ≤ B := by
    let ℓ : ℝ := Real.log ((((n.1+1)*(n.2+1)*K : ℕ) : ℝ)/(H : ℝ))
    have hfloor := d04_nat_log_ratio_gap hT hP
      (Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) hK) hH hn hcap
    have hp : ((1/4 : ℝ)*T^(1-P))^N ≤ (1+|T*ℓ|)^N := by
      exact pow_le_pow_left₀ (by positivity) (hfloor.trans (by linarith [abs_nonneg (T*ℓ)])) N
    have hqre : τ.re ≤ R := (Complex.re_le_norm τ).trans hτ
    have hqpow : (1+‖τ‖)^N ≤ (1+R)^N := pow_le_pow_left₀ (by positivity) (by linarith) N
    have hbound := (mul_le_mul_of_nonneg_right hp
      (norm_nonneg (profileLaplaceTransform
        (a03ProfileProduct Φ (fun y : ℝ => (y : ℂ)^τ)) (((T*ℓ : ℝ) : ℂ)*I)))).trans
      ((hd τ hqre (T*ℓ)).trans (mul_le_mul_of_nonneg_left hqpow hD₀))
    have hpos : 0 < ((1/4 : ℝ)*T^(1-P))^N := by positivity
    have hdiv : ‖profileLaplaceTransform
        (a03ProfileProduct Φ (fun y : ℝ => (y : ℂ)^τ)) (((T*ℓ : ℝ) : ℂ)*I)‖ ≤
        D₁ / ((1/4 : ℝ)*T^(1-P))^N :=
      (le_div_iff₀ hpos).2 (by simpa only [mul_comm] using hbound)
    rw [a03_profile_time_fourier_rescaling _ ht, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg ht.le]
    calc
      _ ≤ T * (D₁ / ((1/4 : ℝ)*T^(1-P))^N) := mul_le_mul_of_nonneg_left hdiv ht.le
      _ = B := by
        dsimp [B]
        have hpT : (T^(1-P))^N = T^((1-P)*(N : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
        rw [mul_pow, one_div_pow, hpT, div_mul_eq_mul_div, one_mul,
          div_div_eq_mul_div, Real.rpow_sub ht, Real.rpow_one]
        ring
  obtain ⟨hs, hbnd⟩ := d04_exponential_offDiagonal_sum_bound hT hC hB H K _ c hc hb
  refine ⟨hs, hbnd.trans_eq ?_⟩
  dsimp [B]
  have hpTotal : T^(7-(1-P)*(N : ℝ)) = T^(1-(1-P)*(N : ℝ))*T^(6 : ℕ) := by
    rw [show 7-(1-P)*(N : ℝ) = (1-(1-P)*(N : ℝ))+6 by ring,
      Real.rpow_add ht]
    norm_num
  rw [hpTotal]
  ring

end
end Sechstmoment
