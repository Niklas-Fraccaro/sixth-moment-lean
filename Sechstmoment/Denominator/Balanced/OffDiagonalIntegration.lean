import Sechstmoment.Analysis.Fourier.UniformDecay
import Sechstmoment.Arithmetic.Divisors.LogFrequency

/-! Repeated integration by parts for finite balanced denominator sums.
The hypotheses give time regularity and absolute coefficient mass; no
off-diagonal error estimate or moment asymptotic is assumed. -/
namespace Sechstmoment
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

/-- Integration by parts can be summed with the actual derivative and
coefficient budgets retained, even for varying time amplitudes. -/
theorem d02_finite_offDiagonal_fourier_bound {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (f : ι → ℝ → ℂ) (ξ B : ι → ℝ) (N : ℕ)
    (hS : ∀ i ∈ s, ContDiff ℝ ∞ (f i))
    (hsupp : ∀ i ∈ s, tsupport (f i) ⊆ Icc (1 : ℝ) 2)
    (hB : ∀ i ∈ s, ∀ x, ‖iteratedDeriv N (f i) x‖ ≤ B i)
    {frequencyFloor : ℝ} (hFrequency : 0 < frequencyFloor) (hfreq : ∀ i ∈ s, frequencyFloor ≤ |ξ i|) :
    ‖∑ i ∈ s, c i * profileLaplaceTransform (f i) ((ξ i : ℂ) * I)‖ ≤
      (∑ i ∈ s, ‖c i‖ * B i) / frequencyFloor ^ N := by
  have hFrequencyPower : 0 < frequencyFloor ^ N := pow_pos hFrequency N
  apply (le_div_iff₀ hFrequencyPower).2
  calc
    _ ≤ (∑ i ∈ s, ‖c i * profileLaplaceTransform (f i) ((ξ i : ℂ) * I)‖) * frequencyFloor ^ N :=
      mul_le_mul_of_nonneg_right (norm_sum_le _ _) hFrequencyPower.le
    _ = ∑ i ∈ s, frequencyFloor ^ N * ‖c i‖ *
        ‖profileLaplaceTransform (f i) ((ξ i : ℂ) * I)‖ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_mul]
      ring
    _ ≤ ∑ i ∈ s, ‖c i‖ * B i := by
      apply Finset.sum_le_sum
      intro i hi
      have hd := a03_profile_frequency_dyadic_derivative_bound (hS i hi) (hsupp i hi) N (hB i hi) (ξ i)
      have hp : frequencyFloor ^ N ≤ |ξ i| ^ N := pow_le_pow_left₀ hFrequency.le (hfreq i hi) N
      calc
        _ ≤ ‖c i‖ * (|ξ i| ^ N * ‖profileLaplaceTransform (f i) ((ξ i : ℂ) * I)‖) := by
          have hh := mul_le_mul_of_nonneg_right hp (norm_nonneg (profileLaplaceTransform (f i) ((ξ i : ℂ) * I)))
          simpa only [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left hh (norm_nonneg (c i))
        _ ≤ ‖c i‖ * B i := mul_le_mul_of_nonneg_left hd (norm_nonneg (c i))

/-- Exact rescaling of the literal negative logarithmic denominator phase. -/
theorem d02_balanced_time_sum_rescaling {ι : Type*} (s : Finset ι)
    {T : ℝ} (hT : 0 < T) (H K m n : ι → ℕ) (c : ι → ℂ) (f : ι → ℝ → ℂ) :
    (∑ i ∈ s, c i * a03ProfileTimeFourier (f i) T
      (-Real.log (((H i * m i : ℕ) : ℝ) / ((K i * n i : ℕ) : ℝ)))) =
      (T : ℂ) * ∑ i ∈ s, c i * profileLaplaceTransform (f i)
        (((-T * Real.log (((H i * m i : ℕ) : ℝ) /
          ((K i * n i : ℕ) : ℝ)) : ℝ) : ℂ) * I) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [a03_profile_time_fourier_rescaling (f i) hT,
    show T * -Real.log (((H i * m i : ℕ) : ℝ) / ((K i * n i : ℕ) : ℝ)) =
      -T * Real.log (((H i * m i : ℕ) : ℝ) / ((K i * n i : ℕ) : ℝ)) by ring]
  ring

/-- After restoring t = T y, an arbitrary finite truncation of the literal
balanced off-diagonal has the expected power saving per integration by parts. -/
theorem d02_balanced_offDiagonal_integral_bound {ι : Type*} (s : Finset ι)
    {T S δ P C : ℝ} (hT : 0 < T) (hC : 0 ≤ C)
    (H K m n : ι → ℕ) (c : ι → ℂ) (f : ι → ℝ → ℂ) (B : ι → ℝ) (N : ℕ)
    (hH : ∀ i ∈ s, 0 < H i) (hK : ∀ i ∈ s, 0 < K i)
    (hm : ∀ i ∈ s, 0 < m i) (hn : ∀ i ∈ s, 0 < n i)
    (hne : ∀ i ∈ s, H i * m i ≠ K i * n i)
    (hHK : ∀ i ∈ s, (H i : ℝ) * (K i : ℝ) ≤ T ^ S)
    (hmn : ∀ i ∈ s, (m i : ℝ) * (n i : ℝ) ≤ T ^ (1 + δ))
    (hS : ∀ i ∈ s, ContDiff ℝ ∞ (f i))
    (hsupp : ∀ i ∈ s, tsupport (f i) ⊆ Icc (1 : ℝ) 2)
    (hB : ∀ i ∈ s, ∀ x, ‖iteratedDeriv N (f i) x‖ ≤ B i)
    (hmass : (∑ i ∈ s, ‖c i‖ * B i) ≤ C * T ^ P) :
    ‖∑ i ∈ s, c i * a03ProfileTimeFourier (f i) T
      (-Real.log (((H i * m i : ℕ) : ℝ) / ((K i * n i : ℕ) : ℝ)))‖ ≤
      2 ^ N * C * T ^ (1 + P - ((1 - S - δ) / 2) * (N : ℝ)) := by
  let κ : ℝ := (1 - S - δ) / 2
  let ξ : ι → ℝ := fun i => -T * Real.log (((H i * m i : ℕ) : ℝ) / ((K i * n i : ℕ) : ℝ))
  have hCT : 0 ≤ C * T ^ P := mul_nonneg hC (Real.rpow_nonneg hT.le _)
  have hFrequency : 0 < (1 / 2 : ℝ) * T ^ κ := by positivity
  have hf : ∀ i ∈ s, (1 / 2 : ℝ) * T ^ κ ≤ |ξ i| := by
    intro i hi
    simpa only [ξ, neg_mul, abs_neg] using
      d02_balanced_offDiagonal_frequency hT (hH i hi) (hK i hi) (hm i hi) (hn i hi)
        (hne i hi) (hHK i hi) (hmn i hi)
  have hbound := d02_finite_offDiagonal_fourier_bound s c f ξ B N hS hsupp hB hFrequency hf
  rw [d02_balanced_time_sum_rescaling s hT H K m n c f,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg hT.le]
  calc
    _ ≤ T * ((∑ i ∈ s, ‖c i‖ * B i) / ((1 / 2 : ℝ) * T ^ κ) ^ N) :=
      mul_le_mul_of_nonneg_left hbound hT.le
    _ ≤ T * ((C * T ^ P) / ((1 / 2 : ℝ) * T ^ κ) ^ N) := by
      gcongr
    _ = 2 ^ N * C * T ^ (1 + P - κ * (N : ℝ)) := by
      have hpow : ((1 / 2 : ℝ) * T ^ κ) ^ N = T ^ (κ * (N : ℝ)) / (2 : ℝ) ^ N := by
        rw [mul_pow, one_div_pow, div_mul_eq_mul_div, one_mul,
          ← Real.rpow_natCast, ← Real.rpow_mul hT.le]
      rw [hpow, div_div_eq_mul_div]
      have hr : T ^ (1 + P - κ * (N : ℝ)) = T * T ^ P / T ^ (κ * (N : ℝ)) := by
        rw [Real.rpow_sub hT, Real.rpow_add hT, Real.rpow_one]
      rw [hr]
      ring
    _ = _ := rfl

/-- Once the integration-by-parts order exceeds the polynomial budget,
the bound is any prescribed negative power of T. -/
theorem d02_balanced_offDiagonal_power_bound {T S δ P C A : ℝ}
    (hT : 1 ≤ T) (hC : 0 ≤ C) (N : ℕ)
    (horder : 1 + P - ((1 - S - δ) / 2) * (N : ℝ) ≤ -A)
    {z : ℂ}
    (hz : ‖z‖ ≤ 2 ^ N * C * T ^ (1 + P - ((1 - S - δ) / 2) * (N : ℝ))) :
    ‖z‖ ≤ 2 ^ N * C * T ^ (-A) := by
  exact hz.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hT horder) (mul_nonneg (by positivity) hC))

/-- A positive frequency exponent always permits enough integrations by parts. -/
theorem d02_balanced_offDiagonal_exists_order {S δ : ℝ} (hδ : δ < 1 - S)
    (P A : ℝ) :
    ∃ N : ℕ, 1 + P - ((1 - S - δ) / 2) * (N : ℝ) ≤ -A := by
  have hκ := d02_balanced_frequency_exponent_pos hδ
  obtain ⟨N, hN⟩ := exists_nat_gt ((1 + P + A) / ((1 - S - δ) / 2))
  refine ⟨N, ?_⟩
  have hh := (div_lt_iff₀ hκ).1 hN
  linarith

/-- Polynomial coefficient mass and polynomial derivative envelopes, together
with the literal arithmetic cutoffs, imply every negative-power time-sum bound.
The finite set and every amplitude may vary with the height. -/
theorem d02_balanced_offDiagonal_arbitrary_power_decay {ι : Type*}
    (s : ℝ → Finset ι) (H K m n : ℝ → ι → ℕ)
    (c : ℝ → ι → ℂ) (f : ℝ → ι → ℝ → ℂ)
    {S δ P Q C : ℝ} (hδ : δ < 1 - S) (hC : 0 ≤ C)
    (B : ℕ → ℝ) (hB : ∀ N, 0 ≤ B N)
    (hgeom : ∀ᶠ T : ℝ in atTop, ∀ i ∈ s T,
      0 < H T i ∧ 0 < K T i ∧ 0 < m T i ∧ 0 < n T i ∧
      H T i * m T i ≠ K T i * n T i ∧
      (H T i : ℝ) * (K T i : ℝ) ≤ T ^ S ∧
      (m T i : ℝ) * (n T i : ℝ) ≤ T ^ (1 + δ))
    (hreg : ∀ᶠ T : ℝ in atTop, ∀ i ∈ s T,
      ContDiff ℝ ∞ (f T i) ∧ tsupport (f T i) ⊆ Icc (1 : ℝ) 2)
    (hder : ∀ N : ℕ, ∀ᶠ T : ℝ in atTop, ∀ i ∈ s T, ∀ x : ℝ,
      ‖iteratedDeriv N (f T i) x‖ ≤ B N * T ^ Q)
    (hmass : ∀ᶠ T : ℝ in atTop, (∑ i ∈ s T, ‖c T i‖) ≤ C * T ^ P)
    (A : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ T : ℝ in atTop,
      ‖∑ i ∈ s T, c T i * a03ProfileTimeFourier (f T i) T
        (-Real.log (((H T i * m T i : ℕ) : ℝ) /
          ((K T i * n T i : ℕ) : ℝ)))‖ ≤ D * T ^ (-A) := by
  obtain ⟨N, hN⟩ := d02_balanced_offDiagonal_exists_order hδ (P + Q) A
  refine ⟨2 ^ N * (C * B N),
    mul_nonneg (by positivity) (mul_nonneg hC (hB N)), ?_⟩
  filter_upwards [hgeom, hreg, hder N, hmass, eventually_ge_atTop (1 : ℝ)] with T hg hr hd hc hT
  have ht : 0 < T := zero_lt_one.trans_le hT
  have hCB : 0 ≤ C * B N := mul_nonneg hC (hB N)
  have hbudget : (∑ i ∈ s T, ‖c T i‖ * (B N * T ^ Q)) ≤
      (C * B N) * T ^ (P + Q) := by
    rw [← Finset.sum_mul]
    calc
      _ ≤ (C * T ^ P) * (B N * T ^ Q) :=
        mul_le_mul_of_nonneg_right hc (mul_nonneg (hB N) (Real.rpow_nonneg ht.le _))
      _ = _ := by rw [Real.rpow_add ht]; ring
  have hz := d02_balanced_offDiagonal_integral_bound (s T) ht hCB
    (H T) (K T) (m T) (n T) (c T) (f T) (fun _ => B N * T ^ Q) N
    (fun i hi => (hg i hi).1) (fun i hi => (hg i hi).2.1)
    (fun i hi => (hg i hi).2.2.1) (fun i hi => (hg i hi).2.2.2.1)
    (fun i hi => (hg i hi).2.2.2.2.1) (fun i hi => (hg i hi).2.2.2.2.2.1)
    (fun i hi => (hg i hi).2.2.2.2.2.2)
    (fun i hi => (hr i hi).1) (fun i hi => (hr i hi).2)
    (fun i hi x => hd i hi x) hbudget
  exact d02_balanced_offDiagonal_power_bound hT hCB N hN hz

end
end Sechstmoment
