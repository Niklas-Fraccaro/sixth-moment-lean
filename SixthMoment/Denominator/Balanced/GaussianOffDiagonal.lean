import SixthMoment.Denominator.Balanced.GaussianTimeAmplitude
import SixthMoment.Denominator.Balanced.OffDiagonalIntegration
import SixthMoment.Zeta.AFE.Two.Coefficients

namespace SixthMoment
open Complex Real Set Filter Source
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1500000

def d02SixIndexH (q : Fin 6 → ℕ) : ℕ := (q 0 + 1) * (q 1 + 1)
def d02SixIndexK (q : Fin 6 → ℕ) : ℕ := (q 2 + 1) * (q 3 + 1)
def d02SixIndexM (q : Fin 6 → ℕ) : ℕ := q 4 + 1
def d02SixIndexN (q : Fin 6 → ℕ) : ℕ := q 5 + 1

theorem d02_six_index_amplifier_cutoff {T : ℝ} (hT : 0 < T)
    (a : Fin 6 → ℝ) (q : Fin 6 → ℕ)
    (hq : q ∈ d02PositiveBox (fun j => ⌊T ^ (a j)⌋₊)) :
    (d02SixIndexH q : ℝ) * (d02SixIndexK q : ℝ) ≤
      T ^ (a 0 + a 1 + a 2 + a 3) := by
  have hc (j : Fin 6) : (q j + 1 : ℝ) ≤ T ^ (a j) := by
    have hqj : q j + 1 ≤ ⌊T ^ (a j)⌋₊ :=
      Nat.succ_le_of_lt (Finset.mem_range.1 (Fintype.mem_piFinset.1 hq j))
    have hqjR : (q j + 1 : ℝ) ≤ (⌊T ^ (a j)⌋₊ : ℝ) := by exact_mod_cast hqj
    exact hqjR.trans (Nat.floor_le (Real.rpow_nonneg hT.le _))
  unfold d02SixIndexH d02SixIndexK
  push_cast
  calc
    _ ≤ (T ^ (a 0) * T ^ (a 1)) * (T ^ (a 2) * T ^ (a 3)) := by
      exact mul_le_mul
        (mul_le_mul (hc 0) (hc 1) (by positivity) (Real.rpow_nonneg hT.le _))
        (mul_le_mul (hc 2) (hc 3) (by positivity) (Real.rpow_nonneg hT.le _))
        (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add hT, ← Real.rpow_add hT, ← Real.rpow_add hT]
      congr 1
      ring

theorem d02_gaussian_six_index_offDiagonal_uniform_power_bound {Φ : ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc (1 : ℝ) 2)
    (a : Fin 6 → ℝ) {δ R R' F : ℝ}
    (hδ : δ < 1 - (a 0 + a 1 + a 2 + a 3))
    (hR : 0 ≤ R) (hR' : 0 ≤ R') (hF : 0 ≤ F) (A : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ T : ℝ, 1 ≤ T → 1 ≤ Real.log T →
      ∀ (s : Finset (Fin 6 → ℕ)) (σ : Fin 6 → ℂ)
        (w : (Fin 6 → ℕ) → ℂ) (τ : (Fin 6 → ℕ) → ℂ),
      s ⊆ d02PositiveBox (fun j => ⌊T ^ (a j)⌋₊) →
      (∀ j, ‖σ j‖ ≤ R) → (∀ q ∈ s, ‖w q‖ ≤ F) → (∀ q ∈ s, ‖τ q‖ ≤ R') →
      (∀ q ∈ s, d02SixIndexH q * d02SixIndexM q ≠ d02SixIndexK q * d02SixIndexN q ∧
        (d02SixIndexM q : ℝ) * (d02SixIndexN q : ℝ) ≤ T ^ (1 + δ)) →
      ‖∑ q ∈ s, (w q * d02ShiftedSqrtCoefficient T σ q) *
        a03ProfileTimeFourier
          (a03ProfileProduct
            (a03ProfileProduct Φ (d02GaussianTimeAmplitude
              (2 * Real.pi * (d02SixIndexM q : ℝ) * (d02SixIndexN q : ℝ) / T)))
            (fun y : ℝ => (y : ℂ) ^ (τ q))) T
          (-Real.log (((d02SixIndexH q * d02SixIndexM q : ℕ) : ℝ) /
            ((d02SixIndexK q * d02SixIndexN q : ℕ) : ℝ)))‖ ≤ D * T ^ (-A) := by
  obtain ⟨B, hB, hb⟩ := d02GaussianShiftedProfile_uniform_derivative_bounds hΦ hΦs hR'
  obtain ⟨N, hN⟩ := d02_balanced_offDiagonal_exists_order hδ ((∑ j, a j) / 2) A
  let C : ℝ := (F * Real.exp (R * ∑ j, a j)) * 2 ^ (6 : ℕ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCB : 0 ≤ C * B N := mul_nonneg hC (hB N)
  refine ⟨2 ^ N * (C * B N), mul_nonneg (by positivity) hCB, ?_⟩
  intro T hT hL s σ w τ hs hσ hw hτ hcut
  have hTp : 0 < T := zero_lt_one.trans_le hT
  let f : (Fin 6 → ℕ) → ℝ → ℂ := fun q =>
    a03ProfileProduct
      (a03ProfileProduct Φ (d02GaussianTimeAmplitude
        (2 * Real.pi * (d02SixIndexM q : ℝ) * (d02SixIndexN q : ℝ) / T)))
      (fun y : ℝ => (y : ℂ) ^ (τ q))
  have hreg (q : Fin 6 → ℕ) (hq : q ∈ s) :=
    hb (2 * Real.pi * (d02SixIndexM q : ℝ) * (d02SixIndexN q : ℝ) / T) (τ q) (hτ q hq)
  have hm := d02_shifted_height_coefficient_mass_le hTp hL hR hF a σ hσ s w hs hw
  have hmass : (∑ q ∈ s, ‖w q * d02ShiftedSqrtCoefficient T σ q‖ * B N) ≤
      (C * B N) * T ^ ((∑ j, a j) / 2) := by
    rw [← Finset.sum_mul]
    calc
      _ ≤ ((F * Real.exp (R * ∑ j, a j)) * 2 ^ (6 : ℕ) *
          T ^ ((∑ j, a j) / 2)) * B N := mul_le_mul_of_nonneg_right hm (hB N)
      _ = _ := by dsimp [C]; ring
  have hz := d02_balanced_offDiagonal_integral_bound s hTp hCB
    d02SixIndexH d02SixIndexK d02SixIndexM d02SixIndexN
    (fun q => w q * d02ShiftedSqrtCoefficient T σ q) f (fun _ => B N) N
    (fun q _ => by unfold d02SixIndexH; positivity)
    (fun q _ => by unfold d02SixIndexK; positivity)
    (fun q _ => by unfold d02SixIndexM; positivity)
    (fun q _ => by unfold d02SixIndexN; positivity)
    (fun q hq => (hcut q hq).1)
    (fun q hq => d02_six_index_amplifier_cutoff hTp a q (hs hq))
    (fun q hq => (hcut q hq).2)
    (fun q hq => (hreg q hq).1) (fun q hq => (hreg q hq).2.1)
    (fun q hq x => (hreg q hq).2.2 N x) hmass
  exact d02_balanced_offDiagonal_power_bound hT hCB N hN hz

theorem d02_gaussian_six_index_offDiagonal_arbitrary_power_decay {Φ : ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc (1 : ℝ) 2)
    (a : Fin 6 → ℝ) {δ R R' F : ℝ}
    (hδ : δ < 1 - (a 0 + a 1 + a 2 + a 3))
    (hR : 0 ≤ R) (hR' : 0 ≤ R') (hF : 0 ≤ F)
    (s : ℝ → Finset (Fin 6 → ℕ)) (σ : ℝ → Fin 6 → ℂ)
    (w : ℝ → (Fin 6 → ℕ) → ℂ) (ρ : ℝ → (Fin 6 → ℕ) → ℂ)
    (hs : ∀ᶠ T : ℝ in atTop, s T ⊆ d02PositiveBox (fun j => ⌊T ^ (a j)⌋₊))
    (hσ : ∀ᶠ T : ℝ in atTop, ∀ j, ‖σ T j‖ ≤ R)
    (hw : ∀ᶠ T : ℝ in atTop, ∀ q ∈ s T, ‖w T q‖ ≤ F)
    (hρ : ∀ᶠ T : ℝ in atTop, ∀ q ∈ s T, ‖ρ T q‖ ≤ R')
    (hcut : ∀ᶠ T : ℝ in atTop, ∀ q ∈ s T,
      d02SixIndexH q * d02SixIndexM q ≠ d02SixIndexK q * d02SixIndexN q ∧
      (d02SixIndexM q : ℝ) * (d02SixIndexN q : ℝ) ≤ T ^ (1 + δ))
    (A : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ T : ℝ in atTop,
      ‖∑ q ∈ s T, (w T q * d02ShiftedSqrtCoefficient T (σ T) q) *
        a03ProfileTimeFourier
          (a03ProfileProduct
            (a03ProfileProduct Φ (d02GaussianTimeAmplitude
              (2 * Real.pi * (d02SixIndexM q : ℝ) * (d02SixIndexN q : ℝ) / T)))
            (fun y : ℝ => (y : ℂ) ^ (ρ T q))) T
          (-Real.log (((d02SixIndexH q * d02SixIndexM q : ℕ) : ℝ) /
            ((d02SixIndexK q * d02SixIndexN q : ℕ) : ℝ)))‖ ≤ D * T ^ (-A) := by
  let C : ℝ := (F * Real.exp (R * ∑ j, a j)) * 2 ^ (6 : ℕ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let c : ℝ → (Fin 6 → ℕ) → ℂ := fun T q => w T q * d02ShiftedSqrtCoefficient T (σ T) q
  let f : ℝ → (Fin 6 → ℕ) → ℝ → ℂ := fun T q =>
    a03ProfileProduct
      (a03ProfileProduct Φ (d02GaussianTimeAmplitude
        (2 * Real.pi * (d02SixIndexM q : ℝ) * (d02SixIndexN q : ℝ) / T)))
      (fun y : ℝ => (y : ℂ) ^ (ρ T q))
  obtain ⟨B, hB, hb⟩ := d02GaussianShiftedProfile_uniform_derivative_bounds hΦ hΦs hR'
  refine d02_balanced_offDiagonal_arbitrary_power_decay s
    (fun _ => d02SixIndexH) (fun _ => d02SixIndexK)
    (fun _ => d02SixIndexM) (fun _ => d02SixIndexN) c f
    (P := (∑ j, a j) / 2) (Q := 0) hδ hC B hB ?_ ?_ ?_ ?_ A
  · filter_upwards [hs, hcut, eventually_gt_atTop (0 : ℝ)] with T hsT hc hT
    intro q hq
    refine ⟨by unfold d02SixIndexH; positivity, by unfold d02SixIndexK; positivity,
      by unfold d02SixIndexM; positivity, by unfold d02SixIndexN; positivity,
      (hc q hq).1, d02_six_index_amplifier_cutoff hT a q (hsT hq), (hc q hq).2⟩
  · filter_upwards [hρ] with T hρT
    intro q hq
    exact (hb _ _ (hρT q hq)).imp_right And.left
  · intro N
    filter_upwards [hρ] with T hρT
    intro q hq x
    simpa only [Real.rpow_zero, mul_one] using (hb _ _ (hρT q hq)).2.2 N x
  · filter_upwards [hs, hσ, hw, eventually_gt_atTop (0 : ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with T hsT hσT hwT hT hL
    exact d02_shifted_height_coefficient_mass_le hT hL hR hF a (σ T) hσT (s T) (w T) hsT hwT

end
end SixthMoment
