import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace SixthMoment
open Real MeasureTheory Set
noncomputable section
set_option maxHeartbeats 1000000

variable {V : Type*} [NormedAddCommGroup V]

def a03RapidEnvelope (C : ℕ → ℝ) (y : V) : ℝ :=
  ⨅ n : ℕ, max (C n) 1 * (1 + ‖y‖) ^ (-(n : ℝ))

def a03PositiveRapidEnvelope (C : ℕ → ℝ) (y : V) : ℝ :=
  a03RapidEnvelope C y + exp (-‖y‖)

def a03TensorNormalizer (C : ℕ → ℝ) (y : V) : ℝ :=
  a03PositiveRapidEnvelope C y ^ ((1 : ℝ) / 10)

def a03EnvelopeConstant (C : ℕ → ℝ) (n : ℕ) : ℝ :=
  max (C n) 1 + (n.factorial : ℝ) * exp 1

private theorem a03_envelope_bddBelow (C : ℕ → ℝ) (y : V) :
    BddBelow (range (fun n : ℕ => max (C n) 1 * (1 + ‖y‖) ^ (-(n : ℝ)))) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  positivity

theorem a03RapidEnvelope_nonneg (C : ℕ → ℝ) (y : V) :
    0 ≤ a03RapidEnvelope C y := by
  apply le_ciInf
  intro n
  positivity

theorem a03RapidEnvelope_le (C : ℕ → ℝ) (n : ℕ) (y : V) :
    a03RapidEnvelope C y ≤ max (C n) 1 * (1 + ‖y‖) ^ (-(n : ℝ)) :=
  ciInf_le (a03_envelope_bddBelow C y) n

theorem a03RapidEnvelope_majorizes {I : Type*} (c : I → V → ℂ)
    (C : ℕ → ℝ)
    (hc : ∀ n i y, ‖c i y‖ ≤ C n * (1 + ‖y‖) ^ (-(n : ℝ)))
    (i : I) (y : V) : ‖c i y‖ ≤ a03RapidEnvelope C y := by
  apply le_ciInf
  intro n
  exact (hc n i y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

theorem a03PositiveRapidEnvelope_pos (C : ℕ → ℝ) (y : V) :
    0 < a03PositiveRapidEnvelope C y := by
  exact add_pos_of_nonneg_of_pos (a03RapidEnvelope_nonneg C y) (exp_pos _)

theorem a03_exp_neg_norm_decay (n : ℕ) (y : V) :
    exp (-‖y‖) ≤ (n.factorial : ℝ) * exp 1 * (1 + ‖y‖) ^ (-(n : ℝ)) := by
  have hp : 0 < (1 + ‖y‖) ^ n := by positivity
  have hf : 0 < (n.factorial : ℝ) := by positivity
  have h := pow_div_factorial_le_exp (1 + ‖y‖) (show 0 ≤ 1 + ‖y‖ by positivity) n
  have hex : exp (1 + ‖y‖) * exp (-‖y‖) = exp 1 := by
    rw [← exp_add]
    congr 1
    ring
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv]
  apply (le_div_iff₀ hp).mpr
  have hm := mul_le_mul_of_nonneg_right ((div_le_iff₀ hf).mp h) (exp_nonneg (-‖y‖))
  calc
    exp (-‖y‖) * (1 + ‖y‖) ^ n = (1 + ‖y‖) ^ n * exp (-‖y‖) := by ring
    _ ≤ exp (1 + ‖y‖) * (n.factorial : ℝ) * exp (-‖y‖) := hm
    _ = (n.factorial : ℝ) * exp 1 := by rw [mul_right_comm, hex]; ring

theorem a03PositiveRapidEnvelope_decay (C : ℕ → ℝ) (n : ℕ) (y : V) :
    a03PositiveRapidEnvelope C y ≤
      a03EnvelopeConstant C n * (1 + ‖y‖) ^ (-(n : ℝ)) := by
  calc
    _ ≤ max (C n) 1 * (1 + ‖y‖) ^ (-(n : ℝ)) +
      (n.factorial : ℝ) * exp 1 * (1 + ‖y‖) ^ (-(n : ℝ)) :=
        add_le_add (a03RapidEnvelope_le C n y) (a03_exp_neg_norm_decay n y)
    _ = _ := by simp only [a03EnvelopeConstant]; ring

theorem a03TensorNormalizer_pos (C : ℕ → ℝ) (y : V) :
    0 < a03TensorNormalizer C y :=
  rpow_pos_of_pos (a03PositiveRapidEnvelope_pos C y) _

theorem a03EnvelopeConstant_pos (C : ℕ → ℝ) (n : ℕ) :
    0 < a03EnvelopeConstant C n := by
  have hm : 0 < max (C n) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  exact add_pos hm (by positivity)

theorem a03TensorNormalizer_decay (C : ℕ → ℝ) (n : ℕ) (y : V) :
    a03TensorNormalizer C y ≤
      a03EnvelopeConstant C n ^ ((1 : ℝ) / 10) *
        (1 + ‖y‖) ^ (-(n : ℝ) / 10) := by
  have h := Real.rpow_le_rpow (a03PositiveRapidEnvelope_pos C y).le
    (a03PositiveRapidEnvelope_decay C n y) (show 0 ≤ (1 : ℝ) / 10 by norm_num)
  dsimp only [a03TensorNormalizer]
  apply h.trans_eq
  rw [Real.mul_rpow (a03EnvelopeConstant_pos C n).le (by positivity),
    ← Real.rpow_mul (show 0 ≤ 1 + ‖y‖ by positivity)]
  congr 2
  ring

theorem a03TensorNormalizer_weighted_bound (C : ℕ → ℝ) (n : ℕ) (y : V) :
    a03TensorNormalizer C y * (1 + ‖y‖) ^ n ≤
      a03EnvelopeConstant C (10*n) ^ ((1 : ℝ) / 10) := by
  have h := mul_le_mul_of_nonneg_right (a03TensorNormalizer_decay C (10*n) y)
    (show 0 ≤ (1 + ‖y‖) ^ n by positivity)
  have he : -((10*n : ℕ) : ℝ)/10 = -(n : ℝ) := by push_cast; ring
  rw [he, mul_assoc, ← Real.rpow_natCast (1 + ‖y‖) n,
    ← Real.rpow_add (show 0 < 1 + ‖y‖ by positivity)] at h
  simpa only [neg_add_cancel, Real.rpow_zero, mul_one, Real.rpow_natCast] using h

theorem a03TensorNormalizer_fifth_power (C : ℕ → ℝ) (y : V) :
    a03TensorNormalizer C y ^ 5 =
      a03PositiveRapidEnvelope C y ^ ((1 : ℝ) / 2) := by
  dsimp only [a03TensorNormalizer]
  rw [← Real.rpow_mul_natCast (a03PositiveRapidEnvelope_pos C y).le]
  norm_num

theorem a03_normalized_coefficient_bound {I : Type*} (c : I → V → ℂ)
    (C : ℕ → ℝ)
    (hc : ∀ n i y, ‖c i y‖ ≤ C n * (1 + ‖y‖) ^ (-(n : ℝ)))
    (i : I) (y : V) :
    ‖c i y / ((a03TensorNormalizer C y ^ 5 : ℝ) : ℂ)‖ ≤
      a03PositiveRapidEnvelope C y ^ ((1 : ℝ) / 2) := by
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg
    (pow_nonneg (a03TensorNormalizer_pos C y).le 5),
    a03TensorNormalizer_fifth_power]
  have hp := a03PositiveRapidEnvelope_pos C y
  have hmajor : ‖c i y‖ ≤ a03PositiveRapidEnvelope C y :=
    (a03RapidEnvelope_majorizes c C hc i y).trans (le_add_of_nonneg_right (exp_nonneg _))
  calc
    _ ≤ a03PositiveRapidEnvelope C y /
      a03PositiveRapidEnvelope C y ^ ((1 : ℝ) / 2) :=
        div_le_div_of_nonneg_right hmajor (by positivity)
    _ = _ := by
      have he := (Real.rpow_sub hp 1 ((1 : ℝ)/2)).symm
      simpa only [Real.rpow_one, show (1 : ℝ)-1/2=1/2 by norm_num] using he

theorem a03_normalized_coefficient_decay {I : Type*} (c : I → V → ℂ)
    (C : ℕ → ℝ)
    (hc : ∀ n i y, ‖c i y‖ ≤ C n * (1 + ‖y‖) ^ (-(n : ℝ)))
    (n : ℕ) (i : I) (y : V) :
    ‖c i y / ((a03TensorNormalizer C y ^ 5 : ℝ) : ℂ)‖ ≤
      a03EnvelopeConstant C (2*n) ^ ((1 : ℝ) / 2) *
        (1 + ‖y‖) ^ (-(n : ℝ)) := by
  apply (a03_normalized_coefficient_bound c C hc i y).trans
  have h := Real.rpow_le_rpow (a03PositiveRapidEnvelope_pos C y).le
    (a03PositiveRapidEnvelope_decay C (2*n) y) (show 0 ≤ (1 : ℝ) / 2 by norm_num)
  apply h.trans_eq
  rw [Real.mul_rpow (a03EnvelopeConstant_pos C (2*n)).le (by positivity),
    ← Real.rpow_mul (show 0 ≤ 1 + ‖y‖ by positivity)]
  congr 2
  push_cast
  ring

variable [MeasurableSpace V] [BorelSpace V]

theorem a03RapidEnvelope_measurable (C : ℕ → ℝ) :
    Measurable (a03RapidEnvelope (V := V) C) := by
  apply Measurable.iInf
  intro n
  fun_prop

theorem a03PositiveRapidEnvelope_measurable (C : ℕ → ℝ) :
    Measurable (a03PositiveRapidEnvelope (V := V) C) :=
  (a03RapidEnvelope_measurable C).add (by fun_prop)

theorem a03TensorNormalizer_measurable (C : ℕ → ℝ) :
    Measurable (a03TensorNormalizer (V := V) C) := by
  exact (a03PositiveRapidEnvelope_measurable C).pow_const _

variable [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {μ : Measure V} [μ.IsAddHaarMeasure]

theorem a03_normalized_coefficient_integrable {I : Type*} (c : I → V → ℂ)
    (C : ℕ → ℝ)
    (hc : ∀ n i y, ‖c i y‖ ≤ C n * (1 + ‖y‖) ^ (-(n : ℝ)))
    (hm : ∀ i, Measurable (c i)) (i : I) :
    Integrable (fun y => c i y / ((a03TensorNormalizer C y ^ 5 : ℝ) : ℂ)) μ := by
  let n := Module.finrank ℝ V + 1
  have hn : (Module.finrank ℝ V : ℝ) < (n : ℝ) := by dsimp [n]; norm_cast; omega
  have hi := (integrable_one_add_norm (μ := μ) hn).const_mul
    (a03EnvelopeConstant C (2*n) ^ ((1 : ℝ) / 2))
  have hmeas : Measurable
      (fun y => c i y / ((a03TensorNormalizer C y ^ 5 : ℝ) : ℂ)) := by
    exact (hm i).div (Complex.measurable_ofReal.comp
      ((a03TensorNormalizer_measurable C).pow_const 5))
  exact hi.mono' hmeas.aestronglyMeasurable
    (ae_of_all μ (a03_normalized_coefficient_decay c C hc n i))

theorem a03_normalized_coefficient_uniform_l1 {I : Type*} (c : I → V → ℂ)
    (C : ℕ → ℝ)
    (hc : ∀ n i y, ‖c i y‖ ≤ C n * (1 + ‖y‖) ^ (-(n : ℝ)))
    (hm : ∀ i, Measurable (c i)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i,
      Integrable (fun y => c i y / ((a03TensorNormalizer C y ^ 5 : ℝ) : ℂ)) μ ∧
      (∫ y, ‖c i y / ((a03TensorNormalizer C y ^ 5 : ℝ) : ℂ)‖ ∂μ) ≤ K := by
  let n := Module.finrank ℝ V + 1
  let D := a03EnvelopeConstant C (2*n) ^ ((1 : ℝ) / 2)
  let P : V → ℝ := fun y => D * (1 + ‖y‖) ^ (-(n : ℝ))
  have hn : (Module.finrank ℝ V : ℝ) < (n : ℝ) := by dsimp [n]; norm_cast; omega
  have hi : Integrable P μ := (integrable_one_add_norm (μ := μ) hn).const_mul D
  have hD : 0 ≤ D := Real.rpow_nonneg (a03EnvelopeConstant_pos C (2*n)).le _
  refine ⟨∫ y, P y ∂μ, integral_nonneg (fun _ => mul_nonneg hD (by positivity)), ?_⟩
  intro i
  have hcint := a03_normalized_coefficient_integrable c C hc hm i (μ := μ)
  refine ⟨hcint, integral_mono hcint.norm hi ?_⟩
  exact a03_normalized_coefficient_decay c C hc n i

theorem a03_uniform_rapid_tensor_normalizer_exists {I : Type*} (c : I → V → ℂ)
    (hm : ∀ i, Measurable (c i))
    (hrapid : ∀ n : ℕ, ∃ C : ℝ, ∀ i y,
      ‖c i y‖ ≤ C * (1 + ‖y‖) ^ (-(n : ℝ))) :
    ∃ a : V → ℝ, Measurable a ∧ (∀ y, 0 < a y) ∧
      (∀ n : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ y, a y * (1 + ‖y‖) ^ n ≤ D) ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ i,
        Integrable (fun y => c i y / ((a y ^ 5 : ℝ) : ℂ)) μ ∧
        (∫ y, ‖c i y / ((a y ^ 5 : ℝ) : ℂ)‖ ∂μ) ≤ K := by
  choose C hC using hrapid
  refine ⟨a03TensorNormalizer C, a03TensorNormalizer_measurable C,
    a03TensorNormalizer_pos C, ?_, ?_⟩
  · intro n
    exact ⟨a03EnvelopeConstant C (10*n) ^ ((1 : ℝ) / 10),
      Real.rpow_nonneg (a03EnvelopeConstant_pos C (10*n)).le _,
      a03TensorNormalizer_weighted_bound C n⟩
  · exact a03_normalized_coefficient_uniform_l1 c C hC hm

end
end SixthMoment
