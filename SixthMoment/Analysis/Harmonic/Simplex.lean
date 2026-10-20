import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import SixthMoment.Analysis.Harmonic.Iteration


namespace SixthMoment.Source.NoDPHarmonic
open Real Complex MeasureTheory Set
open scoped BigOperators Topology
noncomputable section

def rawStep (L : ℝ) (ν : ℂ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*t)⌋₊,
    if Real.log n/L < t then
      (n:ℂ)^(-(1+ν/(L:ℂ)))*f (t-Real.log n/L) else 0

def rawIter (L : ℝ) : List ℂ → (ℝ → ℂ) → ℝ → ℂ
  | [], f => f
  | ν::νs, f => rawStep L ν (rawIter L νs f)

def clippedTime (η L : ℝ) (d : ℕ) : ℝ := max 0 (η-Real.log d/L)

theorem shiftedPower_eq (L : ℝ) (ν : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    (n:ℂ)^(-(1+ν/(L:ℂ))) = (1/(n:ℂ))*expKernel ν (Real.log n/L) := by
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hn
  have hnR : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  rw [neg_add,Complex.cpow_add _ _ hn0,Complex.cpow_neg,Complex.cpow_one,
    Complex.cpow_def_of_ne_zero hn0]
  have hlog : Complex.log (n:ℂ) = (Real.log n:ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log hnR).symm
  rw [hlog]
  simp only [one_div,expKernel,Complex.ofReal_div]
  congr 1
  congr 1
  ring

theorem discreteStep_const_mul (L : ℝ) (ν c : ℂ) (f : ℝ → ℂ) (t : ℝ) :
    discreteStep L ν (fun x => c*f x) t = c*discreteStep L ν f t := by
  unfold discreteStep strictHarmonicQuadrature
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> ring

theorem rawStep_eq {L : ℝ} (hL : L ≠ 0) (ν : ℂ) (f : ℝ → ℂ) (t : ℝ) :
    rawStep L ν f t = (L:ℂ)*discreteStep L ν f t := by
  unfold rawStep discreteStep strictHarmonicQuadrature
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hn1
  have hLc : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  split_ifs
  · rw [shiftedPower_eq L ν hn1]
    push_cast
    field_simp
  · ring

theorem rawIter_eq {L : ℝ} (hL : L ≠ 0) (νs : List ℂ) (f : ℝ → ℂ) (t : ℝ) :
    rawIter L νs f t = (L:ℂ)^νs.length*discreteIter L νs f t := by
  induction νs generalizing t with
  | nil => simp only [rawIter,discreteIter,List.length_nil,pow_zero,one_mul]
  | cons ν νs ih =>
    change rawStep L ν (rawIter L νs f) t = _
    rw [rawStep_eq hL,show rawIter L νs f = fun x => (L:ℂ)^νs.length*discreteIter L νs f x
      from funext ih,discreteStep_const_mul]
    simp only [List.length_cons,discreteIter,pow_succ]
    ring

theorem clippedTime_bounds {η L : ℝ} (hη : 0 ≤ η) (hL : 0 < L)
    {d : ℕ} (hd : 1 ≤ d) :
    clippedTime η L d ∈ Icc 0 η ∧ |clippedTime η L d-η| ≤ Real.log d/L := by
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hlog : 0 ≤ Real.log d/L := div_nonneg (Real.log_nonneg hdR) hL.le
  have ht : clippedTime η L d ∈ Icc 0 η :=
    ⟨le_max_left _ _,max_le hη (by linarith)⟩
  refine ⟨ht,?_⟩
  rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]
  have hlo : η-Real.log d/L ≤ clippedTime η L d := le_max_right _ _
  linarith

theorem shifted_discreteIter_error {η R B D L : ℝ} {f : ℝ → ℂ}
    (hf : RegularProfile η f B D) (hη : 0 ≤ η) (hR : 0 ≤ R) (hL : 1 ≤ L)
    (νs : List ℂ) (hν : ∀ ν ∈ νs, ‖ν‖ ≤ R) {d : ℕ} (hd : 1 ≤ d) :
    ‖discreteIter L νs f (clippedTime η L d)-continuousIter νs f η‖ ≤
      (iterError η R B D νs.length+
        (iterBounds η R B D νs.length).2*Real.log d)/L := by
  have hL0 : 0 < L := by linarith
  have ht := clippedTime_bounds hη hL0 hd
  have hr := continuousIter_regular hf hη hR νs hν
  have he := discreteIter_error hf hη hR hL νs hν ht.1
  have hs := hr.norm_sub_le _ ht.1 η ⟨hη,le_rfl⟩
  have hs' := hs.trans (mul_le_mul_of_nonneg_left ht.2 hr.lip_nonneg)
  have htri := norm_add_le
    (discreteIter L νs f (clippedTime η L d)-continuousIter νs f (clippedTime η L d))
    (continuousIter νs f (clippedTime η L d)-continuousIter νs f η)
  rw [sub_add_sub_cancel] at htri
  exact htri.trans ((add_le_add he hs').trans_eq (by ring))

theorem triple_simplex_error {η R B D L : ℝ} {f : ℝ → ℂ}
    (hf : RegularProfile η f B D) (hη : 0 ≤ η) (hR : 0 ≤ R) (hL : 1 ≤ L)
    (ν₁ ν₂ ν₃ : ℂ) (hν₁ : ‖ν₁‖ ≤ R) (hν₂ : ‖ν₂‖ ≤ R) (hν₃ : ‖ν₃‖ ≤ R)
    {d : ℕ} (hd : 1 ≤ d) :
    ‖rawIter L [ν₁,ν₂,ν₃] f (clippedTime η L d) -
        (L:ℂ)^3*continuousIter [ν₁,ν₂,ν₃] f η‖ ≤
      (iterError η R B D 3+(iterBounds η R B D 3).2)*(1+Real.log d)*L^2 := by
  have hL0 : 0 < L := by linarith
  have hν : ∀ ν ∈ [ν₁,ν₂,ν₃], ‖ν‖ ≤ R := by
    intro ν hν
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hν
    rcases hν with rfl | rfl | rfl <;> assumption
  have he := shifted_discreteIter_error hf hη hR hL [ν₁,ν₂,ν₃] hν hd
  simp only [List.length_cons,List.length_nil] at he
  rw [rawIter_eq hL0.ne',show [ν₁,ν₂,ν₃].length = 3 from rfl,← mul_sub,norm_mul,
    norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL0]
  have hC := iterError_nonneg hη hR hf.bound_nonneg hf.lip_nonneg 3
  have hD := (iterBounds_nonneg (R := R) hη hf.bound_nonneg hf.lip_nonneg 3).2
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hlog := Real.log_nonneg hdR
  calc
    _ ≤ L^3*((iterError η R B D 3+(iterBounds η R B D 3).2*Real.log d)/L) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = (iterError η R B D 3+(iterBounds η R B D 3).2*Real.log d)*L^2 := by field_simp
    _ ≤ _ := by gcongr; nlinarith

end
end SixthMoment.Source.NoDPHarmonic
