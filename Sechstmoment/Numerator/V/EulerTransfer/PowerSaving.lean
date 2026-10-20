import Sechstmoment.Numerator.V.EulerTransfer.ProfileError

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace Sechstmoment.Source.NoDPGlobalLFactorization
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest NoDPGlobalConvolution
open Complex Real MeasureTheory Filter Set ZMod
open scoped Topology BigOperators Classical ContDiff
noncomputable section

theorem log_shift_tolerance (a R : ℝ) (ha : 0 < a) :
    ∃ T₀ : ℝ, 1 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T → R/Real.log T ≤ a := by
  refine ⟨max (Real.exp (R/a)) 2,lt_of_lt_of_le (by norm_num) (le_max_right _ _),?_⟩
  intro T hT
  have hlog : 0 < Real.log T := Real.log_pos (by have := (le_max_right (Real.exp (R/a)) 2).trans hT; linarith)
  have H : R/a ≤ Real.log T := by
    have h := Real.log_le_log (Real.exp_pos (R/a)) ((le_max_left _ _).trans hT)
    simpa only [Real.log_exp] using h
  apply (div_le_iff₀ hlog).mpr
  have h := (div_le_iff₀ ha).mp H
  nlinarith

theorem power_saving_shift_region (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1/2)
    (s : Fin 4 → ℂ) (hs : ∀ j, ‖s j‖ ≤ ε/32) :
    (∀ j, ‖s j‖ ≤ min (1/2+ε/16) ((ε/16)/2)) ∧
    (∀ j, (1/2+ε/16)+(s j).re ∈ Icc (1/2:ℝ) (3/4)) := by
  constructor
  · intro j
    apply le_min
    · exact (hs j).trans (by linarith)
    · exact (hs j).trans (by linarith)
  · intro j
    have hr := (re_le_norm (s j)).trans (hs j)
    have hl := (re_le_norm (-s j)).trans (by simpa using hs j)
    simp only [neg_re] at hl
    constructor <;> linarith

theorem length_power_saving (T : ℝ) (hT : 1 ≤ T) (Y : ℕ)
    (η ε : ℝ) (hη : η ≤ 1/4) (hε : 0 < ε) (hYlen : (Y:ℝ) ≤ T^(2*η)) :
    T^(1/2+ε/16) * (Y:ℝ)^((1/2+ε/16)+1/2+ε/16+ε/16) ≤ T^(1/2+2*η+ε) := by
  have hTp : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have ha : 0 ≤ (1/2+ε/16)+1/2+ε/16+ε/16 := by linarith
  calc
    _ ≤ T^(1/2+ε/16) * (T^(2*η))^((1/2+ε/16)+1/2+ε/16+ε/16) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg Y) hYlen ha)
        (Real.rpow_nonneg hTp.le _)
    _ = T^((1/2+ε/16)+(2*η)*((1/2+ε/16)+1/2+ε/16+ε/16)) := by
      rw [← Real.rpow_mul hTp.le,← Real.rpow_add hTp]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT (by nlinarith)

theorem profile_displaced_power_saving {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1:ℝ) 2) (ε η R : ℝ)
    (hε : 0 < ε) (hε' : ε < 1/2) (hη : η ≤ 1/4) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 1 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ Y : ℕ, Y ≠ 0 → (Y:ℝ) ≤ T^(2*η) →
      ∀ f g : ℝ → ℂ, ∀ B : ℝ, 0 ≤ B → (∀ x, ‖f x‖ ≤ B) → (∀ x, ‖g x‖ ≤ B) →
      ∀ s : Fin 4 → ℂ, (∀ j, ‖s j‖ ≤ R/Real.log T) →
        ‖profileRemainderSum f g (Real.log T) Y w (1/2+ε/16) s T‖ ≤
          C*B^2*T^(1/2+2*η+ε) := by
  obtain ⟨C,hC,H⟩ := profileRemainderSum_bound hw hws (1/2+ε/16) (ε/16) (ε/16)
    (by linarith) (by linarith) (by linarith)
  obtain ⟨T₀,hT₀,HT⟩ := log_shift_tolerance (ε/32) R (by linarith)
  refine ⟨C,hC,T₀,hT₀,?_⟩
  intro T hT Y hY hYlen f g B hB hf hg s hs
  have hTp : 0 < T := lt_trans zero_lt_one (lt_of_lt_of_le hT₀ hT)
  have hsmall (j : Fin 4) : ‖s j‖ ≤ ε/32 := (hs j).trans (HT T hT)
  have hregion := power_saving_shift_region ε hε hε' s hsmall
  have h := H f g B hB hf hg (Real.log T) Y hY s hregion.1 hregion.2 T hTp
  apply h.trans
  calc
    _ = C*B^2*(T^(1/2+ε/16)*(Y:ℝ)^((1/2+ε/16)+1/2+ε/16+ε/16)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (length_power_saving T (by linarith) Y η ε hη hε hYlen) (by positivity)

end
end Sechstmoment.Source.NoDPGlobalLFactorization
