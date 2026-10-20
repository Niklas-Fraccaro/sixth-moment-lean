import Sechstmoment.Numerator.V.Arithmetic.UniformCorrectedMellin
import Sechstmoment.Numerator.V.EulerTransfer.PowerSaving


namespace Sechstmoment.Source.NoDPGlobalLFactorization
open Complex Real Set MeasureTheory
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 2000000

theorem timeWeight_displacedRemainder_bound {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {R : ℝ} (hR : 0 ≤ R) (κ ε : ℝ) (hκ : 1/2 < κ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 2*Real.pi ≤ U → 1 ≤ Real.log U →
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ N : ℕ, ∀ hN : N ≠ 0,
      ∀ s : Fin 4 → ℂ, (∀ j, ‖s j‖ ≤ min κ (ε/2)) →
      (∀ j, κ+(s j).re ∈ Icc (1/2:ℝ) (3/4)) → ∀ x : ℝ, 0 < x →
      ‖displacedRemainder N hN (noDPTimeWeight w U (z/(Real.log U:ℂ))) κ s x‖ ≤
        C*x^κ*(N:ℝ)^(-1/2+ε) := by
  obtain ⟨A,hA,H⟩ := timeWeight_correctedMellin_uniform_bound hw hws hR κ ε ε
    (by linarith) hε hε
  let J := ∑' d : ℕ, (d:ℝ)^(-κ-1/2)
  have hJ : 0 ≤ J := tsum_nonneg (fun d => Real.rpow_nonneg (Nat.cast_nonneg d) _)
  refine ⟨A*(J+1),by positivity,?_⟩
  intro U hU hLU z hz N hN s hs hsr x hx
  have hnorm : ‖displacedRemainder N hN (noDPTimeWeight w U (z/(Real.log U:ℂ))) κ s x‖ ≤
      ∑ d : N.divisors, A*x^κ*(N:ℝ)^(-1/2+ε)*(d.val:ℝ)^(-κ-1/2) := by
    rw [displacedRemainder,norm_mul,norm_inv,Complex.norm_natCast]
    apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d _
    let _ : NeZero (N/d.val) := divisorQuotientNeZero N hN d
    have hd : d.val ≠ 0 := NoDPGlobalConvolution.divisor_ne_zero d.property
    have hdp : (0:ℝ) < d.val := by exact_mod_cast Nat.pos_of_ne_zero hd
    have h := (H U hU hLU z hz (N/d.val) inferInstance d.val hd s hs hsr
      (x/d.val) (div_pos hx hdp)).2
    have hh := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (Nat.cast_nonneg N))
    exact hh.trans_eq (divisor_length_identity N d.val hN d.property x κ ε A hx)
  calc
    _ ≤ A*x^κ*(N:ℝ)^(-1/2+ε)*∑ d : N.divisors, (d.val:ℝ)^(-κ-1/2) := by
      simpa only [Finset.mul_sum] using hnorm
    _ ≤ A*x^κ*(N:ℝ)^(-1/2+ε)*J := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (Finset.sum_coe_sort N.divisors (fun d : ℕ => (d:ℝ)^(-κ-1/2))).le.trans
        (divisor_negative_power_sum κ hκ N)
    _ ≤ A*x^κ*(N:ℝ)^(-1/2+ε)*(J+1) := by gcongr; linarith
    _ = _ := by ring

theorem timeWeight_profileRemainderSum_bound_independent_scale {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {R : ℝ} (hR : 0 ≤ R) (κ ε θ : ℝ)
    (hκ : 1/2 < κ) (hε : 0 < ε) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2*Real.pi ≤ T → 1 ≤ Real.log T →
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ L X : ℝ, 0 < X → ∀ f g : ℝ → ℂ, ∀ B : ℝ, 0 ≤ B →
      (∀ x, ‖f x‖ ≤ B) → (∀ x, ‖g x‖ ≤ B) → ∀ Y : ℕ, Y ≠ 0 →
      ∀ s : Fin 4 → ℂ, (∀ j, ‖s j‖ ≤ min κ (ε/2)) →
      (∀ j, κ+(s j).re ∈ Icc (1/2:ℝ) (3/4)) →
      ‖profileRemainderSum f g L Y
        (noDPTimeWeight w T (z/(Real.log T:ℂ))) κ s X‖ ≤
        C*B^2*X^κ*(Y:ℝ)^(κ+1/2+ε+θ) := by
  obtain ⟨A,hA,H⟩ := timeWeight_displacedRemainder_bound hw hws hR κ ε hκ hε
  obtain ⟨D,hD,HD⟩ := divisor_count_subpower θ hθ
  refine ⟨A*D,by positivity,?_⟩
  intro T hT hL z hz L X hX f g B hB hf hg Y hY s hs hsr
  have HA (N : ℕ) (hN : N ≠ 0) :
      ‖displacedRemainder N hN (noDPTimeWeight w T (z/(Real.log T:ℂ))) κ s ((N:ℝ)*X)‖ ≤
        A*X^κ*(N:ℝ)^(κ-1/2+ε) := by
    have hNp : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    apply (H T hT hL z hz N hN s hs hsr _ (mul_pos hNp hX)).trans_eq
    rw [Real.mul_rpow hNp.le hX.le]
    calc
      _ = A*X^κ*((N:ℝ)^κ*(N:ℝ)^(-1/2+ε)) := by ring
      _ = _ := by rw [← Real.rpow_add hNp]; congr 2; ring
  have hpoint (N : Finset.Icc 1 Y) :
      ‖profileCoefficient f g L N.val*
        displacedRemainder N.val (positiveIndexNeZero Y N)
          (noDPTimeWeight w T (z/(Real.log T:ℂ))) κ s ((N.val:ℝ)*X)‖ ≤
        A*D*B^2*X^κ*(N.val:ℝ)^(κ-1/2+ε+θ) := by
    have hN := positiveIndexNeZero Y N
    have hNp : (0:ℝ) < N.val := by exact_mod_cast Nat.pos_of_ne_zero hN
    rw [norm_mul]
    calc
      _ ≤ (B^2*N.val.divisors.card)*(A*X^κ*(N.val:ℝ)^(κ-1/2+ε)) :=
        mul_le_mul (profileCoefficient_bound f g B hB hf hg _ N.val)
          (HA N.val hN) (norm_nonneg _) (by positivity)
      _ ≤ (B^2*(D*(N.val:ℝ)^θ))*(A*X^κ*(N.val:ℝ)^(κ-1/2+ε)) := by
        gcongr
        exact HD N.val hN
      _ = A*D*B^2*X^κ*((N.val:ℝ)^(κ-1/2+ε)*(N.val:ℝ)^θ) := by ring
      _ = _ := by rw [← Real.rpow_add hNp]
  have hsum : ‖profileRemainderSum f g L Y
      (noDPTimeWeight w T (z/(Real.log T:ℂ))) κ s X‖ ≤
      ∑ N : Finset.Icc 1 Y, A*D*B^2*X^κ*(N.val:ℝ)^(κ-1/2+ε+θ) := by
    unfold profileRemainderSum
    exact (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum (fun N _ => hpoint N))
  calc
    _ ≤ A*D*B^2*X^κ*∑ N : Finset.Icc 1 Y, (N.val:ℝ)^(κ-1/2+ε+θ) := by
      simpa only [Finset.mul_sum] using hsum
    _ ≤ A*D*B^2*X^κ*(Y:ℝ)^((κ-1/2+ε+θ)+1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (Finset.sum_coe_sort (Finset.Icc 1 Y) (fun N : ℕ => (N:ℝ)^(κ-1/2+ε+θ))).le.trans
        (positive_power_partial_sum Y hY _ (by linarith))
    _ = _ := by congr 2; ring

theorem timeWeight_profileRemainderSum_bound {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {R : ℝ} (hR : 0 ≤ R) (κ ε θ : ℝ)
    (hκ : 1/2 < κ) (hε : 0 < ε) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2*Real.pi ≤ T → 1 ≤ Real.log T →
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ f g : ℝ → ℂ, ∀ B : ℝ, 0 ≤ B →
      (∀ x, ‖f x‖ ≤ B) → (∀ x, ‖g x‖ ≤ B) → ∀ Y : ℕ, Y ≠ 0 →
      ∀ s : Fin 4 → ℂ, (∀ j, ‖s j‖ ≤ min κ (ε/2)) →
      (∀ j, κ+(s j).re ∈ Icc (1/2:ℝ) (3/4)) →
      ‖profileRemainderSum f g (Real.log T) Y
        (noDPTimeWeight w T (z/(Real.log T:ℂ))) κ s T‖ ≤
        C*B^2*T^κ*(Y:ℝ)^(κ+1/2+ε+θ) := by
  obtain ⟨C,hC,H⟩ := timeWeight_profileRemainderSum_bound_independent_scale
    hw hws hR κ ε θ hκ hε hθ
  refine ⟨C,hC,?_⟩
  intro T hT hL z hz
  exact H T hT hL z hz (Real.log T) T ((by positivity : 0 < 2*Real.pi).trans_le hT)

theorem timeWeight_profile_displaced_power_saving_scaled {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {R : ℝ} (hR : 0 ≤ R) (ε η : ℝ)
    (hε : 0 < ε) (hε' : ε < 1/2) (hη : η ≤ 1/4) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 1 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ X : ℝ, 0 < X → X ≤ T →
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ Y : ℕ, Y ≠ 0 → (Y:ℝ) ≤ T^(2*η) →
      ∀ f g : ℝ → ℂ, ∀ B : ℝ, 0 ≤ B → (∀ x, ‖f x‖ ≤ B) → (∀ x, ‖g x‖ ≤ B) →
      ∀ s : Fin 4 → ℂ, (∀ j, ‖s j‖ ≤ R/Real.log T) →
      ‖profileRemainderSum f g (Real.log T) Y
        (noDPTimeWeight w T (z/(Real.log T:ℂ))) (1/2+ε/16) s X‖ ≤
        C*B^2*T^(1/2+2*η+ε) := by
  obtain ⟨C,hC,H⟩ := timeWeight_profileRemainderSum_bound_independent_scale hw hws hR
    (1/2+ε/16) (ε/16) (ε/16) (by linarith) (by linarith) (by linarith)
  obtain ⟨U,hU,HT⟩ := log_shift_tolerance (ε/32) R (by linarith)
  let T₀ := max U (max (2*Real.pi) (Real.exp 1))
  have hT₀ : 1 < T₀ := hU.trans_le (le_max_left _ _)
  refine ⟨C,hC,T₀,hT₀,?_⟩
  intro T hT X hX hXT z hz Y hY hYlen f g B hB hf hg s hs
  have hTU : U ≤ T := (le_max_left _ _).trans hT
  have hTpi : 2*Real.pi ≤ T :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hL : 1 ≤ Real.log T := by
    have Hlog := Real.log_le_log (Real.exp_pos 1)
      ((le_max_right _ _).trans ((le_max_right _ _).trans hT))
    simpa only [Real.log_exp] using Hlog
  have hsmall (j : Fin 4) : ‖s j‖ ≤ ε/32 := (hs j).trans (HT T hTU)
  have hregion := power_saving_shift_region ε hε hε' s hsmall
  have h := H T hTpi hL z hz (Real.log T) X hX f g B hB hf hg Y hY s hregion.1 hregion.2
  apply h.trans
  calc
    _ = C*B^2*(X^(1/2+ε/16)*(Y:ℝ)^((1/2+ε/16)+1/2+ε/16+ε/16)) := by ring
    _ ≤ C*B^2*(T^(1/2+ε/16)*(Y:ℝ)^((1/2+ε/16)+1/2+ε/16+ε/16)) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (length_power_saving T (by linarith [hT₀]) Y η ε hη hε hYlen) (by positivity)

theorem timeWeight_profile_displaced_power_saving {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {R : ℝ} (hR : 0 ≤ R) (ε η : ℝ)
    (hε : 0 < ε) (hε' : ε < 1/2) (hη : η ≤ 1/4) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 1 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ Y : ℕ, Y ≠ 0 → (Y:ℝ) ≤ T^(2*η) →
      ∀ f g : ℝ → ℂ, ∀ B : ℝ, 0 ≤ B → (∀ x, ‖f x‖ ≤ B) → (∀ x, ‖g x‖ ≤ B) →
      ∀ s : Fin 4 → ℂ, (∀ j, ‖s j‖ ≤ R/Real.log T) →
      ‖profileRemainderSum f g (Real.log T) Y
        (noDPTimeWeight w T (z/(Real.log T:ℂ))) (1/2+ε/16) s T‖ ≤
        C*B^2*T^(1/2+2*η+ε) := by
  obtain ⟨C,hC,T₀,hT₀,H⟩ := timeWeight_profile_displaced_power_saving_scaled hw hws hR ε η hε hε' hη
  refine ⟨C,hC,T₀,hT₀,?_⟩
  intro T hT
  exact H T hT T (by linarith) le_rfl

end
end Sechstmoment.Source.NoDPGlobalLFactorization
