import Sechstmoment.Numerator.V.Arithmetic.Additive.DirichletReduction
import Sechstmoment.Numerator.V.Arithmetic.AmplifierLengthPowers


namespace Sechstmoment.Source
open Complex Real Set MeasureTheory
open scoped BigOperators ContDiff
noncomputable section

theorem amplifier_log_argument_mem {T η : ℝ} (hT : 1 < T) {a : ℕ}
    (ha : a < ⌊T^η⌋₊) : Real.log (a+1:ℝ)/Real.log T ∈ Icc (0:ℝ) η := by
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  have ha1 : (1:ℝ) ≤ a+1 := by linarith [Nat.cast_nonneg (α := ℝ) a]
  have haX : (a+1:ℝ) ≤ T^η :=
    (by exact_mod_cast Nat.succ_le_of_lt ha : (a+1:ℝ) ≤ (⌊T^η⌋₊:ℝ)).trans
      (Nat.floor_le (Real.rpow_nonneg hT0.le η))
  refine ⟨div_nonneg (Real.log_nonneg ha1) hL.le,?_⟩
  apply (div_le_iff₀ hL).mpr
  have H := Real.log_le_log (by positivity : (0:ℝ) < a+1) haX
  rwa [Real.log_rpow hT0] at H

def noDPAmplifierPairWeight (T : ℝ) (f g : ℝ → ℝ) (a b : ℕ) : ℂ :=
  ((f (Real.log (a+1:ℝ)/Real.log T):ℂ)*(g (Real.log (b+1:ℝ)/Real.log T):ℂ))/
    (((a+1:ℝ)*(b+1:ℝ):ℝ):ℂ)

theorem amplified_four_zeta_chi_additive_reduction {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {R : ℝ} (hR : 0 ≤ R) (η : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, max 64 (100*Real.pi) ≤ T →
      4*(2*R+2) ≤ Real.log T → ∀ u : ℂ, ‖u‖ ≤ R/Real.log T →
      ∀ β : Fin 4 → ℂ, (∀ j, ‖β j‖ ≤ R/Real.log T) →
      ∀ B D : ℝ, 0 ≤ B → 0 ≤ D → ∀ f g : ℝ → ℝ,
      (∀ x ∈ Icc (0:ℝ) η, |f x| ≤ B) →
      (∀ x ∈ Icc (0:ℝ) η, |g x| ≤ D) →
      ‖(∑ a ∈ Finset.range ⌊T^η⌋₊, ∑ b ∈ Finset.range ⌊T^η⌋₊,
          noDPAmplifierPairWeight T f g a b*
            noDPFourChiMoment w T (noDPRightLine T R) ((a+1:ℝ)*(b+1:ℝ)) u β)-
        (∑ a ∈ Finset.range ⌊T^η⌋₊, ∑ b ∈ Finset.range ⌊T^η⌋₊,
          noDPAmplifierPairWeight T f g a b*
            ∑' m : ℕ+, noDPAdditiveChiTerm w T ((a+1:ℝ)*(b+1:ℝ)) u β m)‖ ≤
        C*B*D*T^(1/2+2*η:ℝ)*(Real.log T)^4 := by
  obtain ⟨A,hA,H⟩ := four_zeta_chi_additive_reduction hw hws hR
  let E := Real.exp (2*η*(R+2))
  refine ⟨A*E,by dsimp only [E]; positivity,?_⟩
  intro T hT hL u hu β hβ B D hB hD f g hf hg
  have hT64 : 64 ≤ T := (le_max_left _ _).trans hT
  have hT1 : 1 < T := by linarith
  have hT0 : 0 < T := by linarith
  let M := A*B*D*E*T^(1/2:ℝ)*(Real.log T)^4
  have hM : 0 ≤ M := by dsimp only [M,E]; positivity
  have hpoint (a : ℕ) (ha : a ∈ Finset.range ⌊T^η⌋₊)
      (b : ℕ) (hb : b ∈ Finset.range ⌊T^η⌋₊) :
      ‖noDPAmplifierPairWeight T f g a b*
        (noDPFourChiMoment w T (noDPRightLine T R) ((a+1:ℝ)*(b+1:ℝ)) u β-
          ∑' m : ℕ+, noDPAdditiveChiTerm w T ((a+1:ℝ)*(b+1:ℝ)) u β m)‖ ≤ M := by
    let N := (a+1:ℝ)*(b+1:ℝ)
    have hlen := amplifier_pair_indices_length_bound hT0
      (Finset.mem_range.mp ha) (Finset.mem_range.mp hb)
    have hN : 0 < N := hlen.1
    have hweight : ‖noDPAmplifierPairWeight T f g a b‖ ≤ B*D/N := by
      rw [noDPAmplifierPairWeight,norm_div,norm_mul,Complex.norm_real,
        Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
        Real.norm_eq_abs,abs_of_pos hN]
      exact div_le_div_of_nonneg_right
        (mul_le_mul (hf _ (amplifier_log_argument_mem hT1 (Finset.mem_range.mp ha)))
          (hg _ (amplifier_log_argument_mem hT1 (Finset.mem_range.mp hb)))
          (abs_nonneg _) hB) hN.le
    have hcost : N^(noDPRightLine T R-1) ≤ E :=
      amplifier_product_log_power_bound hT1 hR hN hlen.2
    rw [norm_mul]
    calc
      _ ≤ (B*D/N)*(A*N^(noDPRightLine T R)*T^(1/2:ℝ)*(Real.log T)^4) :=
        mul_le_mul hweight (H T hT hL u hu β hβ N hN).2 (norm_nonneg _) (by positivity)
      _ = A*B*D*(N^(noDPRightLine T R-1))*T^(1/2:ℝ)*(Real.log T)^4 := by
        rw [Real.rpow_sub_one hN.ne']
        ring
      _ ≤ M := by dsimp only [M]; gcongr
  have he :
      (∑ a ∈ Finset.range ⌊T^η⌋₊, ∑ b ∈ Finset.range ⌊T^η⌋₊,
        noDPAmplifierPairWeight T f g a b*
          noDPFourChiMoment w T (noDPRightLine T R) ((a+1:ℝ)*(b+1:ℝ)) u β)-
      (∑ a ∈ Finset.range ⌊T^η⌋₊, ∑ b ∈ Finset.range ⌊T^η⌋₊,
        noDPAmplifierPairWeight T f g a b*
          ∑' m : ℕ+, noDPAdditiveChiTerm w T ((a+1:ℝ)*(b+1:ℝ)) u β m) =
      ∑ a ∈ Finset.range ⌊T^η⌋₊, ∑ b ∈ Finset.range ⌊T^η⌋₊,
        noDPAmplifierPairWeight T f g a b*
          (noDPFourChiMoment w T (noDPRightLine T R) ((a+1:ℝ)*(b+1:ℝ)) u β-
            ∑' m : ℕ+, noDPAdditiveChiTerm w T ((a+1:ℝ)*(b+1:ℝ)) u β m) := by
    simp_rw [mul_sub,Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ a ∈ Finset.range ⌊T^η⌋₊, ∑ b ∈ Finset.range ⌊T^η⌋₊, M := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a ha
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (hpoint a ha))
    _ = (⌊T^η⌋₊:ℝ)^2*M := by simp; ring
    _ ≤ (T^η)^2*M := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (Real.rpow_nonneg hT0.le η)) 2) hM
    _ = (A*E)*B*D*T^(1/2+2*η:ℝ)*(Real.log T)^4 := by
      dsimp only [M]
      rw [show (1/2+2*η:ℝ) = (1/2:ℝ)+(η+η) by ring,
        Real.rpow_add hT0,Real.rpow_add hT0]
      ring

end
end Sechstmoment.Source
