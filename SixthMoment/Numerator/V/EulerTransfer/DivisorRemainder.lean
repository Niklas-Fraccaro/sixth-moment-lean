import SixthMoment.Numerator.V.EulerTransfer.CorrectedMellin

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace SixthMoment.Source.NoDPGlobalLFactorization
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest NoDPGlobalConvolution
open Complex Real MeasureTheory Filter Set ZMod
open scoped Topology BigOperators Classical ContDiff
noncomputable section

abbrev divisorQuotientNeZero (N : ℕ) (hN : N ≠ 0) (d : N.divisors) : NeZero (N/d.val) :=
  ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (Nat.dvd_of_mem_divisors d.property))
    (Nat.pos_of_ne_zero (divisor_ne_zero d.property))).ne'⟩

def divisorMellinIntegral (N : ℕ) (hN : N ≠ 0) (d : N.divisors) (w : ℝ → ℂ)
    (κ : ℝ) (s : Fin 4 → ℂ) (x : ℝ) : ℂ :=
  let _ : NeZero (N/d.val) := divisorQuotientNeZero N hN d
  ∫ v : ℝ, correctedMellinIntegrand (N/d.val) d.val w κ s (x/d.val) v

def displacedRemainder (N : ℕ) (hN : N ≠ 0) (w : ℝ → ℂ) (κ : ℝ)
    (s : Fin 4 → ℂ) (x : ℝ) : ℂ :=
  (N:ℂ)⁻¹ * ∑ d : N.divisors, divisorMellinIntegral N hN d w κ s x

theorem divisor_length_identity (N d : ℕ) (hN : N ≠ 0) (hd : d ∈ N.divisors)
    (x κ ε C : ℝ) (hx : 0 < x) :
    (N:ℝ)⁻¹ * (C*(d:ℝ)^ε*((N/d:ℕ):ℝ)^(1/2+ε)*(x/d)^κ) =
      C*x^κ*(N:ℝ)^(-1/2+ε)*(d:ℝ)^(-κ-1/2) := by
  have hNp : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hdp : (0:ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (divisor_ne_zero hd)
  rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hdp.ne',Real.div_rpow hNp.le hdp.le,
    Real.div_rpow hx.le hdp.le]
  have hpowN : (N:ℝ)^(-1/2+ε)*(N:ℝ) = (N:ℝ)^(1/2+ε) := by
    calc
      _ = (N:ℝ)^(-1/2+ε)*(N:ℝ)^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hNp]; congr 1; ring
  have hpowd : (d:ℝ)^(-κ-1/2)*(d:ℝ)^κ*(d:ℝ)^(1/2+ε) = (d:ℝ)^ε := by
    rw [← Real.rpow_add hdp,← Real.rpow_add hdp]
    congr 1
    ring
  rw [← hpowd,← hpowN]
  field_simp

theorem divisor_negative_power_sum (κ : ℝ) (hκ : 1/2 < κ) (N : ℕ) :
    (∑ d ∈ N.divisors, (d:ℝ)^(-κ-1/2)) ≤ ∑' d : ℕ, (d:ℝ)^(-κ-1/2) := by
  have H : Summable (fun d : ℕ => (d:ℝ)^(-κ-1/2)) := Real.summable_nat_rpow.mpr (by linarith)
  exact Summable.sum_le_tsum N.divisors (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _) H

theorem displacedRemainder_bound {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1:ℝ) 2) (κ ε : ℝ) (hκ : 1/2 < κ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ hN : N ≠ 0,
      ∀ s : Fin 4 → ℂ, (∀ j, ‖s j‖ ≤ min κ (ε/2)) →
      (∀ j, κ+(s j).re ∈ Icc (1/2:ℝ) (3/4)) → ∀ x : ℝ, 0 < x →
        ‖displacedRemainder N hN w κ s x‖ ≤ C*x^κ*(N:ℝ)^(-1/2+ε) := by
  obtain ⟨A,hA,H⟩ := correctedMellin_bound hw hws κ ε ε (by linarith) hε hε
  let J := ∑' d : ℕ, (d:ℝ)^(-κ-1/2)
  have hJ : 0 ≤ J := tsum_nonneg (fun d => Real.rpow_nonneg (Nat.cast_nonneg d) _)
  refine ⟨A*(J+1),by positivity,?_⟩
  intro N hN s hs hsr x hx
  have hnorm : ‖displacedRemainder N hN w κ s x‖ ≤
      ∑ d : N.divisors, A*x^κ*(N:ℝ)^(-1/2+ε)*(d.val:ℝ)^(-κ-1/2) := by
    rw [displacedRemainder,norm_mul,norm_inv,Complex.norm_natCast]
    apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d _
    let _ : NeZero (N/d.val) := divisorQuotientNeZero N hN d
    have hd : d.val ≠ 0 := divisor_ne_zero d.property
    have hdp : (0:ℝ) < d.val := by exact_mod_cast Nat.pos_of_ne_zero hd
    have h := (H (N/d.val) inferInstance d.val hd s hs hsr (x/d.val) (div_pos hx hdp)).2
    have hh := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (Nat.cast_nonneg N))
    exact hh.trans_eq (divisor_length_identity N d.val hN d.property x κ ε A hx)
  calc
    _ ≤ A*x^κ*(N:ℝ)^(-1/2+ε) * ∑ d : N.divisors, (d.val:ℝ)^(-κ-1/2) := by
      simpa only [Finset.mul_sum] using hnorm
    _ ≤ A*x^κ*(N:ℝ)^(-1/2+ε) * J := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (Finset.sum_coe_sort N.divisors (fun d : ℕ => (d:ℝ)^(-κ-1/2))).le.trans
        (divisor_negative_power_sum κ hκ N)
    _ ≤ A*x^κ*(N:ℝ)^(-1/2+ε) * (J+1) := by gcongr; linarith
    _ = _ := by ring

theorem displacedRemainder_scaled_bound {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1:ℝ) 2) (κ ε : ℝ) (hκ : 1/2 < κ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ hN : N ≠ 0,
      ∀ s : Fin 4 → ℂ, (∀ j, ‖s j‖ ≤ min κ (ε/2)) →
      (∀ j, κ+(s j).re ∈ Icc (1/2:ℝ) (3/4)) → ∀ T : ℝ, 0 < T →
        ‖displacedRemainder N hN w κ s ((N:ℝ)*T)‖ ≤ C*T^κ*(N:ℝ)^(κ-1/2+ε) := by
  obtain ⟨C,hC,H⟩ := displacedRemainder_bound hw hws κ ε hκ hε
  refine ⟨C,hC,?_⟩
  intro N hN s hs hsr T hT
  have hNp : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  apply (H N hN s hs hsr _ (mul_pos hNp hT)).trans_eq
  rw [Real.mul_rpow hNp.le hT.le]
  calc
    _ = C*T^κ*((N:ℝ)^κ*(N:ℝ)^(-1/2+ε)) := by ring
    _ = _ := by rw [← Real.rpow_add hNp]; congr 2; ring

end
end SixthMoment.Source.NoDPGlobalLFactorization
