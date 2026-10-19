import Sechstmoment.Arithmetic.Watt.PoissonCompletion

/-! Uniform Fourier decay for general smooth profiles, with all constants
depending only on fixed derivative bounds. -/

namespace DivisorProof
namespace Watt41
open Real MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff FourierTransform SchwartzMap
noncomputable section
set_option maxHeartbeats 2000000

structure NormalizedProfileData (bounds : ℕ → ℝ) (g : ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ g
  support : tsupport g ⊆ Icc 0 2
  derivatives : ∀ j x, ‖iteratedDeriv j g x‖ ≤ bounds j

theorem NormalizedProfileData.compactSupport {bounds : ℕ → ℝ} {g : ℝ → ℂ}
    (h : NormalizedProfileData bounds g) : HasCompactSupport g :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) h.support

theorem NormalizedProfileData.derivative_integrable {bounds : ℕ → ℝ} {g : ℝ → ℂ}
    (h : NormalizedProfileData bounds g) (j : ℕ) :
    Integrable (iteratedFDeriv ℝ j g) :=
  (h.smooth.continuous_iteratedFDeriv (by exact_mod_cast le_top)).integrable_of_hasCompactSupport
    (h.compactSupport.iteratedFDeriv j)

theorem NormalizedProfileData.derivative_integral_le {bounds : ℕ → ℝ} {g : ℝ → ℂ}
    (h : NormalizedProfileData bounds g) (j : ℕ) :
    (∫ x : ℝ, ‖iteratedFDeriv ℝ j g x‖) ≤ 2*bounds j := by
  have hb (x : ℝ) : ‖iteratedFDeriv ℝ j g x‖ ≤ bounds j := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact h.derivatives j x
  have hint := (h.derivative_integrable j).norm
  have heq : (∫ x : ℝ in Icc 0 2, ‖iteratedFDeriv ℝ j g x‖) =
      ∫ x : ℝ, ‖iteratedFDeriv ℝ j g x‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hout : x ∉ tsupport g := fun hx' => hx (h.support hx')
    have hz : iteratedFDeriv ℝ j g x = 0 := by
      by_contra hn
      exact hout (support_iteratedFDeriv_subset j hn)
    exact norm_eq_zero.mpr hz
  rw [← heq]
  calc _ ≤ ∫ x : ℝ in Icc 0 2, bounds j :=
      setIntegral_mono_on hint.integrableOn continuous_const.integrableOn_Icc
        measurableSet_Icc (fun x _ => hb x)
    _ = 2*bounds j := by simp [mul_comm]

theorem NormalizedProfileData.fourier_moment_le {bounds : ℕ → ℝ} {g : ℝ → ℂ}
    (h : NormalizedProfileData bounds g) (J : ℕ) (w : ℝ) :
    ‖w‖^J*‖𝓕 g w‖ ≤ 2^J*∑ j ∈ range (J+1), 2*bounds j := by
  have hint : ∀ k n : ℕ, (k : ℕ∞) ≤ 0 → (n : ℕ∞) ≤ ⊤ →
      Integrable (fun x : ℝ => ‖x‖^k*‖iteratedFDeriv ℝ n g x‖) := by
    intro k n hk _
    have hk0 : k = 0 := by exact_mod_cast (le_antisymm hk bot_le)
    subst k
    simpa only [pow_zero, one_mul] using (h.derivative_integrable n).norm
  have hm := Real.pow_mul_norm_iteratedFDeriv_fourier_le
    (K := 0) (N := ⊤) (k := 0) (n := J) h.smooth hint le_rfl le_top w
  simp only [norm_iteratedFDeriv_zero, pow_zero, Nat.cast_zero, zero_add,
    mul_zero, one_mul, range_one, sum_product, sum_singleton] at hm
  apply hm.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact sum_le_sum fun j _ => h.derivative_integral_le j

def fourierDecayConstant (bounds : ℕ → ℝ) (J : ℕ) : ℝ :=
  2^J*(2*bounds 0+2^J*∑ j ∈ range (J+1), 2*bounds j)

theorem fourierDecayConstant_nonneg {bounds : ℕ → ℝ}
    (hb : ∀ j, 0 ≤ bounds j) (J : ℕ) : 0 ≤ fourierDecayConstant bounds J := by
  unfold fourierDecayConstant
  have hb0 := hb 0
  have hsum : 0 ≤ ∑ j ∈ range (J+1), 2*bounds j :=
    sum_nonneg fun j _ => mul_nonneg (by norm_num) (hb j)
  positivity

theorem NormalizedProfileData.fourier_decay {bounds : ℕ → ℝ} {g : ℝ → ℂ}
    (h : NormalizedProfileData bounds g) (hb : ∀ j, 0 ≤ bounds j) (J : ℕ) (w : ℝ) :
    ‖𝓕 g w‖ ≤ fourierDecayConstant bounds J/(1+‖w‖)^J := by
  have hb0 := hb 0
  have hsum : 0 ≤ ∑ j ∈ range (J+1), 2*bounds j :=
    sum_nonneg fun j _ => mul_nonneg (by norm_num) (hb j)
  have hzero : ‖𝓕 g w‖ ≤ 2*bounds 0 := by
    simpa only [pow_zero, one_mul, zero_add, Finset.range_one, sum_singleton] using
      h.fourier_moment_le 0 w
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1+‖w‖) J)).mpr
  rw [mul_comm]
  by_cases hw : ‖w‖ ≤ 1
  · calc (1+‖w‖)^J*‖𝓕 g w‖ ≤ 2^J*(2*bounds 0) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) J) hzero
          (norm_nonneg _) (by positivity)
      _ ≤ fourierDecayConstant bounds J := by
        unfold fourierDecayConstant
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (mul_nonneg (by positivity) hsum)) (by positivity)
  · have hm := h.fourier_moment_le J w
    calc (1+‖w‖)^J*‖𝓕 g w‖ ≤ (2*‖w‖)^J*‖𝓕 g w‖ := by
          gcongr
          linarith
      _ = 2^J*(‖w‖^J*‖𝓕 g w‖) := by rw [mul_pow]; ring
      _ ≤ 2^J*(2^J*∑ j ∈ range (J+1), 2*bounds j) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ ≤ fourierDecayConstant bounds J := by
        unfold fourierDecayConstant
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (by positivity)) (by positivity)

/-- Change of scale in the literal integral, including the normalising factor. -/
theorem fourierCoefficient_rescale (g : ℝ → ℂ) (c : ℕ) {r : ℝ}
    (hr : 0 < r) (l : ℤ) :
    fourierCoefficient g c l =
      (r : ℂ)*𝓕 (fun x : ℝ => g ((c : ℝ)*(r*x))) (-(l : ℝ)*r) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have h := Measure.integral_comp_mul_left
    (fun x : ℝ => g ((c : ℝ)*x)*ePhase ((l : ℝ)*x)) r
  have heq : (fun x : ℝ =>
      Complex.exp ((↑(-2*Real.pi*x*(-(l : ℝ)*r)) : ℂ)*Complex.I) •
        g ((c : ℝ)*(r*x))) =
      (fun x : ℝ => g ((c : ℝ)*(r*x))*ePhase ((l : ℝ)*(r*x))) := by
    funext x
    have hexp : Complex.exp ((↑(-2*Real.pi*x*(-(l : ℝ)*r)) : ℂ)*Complex.I) =
        ePhase ((l : ℝ)*(r*x)) := by
      unfold ePhase
      congr 1
      push_cast
      ring
    rw [hexp]
    simp only [smul_eq_mul]
    ring
  rw [heq]
  change fourierCoefficient g c l = (r : ℂ)*_
  rw [h, abs_of_pos (inv_pos.mpr hr), RCLike.real_smul_eq_coe_mul]
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  change fourierCoefficient g c l =
    (r : ℂ)*(((r⁻¹ : ℝ) : ℂ)*fourierCoefficient g c l)
  rw [Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hrc, one_mul]

theorem fourierCoefficient_decay {bounds : ℕ → ℝ} {g : ℝ → ℂ} {c : ℕ} {r : ℝ}
    (hr : 0 < r) (hb : ∀ j, 0 ≤ bounds j)
    (h : NormalizedProfileData bounds (fun x : ℝ => g ((c : ℝ)*(r*x))))
    (J : ℕ) (l : ℤ) :
    ‖fourierCoefficient g c l‖ ≤
      r*fourierDecayConstant bounds J/(1+|(l : ℝ)| * r)^J := by
  rw [fourierCoefficient_rescale g c hr l, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hr.le]
  have hm := h.fourier_decay hb J (-(l : ℝ)*r)
  simpa only [norm_mul, norm_neg, Real.norm_eq_abs, abs_of_pos hr, mul_div_assoc] using
    mul_le_mul_of_nonneg_left hm hr.le

end
end Watt41
end DivisorProof
