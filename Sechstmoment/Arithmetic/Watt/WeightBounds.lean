import Sechstmoment.Arithmetic.QuadraticDivisor.Reduction.WattWeights
import Sechstmoment.Arithmetic.Watt.Partition


namespace DivisorProof
namespace Watt41
open Real Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 2000000

theorem derivative_dilation {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    {b : ℕ → ℝ} (hd : ∀ j x, 0 < x → ‖iteratedDeriv j f x‖ ≤ b j*x^(-(j : ℝ)))
    {c : ℝ} (hc : 0 < c) (j : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖iteratedDeriv j (fun x => f (c*x)) x‖ ≤ b j*x^(-(j : ℝ)) := by
  rw [iteratedDeriv_comp_const_smul (hf.of_le (by exact_mod_cast le_top)) c]
  dsimp only
  rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hc.le j)]
  have he : c^j*(c*x)^(-(j : ℝ)) = x^(-(j : ℝ)) := by
    rw [Real.rpow_neg (mul_pos hc hx).le,Real.rpow_natCast,mul_pow,
      Real.rpow_neg hx.le,Real.rpow_natCast]
    field_simp [hc.ne',hx.ne']
  calc c^j*‖iteratedDeriv j f (c*x)‖ ≤ c^j*(b j*(c*x)^(-(j : ℝ))) :=
      mul_le_mul_of_nonneg_left (hd j (c*x) (mul_pos hc hx)) (pow_nonneg hc.le j)
    _ = b j*x^(-(j : ℝ)) := by rw [mul_left_comm,he]

def scaledTransition (A x : ℝ) : ℂ := (transition (x/A) : ℂ)

theorem scaledTransition_smooth (A : ℝ) : ContDiff ℝ ∞ (scaledTransition A) :=
  Complex.ofRealCLM.contDiff.comp (transition_smooth.comp (contDiff_id.div_const A))

theorem scaledTransition_derivative {b : ℕ → ℝ}
    (hd : ∀ j x, 0 < x → ‖iteratedDeriv j transition x‖ ≤ b j*x^(-(j : ℝ)))
    {A : ℝ} (hA : 0 < A) (j : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖iteratedDeriv j (scaledTransition A) x‖ ≤ b j*x^(-(j : ℝ)) := by
  have hfc : ContDiff ℝ ∞ (fun x => (transition x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp transition_smooth
  have hd' : ∀ j x, 0 < x →
      ‖iteratedDeriv j (fun x => (transition x : ℂ)) x‖ ≤ b j*x^(-(j : ℝ)) := by
    intro j x hx
    rw [norm_iteratedDeriv_ofReal transition_smooth]
    exact hd j x hx
  have heq : scaledTransition A = fun x => (transition (A⁻¹*x) : ℂ) := by
    funext x
    simp only [scaledTransition,div_eq_mul_inv,mul_comm]
  rw [heq]
  exact derivative_dilation hfc hd' (inv_pos.mpr hA) j hx

theorem block_derivative_bound {b : ℕ → ℝ} (hb : ∀ j, 0 ≤ b j)
    (hd : ∀ j x, 0 < x → ‖iteratedDeriv j transition x‖ ≤ b j*x^(-(j : ℝ)))
    {A : ℝ} (hA : 0 < A) (k j : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖iteratedDeriv j (fun x => (block A k x : ℂ)) x‖ ≤ (2*b j)*x^(-(j : ℝ)) := by
  cases k with
  | zero =>
    have hd' := scaledTransition_derivative hd hA j hx
    change ‖iteratedDeriv j (scaledTransition A) x‖ ≤ _
    have hp := Real.rpow_nonneg hx.le (-(j : ℝ))
    have hb' := hb j
    have hbp := mul_nonneg hb' hp
    linarith
  | succ k =>
    have heq : (fun x => (block A (k+1) x : ℂ)) =
        (fun x => scaledTransition (blockScale A (k+1)) x-scaledTransition (blockScale A k) x) := by
      funext x
      simp only [block,scaledTransition,Complex.ofReal_sub]
    rw [heq,iteratedDeriv_fun_sub
      ((scaledTransition_smooth _).of_le (by exact_mod_cast le_top)).contDiffAt
      ((scaledTransition_smooth _).of_le (by exact_mod_cast le_top)).contDiffAt]
    apply (norm_sub_le _ _).trans
    have h₁ := scaledTransition_derivative hd (blockScale_pos hA (k+1)) j hx
    have h₂ := scaledTransition_derivative hd (blockScale_pos hA k) j hx
    linarith

theorem delta_derivative_product {f g : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {a b : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hdf : ∀ j x, 0 < x → ‖iteratedDeriv j f x‖ ≤ a j*(δ*x)^(-(j : ℝ)))
    (hdg : ∀ j x, 0 < x → ‖iteratedDeriv j g x‖ ≤ b j*x^(-(j : ℝ)))
    (j : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖iteratedDeriv j (fun x => f x*g x) x‖ ≤
      derivativeProductBound a b j*(δ*x)^(-(j : ℝ)) := by
  rw [iteratedDeriv_fun_mul (hf.of_le (by exact_mod_cast le_top)).contDiffAt
    (hg.of_le (by exact_mod_cast le_top)).contDiffAt]
  apply (norm_sum_le _ _).trans
  unfold derivativeProductBound
  rw [sum_mul]
  apply sum_le_sum
  intro i hi
  have hij : i ≤ j := Nat.le_of_lt_succ (mem_range.mp hi)
  have hpow : (δ*x)^(-(i : ℝ))*(δ*x)^(-((j-i : ℕ) : ℝ)) = (δ*x)^(-(j : ℝ)) := by
    rw [← Real.rpow_add (mul_pos hδ hx),Nat.cast_sub hij]
    congr 1
    ring
  have hsmall : x^(-((j-i : ℕ) : ℝ)) ≤ (δ*x)^(-((j-i : ℕ) : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos hδ hx) (by nlinarith)
      (neg_nonpos.mpr (Nat.cast_nonneg _))
  simp only [norm_mul,Complex.norm_natCast]
  have hai := ha i
  have hbi := hb (j-i)
  have hcoef : 0 ≤ (j.choose i : ℝ)*(a i*(δ*x)^(-(i : ℝ))) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hai (Real.rpow_nonneg (by positivity) _))
  calc _ ≤ (j.choose i : ℝ)*(a i*(δ*x)^(-(i : ℝ)))*
        (b (j-i)*x^(-((j-i : ℕ) : ℝ))) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hdf i x hx) (Nat.cast_nonneg _))
          (hdg (j-i) x hx) (norm_nonneg _) hcoef
    _ ≤ (j.choose i : ℝ)*(a i*(δ*x)^(-(i : ℝ)))*
        (b (j-i)*(δ*x)^(-((j-i : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsmall hbi) hcoef
    _ = _ := by
      calc _ = ((j.choose i : ℝ)*a i*b (j-i))*
          ((δ*x)^(-(i : ℝ))*(δ*x)^(-((j-i : ℕ) : ℝ))) := by ring
        _ = _ := by rw [hpow]

theorem weightedBlock_derivative_data (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) :
    ∃ b : ℕ → ℝ, (∀ j, 0 ≤ b j) ∧
      ∀ (u : ℝ → ℂ) (A δ : ℝ), ContDiff ℝ ∞ u → 0 < A → 0 < δ → δ ≤ 1 →
      (∀ j x, 0 < x → ‖iteratedDeriv j u x‖ ≤ a j*(δ*x)^(-(j : ℝ))) →
      ∀ k j x, 0 < x →
        ‖iteratedDeriv j (weightedBlock u A k) x‖ ≤ b j*(δ*x)^(-(j : ℝ)) := by
  obtain ⟨c,hc,hd⟩ := transition_derivative_bounds
  have hc' : ∀ j, 0 ≤ 2*c j := fun j => mul_nonneg (by norm_num) (hc j)
  refine ⟨derivativeProductBound a (fun j => 2*c j),derivativeProductBound_nonneg ha hc',?_⟩
  intro u A δ hu hA hδ hδ₁ hdu k j x hx
  exact delta_derivative_product hu
    (Complex.ofRealCLM.contDiff.comp (block_smooth A k)) ha hc' hδ hδ₁ hdu
    (fun j x hx => block_derivative_bound hc hd hA k j hx) j hx

end
end Watt41
end DivisorProof
