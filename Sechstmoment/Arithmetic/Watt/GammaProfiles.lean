import Sechstmoment.Arithmetic.Watt.Fourier

/-! Normalisation and uniform Fourier control of the actual gamma slices.
The constants are explicit functions of the fixed mixed derivative bounds. -/

namespace DivisorProof
namespace Watt41
open Real Set Finset Classical
open scoped BigOperators ContDiff FourierTransform
noncomputable section
set_option maxHeartbeats 2000000

theorem iteratedDeriv_eq_zero_of_not_tsupport (g : ℝ → ℂ) (j : ℕ) (x : ℝ)
    (hx : x ∉ tsupport g) : iteratedDeriv j g x = 0 := by
  have hz : iteratedFDeriv ℝ j g x = 0 := by
    by_contra hn
    exact hx (support_iteratedFDeriv_subset j hn)
  apply norm_eq_zero.mp
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv,hz,norm_zero]

theorem gamma_slice_smooth {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (r s : ℕ) (t : ℝ) : ContDiff ℝ ∞ (fun x => γ r s x t) :=
  (hw.gamma_smooth r s).comp (contDiff_id.prodMk contDiff_const)

theorem gamma_slice_support {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (r s : ℕ) (t : ℝ) :
    tsupport (fun x => γ r s x t) ⊆ Icc (p.V/2) p.V := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hne : (fun z : ℝ × ℝ => γ r s z.1 z.2) (x,t) ≠ 0 := hx
  exact (hw.gamma_support r s (subset_tsupport _ hne)).1

theorem gamma_slice_derivative_bound {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (r s j : ℕ) {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    ‖iteratedDeriv j (fun x => γ r s x t) x‖ ≤ g j 0*x^(-(j : ℝ)) := by
  simpa only [iteratedDeriv_zero,Nat.cast_zero,neg_zero,Real.rpow_zero,mul_one] using
    hw.gamma_derivatives r s j 0 x t hx ht

def gammaProfileBounds (g : ℕ → ℕ → ℝ) (j : ℕ) : ℝ := 2^j*g j 0

theorem gammaProfileBounds_nonneg {g : ℕ → ℕ → ℝ}
    (hg : ∀ i j, 0 ≤ g i j) (j : ℕ) : 0 ≤ gammaProfileBounds g j :=
  mul_nonneg (by positivity) (hg j 0)

theorem gamma_normalized_data {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hg : ∀ i j, 0 ≤ g i j) (hV : 0 < p.V) (r s : ℕ) {t : ℝ} (ht : 0 < t) :
    NormalizedProfileData (gammaProfileBounds g) (fun x => γ r s (p.V*x) t) := by
  have hs := gamma_slice_smooth hw r s t
  have hsupport := gamma_slice_support hw r s t
  refine ⟨hs.comp (contDiff_const.mul contDiff_id),?_,?_⟩
  · apply closure_minimal _ isClosed_Icc
    intro x hx
    have hxv := hsupport (subset_tsupport _ hx)
    constructor <;> nlinarith [hxv.1,hxv.2]
  · intro j x
    rw [iteratedDeriv_comp_const_smul (hs.of_le (by exact_mod_cast le_top)) p.V]
    dsimp only
    rw [norm_smul,Real.norm_of_nonneg (pow_nonneg hV.le j)]
    by_cases hz : iteratedDeriv j (fun x => γ r s x t) (p.V*x) = 0
    · rw [hz,norm_zero,mul_zero]
      exact gammaProfileBounds_nonneg hg j
    have hxv : p.V*x ∈ tsupport (fun x => γ r s x t) := by
      by_contra hout
      exact hz (iteratedDeriv_eq_zero_of_not_tsupport _ j _ hout)
    have hxb := hsupport hxv
    have hx : 0 < x := by nlinarith [hxb.1]
    have hhalf : (1/2 : ℝ) ≤ x := by nlinarith [hxb.1]
    have hvx : 0 < p.V*x := mul_pos hV hx
    have hd := gamma_slice_derivative_bound hw r s j hvx ht
    have he : p.V^j*(p.V*x)^(-(j : ℝ)) = x^(-(j : ℝ)) := by
      rw [Real.rpow_neg hvx.le,Real.rpow_natCast,mul_pow,
        Real.rpow_neg hx.le,Real.rpow_natCast]
      field_simp [hV.ne',hx.ne']
    have hp : x^(-(j : ℝ)) ≤ (2 : ℝ)^j := by
      rw [Real.rpow_neg hx.le,Real.rpow_natCast]
      have hh := inv_anti₀ (pow_pos (by norm_num : (0 : ℝ) < 1/2) j)
        (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/2) hhalf j)
      simpa only [inv_pow,one_div,inv_inv] using hh
    calc p.V^j*‖iteratedDeriv j (fun x => γ r s x t) (p.V*x)‖ ≤
          p.V^j*(g j 0*(p.V*x)^(-(j : ℝ))) :=
        mul_le_mul_of_nonneg_left hd (pow_nonneg hV.le j)
      _ = g j 0*x^(-(j : ℝ)) := by rw [mul_left_comm,he]
      _ ≤ g j 0*(2 : ℝ)^j := mul_le_mul_of_nonneg_left hp (hg j 0)
      _ = gammaProfileBounds g j := by unfold gammaProfileBounds; ring

/-- Uniform rapid decay at the correct scale V/c, for every arithmetic slice. -/
theorem gamma_fourier_decay {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hg : ∀ i j, 0 ≤ g i j) (hV : 0 < p.V) (r s : ℕ) {t : ℝ} (ht : 0 < t)
    {c : ℕ} (hc : 0 < c) (J : ℕ) (l : ℤ) :
    ‖fourierCoefficient (fun v => γ r s v t) c l‖ ≤
      (p.V/c)*fourierDecayConstant (gammaProfileBounds g) J/
        (1+|(l : ℝ)| * (p.V/c))^J := by
  have hcp : (0 : ℝ) < c := by exact_mod_cast hc
  have hdata := gamma_normalized_data hw hg hV r s ht
  have heq : (fun x : ℝ => γ r s ((c : ℝ)*(p.V/c*x)) t) =
      (fun x : ℝ => γ r s (p.V*x) t) := by
    funext x
    congr 1
    field_simp
  exact fourierCoefficient_decay (div_pos hV hcp) (gammaProfileBounds_nonneg hg)
    (heq.symm ▸ hdata) J l

end
end Watt41
end DivisorProof
