import SixthMoment.Arithmetic.Watt.CompletedBlock
import SixthMoment.Arithmetic.Watt.Ramanujan


namespace DivisorProof
namespace Watt41
open Real MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 2000000

theorem gamma_fourier_zero_bound {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hg : ∀ i j, 0 ≤ g i j) (hV : 0 < p.V) (r s : ℕ) {t : ℝ} (ht : 0 < t)
    {c : ℕ} (hc : 0 < c) :
    ‖fourierCoefficient (fun v => γ r s v t) c 0‖ ≤ (4*g 0 0)*(p.V/c) := by
  have h := gamma_fourier_decay hw hg hV r s ht hc 0 0
  norm_num [fourierDecayConstant,gammaProfileBounds] at h
  convert h using 1
  ring

theorem completedTerm_zero_bound {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hg : ∀ i j, 0 ≤ g i j) (hV : 0 < p.V) (positive : Bool) (h k r : ℕ)
    {s t : ℕ} (hs : 0 < s) (ht : 0 < t) (hr : r.Coprime (s*t)) :
    ‖completedTerm p γ positive h k r s t 0‖ ≤
      (4*g 0 0)*(p.V/(s*t : ℕ))*(Nat.gcd (h*k) (s*t) : ℝ) := by
  have hc := Nat.mul_pos hs ht
  have hnat : (phaseSign positive*(h : ℤ)*k).natAbs = h*k := by
    cases positive <;> simp [phaseSign,Int.natAbs_mul]
  have hRam := ramanujan_bound hc
    ((phaseSign positive*(h : ℤ)*k)*(inverseRepresentative r (s*t) : ℤ))
  rw [inverse_parameter_gcd hc hr,hnat] at hRam
  unfold completedTerm
  rw [norm_mul,neg_zero]
  exact mul_le_mul (gamma_fourier_zero_bound hw hg hV r s (by exact_mod_cast ht) hc)
    hRam (norm_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) (hg 0 0))
      (div_nonneg hV.le (Nat.cast_nonneg _)))

theorem sum_sum_gcd_real_le {H K : ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K)
    {c : ℕ} (hc : 0 < c) :
    (∑ h ∈ positiveRange H, ∑ k ∈ positiveRange K, (Nat.gcd (h*k) c : ℝ)) ≤
      H*K*(c.divisors.card : ℝ)^2 := by
  have hnat := sum_sum_gcd_le ⌊H⌋₊ ⌊K⌋₊ c hc.ne'
  have hreal : (∑ h ∈ positiveRange H, ∑ k ∈ positiveRange K, (Nat.gcd (h*k) c : ℝ)) ≤
      (⌊H⌋₊ : ℝ)*⌊K⌋₊*(c.divisors.card : ℝ)^2 := by exact_mod_cast hnat
  apply hreal.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (Nat.floor_le hH) (Nat.floor_le hK) (Nat.cast_nonneg _) hH) (sq_nonneg _)

theorem zero_frequency_fibre_bound {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hb : ∀ j, 0 ≤ b j) (hg : ∀ i j, 0 ≤ g i j)
    (hH : 0 ≤ p.H) (hK : 0 ≤ p.C) (hV : 0 < p.V)
    (positive : Bool) (r : ℕ) {s t : ℕ} (hs : 0 < s) (ht : 0 < t)
    (hr : r.Coprime (s*t)) :
    ‖∑ h ∈ positiveRange p.H, ∑ k ∈ positiveRange p.C,
      u₀ h*u₁ k*completedTerm p γ positive h k r s t 0‖ ≤
      b 0^2*(4*g 0 0)*(p.V/(s*t : ℕ))*p.H*p.C*((s*t).divisors.card : ℝ)^2 := by
  have hweight (x : ℝ) (hx : 0 < x) : ‖u₀ x‖+‖u₁ x‖ ≤ b 0 := by
    simpa only [iteratedDeriv_zero,Nat.cast_zero,neg_zero,Real.rpow_zero,mul_one] using
      hw.derivatives 0 x hx
  let D := b 0^2*(4*g 0 0)*(p.V/(s*t : ℕ))
  have hD : 0 ≤ D := mul_nonneg
    (mul_nonneg (sq_nonneg (b 0)) (mul_nonneg (by norm_num) (hg 0 0)))
    (div_nonneg hV.le (Nat.cast_nonneg _))
  have hp (h : ℕ) (hh : h ∈ positiveRange p.H) (k : ℕ) (hk : k ∈ positiveRange p.C) :
      ‖u₀ h*u₁ k*completedTerm p γ positive h k r s t 0‖ ≤ D*(Nat.gcd (h*k) (s*t) : ℝ) := by
    have hhp : (0 : ℝ) < h := by exact_mod_cast (mem_positiveRange.mp hh).1
    have hkp : (0 : ℝ) < k := by exact_mod_cast (mem_positiveRange.mp hk).1
    have h₀ : ‖u₀ h‖ ≤ b 0 := (le_add_of_nonneg_right (norm_nonneg _)).trans (hweight h hhp)
    have h₁ : ‖u₁ k‖ ≤ b 0 := (le_add_of_nonneg_left (norm_nonneg _)).trans (hweight k hkp)
    rw [norm_mul,norm_mul]
    have hprod : ‖u₀ h‖*‖u₁ k‖ ≤ b 0^2 := by
      simpa only [pow_two] using mul_le_mul h₀ h₁ (norm_nonneg _) (hb 0)
    have hp := mul_le_mul hprod (completedTerm_zero_bound hw hg hV positive h k r hs ht hr)
      (norm_nonneg _) (sq_nonneg (b 0))
    exact hp.trans_eq (by dsimp [D]; ring)
  calc
    _ ≤ ∑ h ∈ positiveRange p.H, ∑ k ∈ positiveRange p.C,
        D*(Nat.gcd (h*k) (s*t) : ℝ) := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro h hh
      exact (norm_sum_le _ _).trans (sum_le_sum (fun k hk => hp h hh k hk))
    _ = D*(∑ h ∈ positiveRange p.H, ∑ k ∈ positiveRange p.C, (Nat.gcd (h*k) (s*t) : ℝ)) := by
      simp only [mul_sum]
    _ ≤ D*(p.H*p.C*((s*t).divisors.card : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (sum_sum_gcd_real_le hH hK (Nat.mul_pos hs ht)) hD
    _ = _ := by dsimp [D]; ring

theorem completedTerm_decay {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hg : ∀ i j, 0 ≤ g i j) (hV : 0 < p.V) (positive : Bool) (h k r : ℕ)
    {s t : ℕ} (hs : 0 < s) (ht : 0 < t) (J : ℕ) (l : ℤ) :
    ‖completedTerm p γ positive h k r s t l‖ ≤
      (p.V/(s*t : ℕ))*(fourierDecayConstant (gammaProfileBounds g) J*(s*t : ℕ))/
        (1+|(l : ℝ)| *(p.V/(s*t : ℕ)))^J := by
  have hcoeff := gamma_fourier_decay hw hg hV r s (t := (t : ℝ)) (by exact_mod_cast ht) (Nat.mul_pos hs ht) J l
  unfold completedTerm
  rw [norm_mul]
  apply (mul_le_mul hcoeff (classicalKloostermanSum_trivial _ _ (s*t)) (norm_nonneg _)
    (div_nonneg (mul_nonneg (div_nonneg hV.le (Nat.cast_nonneg _))
      (fourierDecayConstant_nonneg (gammaProfileBounds_nonneg hg) J))
      (pow_nonneg (by positivity) J))).trans_eq
  ring

theorem completedTerm_tail_bound {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hg : ∀ i j, 0 ≤ g i j) (hV : 0 < p.V) (positive : Bool) (h k r : ℕ)
    {s t : ℕ} (hs : 0 < s) (ht : 0 < t) {L : ℝ} (hL : 0 ≤ L) (J : ℕ) :
    Summable (fun l : ℤ => if L < |(l : ℝ)| then completedTerm p γ positive h k r s t l else 0) ∧
      ‖∑' l : ℤ, if L < |(l : ℝ)| then completedTerm p γ positive h k r s t l else 0‖ ≤
        (fourierDecayConstant (gammaProfileBounds g) (J+2)*(s*t : ℕ)/
          ((p.V/(s*t : ℕ))*(1+L*(p.V/(s*t : ℕ)))^J))*inverseSquareMass := by
  apply fourier_tail_bound _ (div_pos hV (by exact_mod_cast Nat.mul_pos hs ht)) hL J
    (fun l => completedTerm_decay hw hg hV positive h k r hs ht (J+2) l)
  exact mul_nonneg (fourierDecayConstant_nonneg (gammaProfileBounds_nonneg hg) (J+2))
    (Nat.cast_nonneg _)

theorem dualLength_frequency_scale {p : WattScales} {E : ℝ}
    (hV : 0 < p.V) (hE : 0 ≤ E) {s t : ℕ} (hs : 0 < s) (ht : 0 < t)
    (hsS : (s : ℝ) ≤ p.S) (htP : (t : ℝ) ≤ p.P) :
    E ≤ dualLength p E*(p.V/(s*t : ℕ)) := by
  have hcp : (0 : ℝ) < (s*t : ℕ) := by exact_mod_cast Nat.mul_pos hs ht
  have hS : 0 ≤ p.S := (Nat.cast_nonneg s).trans hsS
  have hcc : ((s*t : ℕ) : ℝ) ≤ p.S*p.P := by
    simpa only [Nat.cast_mul] using mul_le_mul hsS htP (Nat.cast_nonneg t) hS
  have heq : dualLength p E*(p.V/(s*t : ℕ)) = (p.S*p.P*E)/(s*t : ℕ) := by
    unfold dualLength
    field_simp [hV.ne']
  rw [heq]
  apply (le_div_iff₀ hcp).mpr
  nlinarith [mul_le_mul_of_nonneg_right hcc hE]

theorem completedTerm_tail_at_dualCutoff {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ E : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hg : ∀ i j, 0 ≤ g i j) (hV : 0 < p.V) (hE : 1 ≤ E)
    (positive : Bool) (h k r : ℕ) {s t : ℕ} (hs : 0 < s) (ht : 0 < t)
    (hsS : (s : ℝ) ≤ p.S) (htP : (t : ℝ) ≤ p.P) (J : ℕ) :
    ‖∑' l : ℤ, if dualLength p E/2 < |(l : ℝ)| then
      completedTerm p γ positive h k r s t l else 0‖ ≤
        ((2 : ℝ)^J*fourierDecayConstant (gammaProfileBounds g) (J+2)*((s*t : ℕ) : ℝ)^2/
          (p.V*E^J))*inverseSquareMass := by
  have hEp : 0 < E := by linarith
  have hSp : 0 < p.S := lt_of_lt_of_le (by exact_mod_cast hs) hsS
  have hPp : 0 < p.P := lt_of_lt_of_le (by exact_mod_cast ht) htP
  have hcp : (0 : ℝ) < (s*t : ℕ) := by exact_mod_cast Nat.mul_pos hs ht
  have hA := dualLength_pos hSp hPp hV hEp
  have htail := (completedTerm_tail_bound hw hg hV positive h k r hs ht
    (L := dualLength p E/2) (by positivity) J).2
  apply htail.trans
  apply mul_le_mul_of_nonneg_right _ inverseSquareMass_nonneg
  have hscale := dualLength_frequency_scale hV hEp.le hs ht hsS htP
  have hpow : (E/2)^J ≤ (1+(dualLength p E/2)*(p.V/(s*t : ℕ)))^J := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  calc
    _ ≤ (fourierDecayConstant (gammaProfileBounds g) (J+2)*(s*t : ℕ))/
        ((p.V/(s*t : ℕ))*(E/2)^J) :=
      div_le_div_of_nonneg_left
        (mul_nonneg (fourierDecayConstant_nonneg (gammaProfileBounds_nonneg hg) _) hcp.le)
        (by positivity) (mul_le_mul_of_nonneg_left hpow (div_pos hV hcp).le)
    _ = _ := by
      rw [div_pow]
      field_simp [hV.ne',hEp.ne',hcp.ne']

end
end Watt41
end DivisorProof
