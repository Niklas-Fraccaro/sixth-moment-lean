import Sechstmoment.Analysis.Mellin.FourierApproximation

/-! Full-time control of the actual Fourier truncation. The small uniform
approximation error handles |t|<=T^2; uniform Schwartz decay handles the
remaining times. A single integrable rational majorant covers both regions. -/

namespace Sechstmoment.Source
open Complex Real Set MeasureTheory
open scoped FourierTransform
noncomputable section
set_option maxHeartbeats 1000000

theorem noDPTimeTruncation_pointwise (h : SchwartzMap ℝ ℂ)
    (hs : tsupport (𝓕⁻ (h:ℝ → ℂ)) ⊆ Icc (1:ℝ) 2) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, max 3 (100*Real.pi) ≤ T → ∀ t : ℝ,
      (1+|t|)^K*‖𝓕⁻ (noDPFourierCutoff h (T/(100*Real.pi))) (t/T)-
        𝓕⁻ (h:ℝ → ℂ) (t/T)‖ ≤ C/(T^2*(1+t^2)) := by
  let n := 2*K+6
  let J := ∫ ξ : ℝ, |ξ|^n*‖h ξ‖
  let A := (100*Real.pi)^n*J
  have hJ : 0 ≤ J := integral_nonneg (fun _ => by positivity)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  obtain ⟨D,hD,hdecay⟩ := noDPFourierCutoff_uniform_inverse_decay h n
  let C := (2:ℝ)^(K+1)*(A+D+1)
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro T hT t
  have hT3 : 3 ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hp : 0 < 100*Real.pi := by positivity
  let H := T/(100*Real.pi)
  have hH : 1 ≤ H := (le_div_iff₀ hp).mpr (by simpa using (le_max_right _ _).trans hT)
  have hH0 : 0 < H := by linarith
  let r := |t|
  let E := ‖𝓕⁻ (noDPFourierCutoff h H) (t/T)-𝓕⁻ (h:ℝ → ℂ) (t/T)‖
  have hr : 0 ≤ r := abs_nonneg _
  have hE : 0 ≤ E := norm_nonneg _
  have happrox : T^n*E ≤ A := by
    have Hbound := noDPFourierCutoff_inverse_error h hH0 n (t/T)
    calc
      _ = (100*Real.pi)^n*(H^n*E) := by
        dsimp only [H]
        rw [div_pow]
        field_simp [hp.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left Hbound (by positivity)
  have hpoint : T^2*(1+t^2)*(1+r)^K*E ≤ C := by
    by_cases hnear : r ≤ T^2
    · have hr2 : r^2 ≤ T^4 := by
        have Hpow := pow_le_pow_left₀ hr hnear 2
        simpa only [← pow_mul] using Hpow
      have ht2 : t^2 = r^2 := (sq_abs t).symm
      have hfirst : 1+t^2 ≤ 2*T^4 := by
        have Hpow := one_le_pow₀ hT1 (n := 4)
        rw [ht2]
        linarith
      have hsecond : 1+r ≤ 2*T^2 := by linarith [one_le_pow₀ hT1 (n := 2)]
      have hscale : T^2*(1+t^2)*(1+r)^K ≤ (2:ℝ)^(K+1)*T^n := by
        calc
          _ ≤ T^2*(2*T^4)*(2*T^2)^K := by gcongr
          _ = _ := by
            dsimp only [n]
            rw [pow_add T (2*K) 6,pow_mul T 2 K,pow_succ (2:ℝ) K,mul_pow]
            ring
      calc
        _ ≤ ((2:ℝ)^(K+1)*T^n)*E := mul_le_mul_of_nonneg_right hscale hE
        _ = (2:ℝ)^(K+1)*(T^n*E) := by ring
        _ ≤ (2:ℝ)^(K+1)*A := mul_le_mul_of_nonneg_left happrox (by positivity)
        _ ≤ _ := by dsimp only [C]; gcongr; linarith
    · have hfar : T^2 ≤ r := le_of_lt (lt_of_not_ge hnear)
      have hr1 : 1 ≤ r := (one_le_pow₀ hT1 (n := 2)).trans hfar
      have hzero : 𝓕⁻ (h:ℝ → ℂ) (t/T) = 0 := by
        apply Function.notMem_support.mp
        intro hm
        have Hsupp := hs (subset_tsupport _ hm)
        have htx : |t/T| ≤ 2 := by rw [abs_of_nonneg (by linarith [Hsupp.1])]; exact Hsupp.2
        rw [abs_div,abs_of_pos hT0] at htx
        have Hlow : T ≤ r/T := (le_div_iff₀ hT0).mpr (by simpa only [pow_two] using hfar)
        linarith
      have hdec : r^n*E ≤ D*T^n := by
        have Hd := hdecay H hH (t/T)
        have hsimple : |t/T|^n*‖𝓕⁻ (noDPFourierCutoff h H) (t/T)‖ ≤ D := by
          apply (mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (abs_nonneg _) (show |t/T| ≤ 2*Real.pi* |t/T| by
              nlinarith [Real.two_le_pi,abs_nonneg (t/T)]) n) (norm_nonneg _)).trans Hd
        dsimp only [E]
        rw [hzero,sub_zero]
        rw [abs_div,abs_of_pos hT0,div_pow] at hsimple
        apply (div_le_iff₀ (pow_pos hT0 n)).mp
        convert hsimple using 1
        ring
      have hscale : T^(n+2) ≤ r^(K+4) := by
        have Hpow := pow_le_pow_left₀ (sq_nonneg T) hfar (K+4)
        simpa only [← pow_mul,show n+2 = 2*(K+4) by dsimp [n]; omega] using Hpow
      have hcancel : T^2*r^(K+2)*E ≤ D := by
        have Hmul := mul_le_mul_of_nonneg_right hscale
          (mul_nonneg (pow_nonneg hr (K+2)) hE)
        have Hchain : T^n*(T^2*r^(K+2)*E) ≤ T^n*D := by
          calc
            _ = T^(n+2)*(r^(K+2)*E) := by rw [pow_add]; ring
            _ ≤ r^(K+4)*(r^(K+2)*E) := Hmul
            _ = r^n*E := by rw [← mul_assoc,← pow_add,show K+4+(K+2) = n by dsimp [n]; omega]
            _ ≤ T^n*D := hdec.trans_eq (by ring)
        exact (mul_le_mul_iff_of_pos_left (pow_pos hT0 n)).mp Hchain
      have hfirst : 1+t^2 ≤ 2*r^2 := by
        rw [← sq_abs t]
        dsimp only [r] at hr1 ⊢
        nlinarith
      have hsecond : 1+r ≤ 2*r := by linarith
      calc
        _ ≤ T^2*(2*r^2)*(2*r)^K*E := by gcongr
        _ = (2:ℝ)^(K+1)*(T^2*r^(K+2)*E) := by
          rw [mul_pow,pow_succ,pow_add]
          ring
        _ ≤ (2:ℝ)^(K+1)*D := mul_le_mul_of_nonneg_left hcancel (by positivity)
        _ ≤ _ := by dsimp only [C]; gcongr; linarith
  apply (le_div_iff₀ (by positivity : 0 < T^2*(1+t^2))).mpr
  calc
    _ = T^2*(1+t^2)*(1+r)^K*E := by dsimp only [r,E,H]; ring
    _ ≤ C := hpoint

end
end Sechstmoment.Source
