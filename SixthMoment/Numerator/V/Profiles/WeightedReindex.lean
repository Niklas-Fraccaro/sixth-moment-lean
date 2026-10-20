import SixthMoment.Analysis.Harmonic.FiniteReindex
import SixthMoment.Arithmetic.Euler.Convolution.Factorization
import SixthMoment.Numerator.V.Profiles.SourceProfile


namespace SixthMoment.Source.NoDPHarmonic
open Real Complex Set Polynomial NoDPGlobalConvolution
open scoped BigOperators
noncomputable section

def profileWeight (η L : ℝ) (P : ℝ[X]) (n : ℕ) : ℂ :=
  (zeroExtendedPolynomialProfile η P (Real.log n/L) : ℂ)

theorem profileWeight_zero_of_lt {η L : ℝ} (hL : 0 < L) (P : ℝ[X])
    {n : ℕ} (hn : ⌊Real.exp (L*η)⌋₊ < n) : profileWeight η L P n = 0 := by
  have hlog : L*η < Real.log n := by
    simpa only [Real.log_exp] using
      Real.log_lt_log (Real.exp_pos (L*η)) (Nat.lt_of_floor_lt hn)
  have hmem : Real.log n/L ∉ Ico 0 η := by
    intro hm
    have := (div_lt_iff₀ hL).mp hm.2
    nlinarith
  simp [profileWeight,zeroExtendedPolynomialProfile,Set.indicator_of_notMem hmem]

theorem profileWeight_mul_zero_of_lt {η L : ℝ} (hL : 0 < L) (P : ℝ[X])
    {d n : ℕ} (hd : 1 ≤ d) (hn : ⌊Real.exp (L*η)⌋₊ < n) :
    profileWeight η L P (d*n) = 0 :=
  profileWeight_zero_of_lt hL P (hn.trans_le (Nat.le_mul_of_pos_left n hd))

theorem sum_weighted_af_mul (N : ℕ) (f g : ArithmeticFunction ℂ) (w : ℕ → ℂ)
    (hw : ∀ n, N < n → w n = 0) :
    (∑ a ∈ Finset.Icc 1 N, (f*g) a*w a) =
      ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, f d*g m*w (d*m) := by
  have hid : ∀ a, (f*g) a*w a = ∑ d ∈ a.divisors, f d*g (a/d)*w (d*(a/d)) := by
    intro a
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun x y => f x*g y),Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
  simp_rw [hid]
  exact sum_divisors_reindex N (fun d m => f d*g m*w (d*m))
    (fun d m h => by rw [hw (d*m) h,mul_zero])

theorem sum_bivariate_divisors_reindex (N : ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℂ)
    (hcut₁ : ∀ d n e m, N < d*n → F d n e m = 0)
    (hcut₂ : ∀ d n e m, N < e*m → F d n e m = 0) :
    (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
      ∑ d ∈ a.divisors, ∑ e ∈ b.divisors, F d (a/d) e (b/e)) =
      ∑ d ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        ∑ e ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, F d n e m := by
  calc
    _ = ∑ a ∈ Finset.Icc 1 N, ∑ d ∈ a.divisors,
        ∑ b ∈ Finset.Icc 1 N, ∑ e ∈ b.divisors, F d (a/d) e (b/e) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ a ∈ Finset.Icc 1 N, ∑ d ∈ a.divisors,
        ∑ e ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, F d (a/d) e m := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro d hd
      exact sum_divisors_reindex N (fun e m => F d (a/d) e m) (hcut₂ d (a/d))
    _ = _ := sum_divisors_reindex N
      (fun d n => ∑ e ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, F d n e m)
      (by
        intro d n h
        apply Finset.sum_eq_zero
        intro e he
        apply Finset.sum_eq_zero
        intro m hm
        exact hcut₁ d n e m h)

theorem sum_weighted_triple (N : ℕ) (s : Fin 4 → ℂ) (w : ℕ → ℂ)
    (hw : ∀ n, N < n → w n = 0) :
    (∑ a ∈ Finset.Icc 1 N, tripleCoeff s a*w a) =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, ∑ c ∈ Finset.Icc 1 N,
        powerAF (1+s 1) a*powerAF (1+s 2) b*powerAF (1+s 3) c*w (a*b*c) := by
  change (∑ a ∈ Finset.Icc 1 N,
    (powerAF (1+s 1)*(powerAF (1+s 2)*powerAF (1+s 3))) a*w a) = _
  rw [sum_weighted_af_mul N _ _ w hw]
  apply Finset.sum_congr rfl
  intro a ha
  have ha1 := (Finset.mem_Icc.mp ha).1
  have hwa : ∀ n, N < n → w (a*n) = 0 :=
    fun n hn => hw _ (hn.trans_le (Nat.le_mul_of_pos_left n ha1))
  have H := sum_weighted_af_mul N (powerAF (1+s 2)) (powerAF (1+s 3))
    (fun n => w (a*n)) hwa
  simp_rw [mul_assoc (powerAF (1+s 1) a)]
  rw [← Finset.mul_sum,H,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Nat.mul_assoc]

end
end SixthMoment.Source.NoDPHarmonic
