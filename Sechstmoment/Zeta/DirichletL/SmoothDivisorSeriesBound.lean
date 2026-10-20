import Sechstmoment.Arithmetic.Divisors.Subpower
import Sechstmoment.Zeta.DirichletL.WeightedCharSeries
import Sechstmoment.Zeta.DirichletL.Weights.Bounds


namespace Sechstmoment.Source
open Complex Real MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section

def dirichletSmoothCoefficients (N : ℕ) (s : ℂ) (a n : ℕ) : ℂ :=
  LSeries.term (fun k : ℕ => (k.divisors.card : ℂ)) s n *
    squareSmoothWeight s a (Real.pi*(n : ℝ)/(N : ℝ))

theorem dirichletSmoothCoefficients_zero (N : ℕ) (s : ℂ) (a : ℕ) :
    dirichletSmoothCoefficients N s a 0 = 0 := by simp [dirichletSmoothCoefficients]

theorem dirichletSmoothCoefficients_norm {N a n : ℕ} (s : ℂ) (hn : n ≠ 0) :
    ‖dirichletSmoothCoefficients N s a n‖ =
      (n.divisors.card : ℝ)/(n : ℝ)^s.re *
        ‖squareSmoothWeight s a (Real.pi*(n : ℝ)/(N : ℝ))‖ := by
  rw [dirichletSmoothCoefficients, norm_mul, LSeries.norm_term_eq, ite_eq_right hn]
  simp only [Complex.norm_natCast]

theorem dirichletSmoothCoefficients_norm_majorant {θ : ℝ} (hθ : 0 < θ) :
    ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, 0 < N → ∀ s : ℂ,
      s.re ∈ Icc (1/4 : ℝ) (3/4) → ∀ a : ℕ, a ≤ 1 →
      ∀ n : ℕ, 0 < n → ∀ δ : ℝ, δ ∈ Icc (0 : ℝ) 1 →
      ((n/N : ℕ)+1 : ℝ)*‖dirichletSmoothCoefficients N s a n‖ ≤
        A*(1+|s.im|)^6*(N : ℝ)^δ*(n : ℝ)^(θ-s.re-δ) := by
  obtain ⟨D,hD,hdiv⟩ := divisor_prime_cost_subpower hθ (by norm_num : (1 : ℝ) ≤ 1)
  obtain ⟨C,hC,hweight⟩ := squareSmoothWeight_scaled_bound
  refine ⟨(D+1)*C, by positivity, ?_⟩
  intro N hN s hs a ha n hn δ hδ
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hdn : (n.divisors.card : ℝ) ≤ (D+1)*(n : ℝ)^θ := by
    have h := hdiv n hn.ne'
    simp only [one_pow, mul_one] at h
    exact h.trans (by gcongr; linarith)
  have hw := hweight N hN s hs a ha n hn δ hδ
  rw [dirichletSmoothCoefficients_norm s hn.ne']
  calc
    _ = ((n.divisors.card : ℝ)/(n : ℝ)^s.re)*
        (((n/N : ℕ)+1 : ℝ)*‖squareSmoothWeight s a (Real.pi*(n : ℝ)/(N : ℝ))‖) := by ring
    _ ≤ (((D+1)*(n : ℝ)^θ)/(n : ℝ)^s.re)*
        (C*(1+|s.im|)^6*(N : ℝ)^δ/(n : ℝ)^δ) := by gcongr
    _ = _ := by
      rw [Real.rpow_sub hn', Real.rpow_sub hn']
      ring

theorem dirichletSmoothCoefficients_summable (N : ℕ) (hN : 0 < N)
    (s : ℂ) (hs : s.re ∈ Icc (1/4 : ℝ) (3/4)) (a : ℕ) (ha : a ≤ 1) :
    Summable (dirichletSmoothCoefficients N s a) := by
  obtain ⟨A,hA,hbound⟩ := dirichletSmoothCoefficients_norm_majorant (θ := 1/8) (by norm_num)
  have hseries : Summable (fun n : ℕ => (n : ℝ)^(-9/8 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  apply Summable.of_norm
  apply (hseries.mul_left (A*(1+|s.im|)^6*(N : ℝ))).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  by_cases hn : n = 0
  · rw [hn,dirichletSmoothCoefficients_zero,norm_zero]
    positivity
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    have h := hbound N hN s hs a ha n hn' 1 (by norm_num)
    rw [Real.rpow_one] at h
    have ht : 1 ≤ ((n/N : ℕ)+1 : ℝ) := le_add_of_nonneg_left (Nat.cast_nonneg _)
    calc
      _ ≤ ((n/N : ℕ)+1 : ℝ)*‖dirichletSmoothCoefficients N s a n‖ :=
        le_mul_of_one_le_left (norm_nonneg _) ht
      _ ≤ A*(1+|s.im|)^6*(N : ℝ)*(n : ℝ)^(1/8-s.re-1) := h
      _ ≤ _ := by
        gcongr
        · exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
        · linarith [hs.1]

theorem dirichletSmoothCoefficients_weighted_l2 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ s : ℂ,
      s.re ∈ Icc (1/4 : ℝ) (3/4) → ∀ a : ℕ, a ≤ 1 →
      ∀ δ : ℝ, δ ∈ Icc (0 : ℝ) 1 → 1/2+ε ≤ s.re+δ →
      Summable (fun n : ℕ => ((n/N : ℕ)+1 : ℝ)^2*‖dirichletSmoothCoefficients N s a n‖^2) ∧
      (∑' n : ℕ, ((n/N : ℕ)+1 : ℝ)^2*‖dirichletSmoothCoefficients N s a n‖^2) ≤
        C*(1+|s.im|)^12*(N : ℝ)^(2*δ) := by
  obtain ⟨A,hA,hbound⟩ := dirichletSmoothCoefficients_norm_majorant (θ := ε/2) (by linarith)
  let p : ℕ → ℝ := fun n => (n : ℝ)^(-1-ε)
  have hp : Summable p := Real.summable_nat_rpow.mpr (by linarith)
  have hp0 : 0 ≤ ∑' n, p n := tsum_nonneg (fun _ => by dsimp [p]; positivity)
  refine ⟨A^2*((∑' n, p n)+1), by positivity, ?_⟩
  intro N hN s hs a ha δ hδ hsd
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  let B : ℝ := A^2*(1+|s.im|)^12*(N : ℝ)^(2*δ)
  have hpoint (n : ℕ) :
      ((n/N : ℕ)+1 : ℝ)^2*‖dirichletSmoothCoefficients N s a n‖^2 ≤ B*p n := by
    by_cases hn : n = 0
    · rw [hn,dirichletSmoothCoefficients_zero,norm_zero]
      simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
      dsimp [B,p]
      positivity
    · have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have h := hbound N hN s hs a ha n (Nat.pos_of_ne_zero hn) δ hδ
      have hexp : ((N : ℝ)^δ)^2 = (N : ℝ)^(2*δ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN'.le]
        congr 1
        ring
      have hnexp : ((n : ℝ)^(ε/2-s.re-δ))^2 = (n : ℝ)^((ε/2-s.re-δ)*2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn'.le]
        norm_num
      calc
        _ = (((n/N : ℕ)+1 : ℝ)*‖dirichletSmoothCoefficients N s a n‖)^2 := by ring
        _ ≤ (A*(1+|s.im|)^6*(N : ℝ)^δ*(n : ℝ)^(ε/2-s.re-δ))^2 := by gcongr
        _ = B*(n : ℝ)^((ε/2-s.re-δ)*2) := by
          rw [mul_pow, mul_pow, mul_pow, hexp, hnexp]
          dsimp only [B]
          ring
        _ ≤ B*p n := by
          dsimp only [p]
          gcongr
          · exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
          · linarith
  have hsum := (hp.mul_left B).of_nonneg_of_le (fun _ => by positivity) hpoint
  refine ⟨hsum, ?_⟩
  calc
    _ ≤ ∑' n, B*p n := hsum.tsum_le_tsum hpoint (hp.mul_left B)
    _ = B*(∑' n, p n) := tsum_mul_left
    _ ≤ B*((∑' n, p n)+1) := by gcongr; linarith
    _ = _ := by dsimp [B]; ring

end
end Sechstmoment.Source
