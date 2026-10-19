import Sechstmoment.Arithmetic.Divisors.Subpower
import Sechstmoment.Numerator.U.ZeroModes.Ratio.EtaAnalytic

/-! Genuine uniform subpower bounds for both ratio-contour eta factors.
All imaginary parts are unrestricted. The bound is proved from the actual
divisor sum and a fixed cost at each distinct prime. -/

namespace Sechstmoment.Source
open Complex Real Nat Set
open scoped BigOperators
open Classical
noncomputable section
set_option maxHeartbeats 0

theorem a03PrimeNegativeCpow_norm_le_one {p : ℕ} (hp : p.Prime)
    {z : ℂ} (hz : 0≤z.re) : ‖(p:ℂ)^(-z)‖≤1 := by
  rw [Complex.norm_natCast_cpow_of_pos hp.pos,Complex.neg_re]
  calc
    _ ≤ (p:ℝ)^0 := Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hp.one_lt.le) (by linarith)
    _ = 1 := Real.rpow_zero _

theorem a03PrimeNegativeCpow_norm_le_half {p : ℕ} (hp : p.Prime)
    {z : ℂ} (hz : 1≤z.re) : ‖(p:ℂ)^(-z)‖≤1/2 := by
  rw [Complex.norm_natCast_cpow_of_pos hp.pos,Complex.neg_re]
  calc
    _ ≤ (p:ℝ)^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hp.one_lt.le) (by linarith)
    _ = (p:ℝ)⁻¹ := Real.rpow_neg_one _
    _ ≤ 1/2 := by
      rw [←one_div]
      exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp.two_le)

theorem bblrEtaCorrection_norm_le_eight {p : ℕ} (hp : p.Prime)
    {x y z : ℂ} (hx : 0≤(1+x).re) (hy : 0≤(1+y).re)
    (hz : 1≤(2+z).re) : ‖bblrEtaCorrection p x y z‖≤8 := by
  have hX := a03PrimeNegativeCpow_norm_le_one hp hx
  have hY := a03PrimeNegativeCpow_norm_le_one hp hy
  have hZ := a03PrimeNegativeCpow_norm_le_half hp hz
  have hnX : ‖1-(p:ℂ)^(-(1+x))‖≤2 := by
    apply (norm_sub_le _ _).trans
    rw [norm_one]
    linarith
  have hnY : ‖1-(p:ℂ)^(-(1+y))‖≤2 := by
    apply (norm_sub_le _ _).trans
    rw [norm_one]
    linarith
  have hnZ : (1/2:ℝ)≤‖1-(p:ℂ)^(-(2+z))‖ := by
    have h := norm_sub_norm_le (1:ℂ) ((p:ℂ)^(-(2+z)))
    simp only [norm_one] at h
    linarith
  unfold bblrEtaCorrection
  rw [norm_div,norm_mul]
  calc
    _ ≤ (2:ℝ)*2/(1/2) := by gcongr
    _ = 8 := by norm_num

theorem bblrEtaArithmetic_norm_le_divisor_prime_cost (α β γ δ u v s : ℂ)
    {n : ℕ} (hn : n≠0)
    (hL : 0≤(γ-δ+2*v+s).re)
    (hX : 0≤(1+(α-β+γ-δ+2*u+2*v+s)).re)
    (hY : 0≤(1+(γ-δ+2*v)).re)
    (hZ : 1≤(2+(α-β+γ-δ+2*u+2*v)).re) :
    ‖bblrEtaArithmetic α β γ δ u v s n‖≤
      (n.divisors.card:ℝ)*(8:ℝ)^n.primeFactors.card := by
  rw [bblrEtaArithmetic_apply α β γ δ u v s hn]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _l∈n.divisors,(8:ℝ)^n.primeFactors.card := by
      apply Finset.sum_le_sum
      intro l hl
      rw [norm_mul]
      have hln : ‖(l:ℂ)^(-(γ-δ+2*v+s))‖≤1 := by
        rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_mem_divisors hl),Complex.neg_re]
        calc
          _ ≤ (l:ℝ)^0 := Real.rpow_le_rpow_of_exponent_le
            (by exact_mod_cast Nat.pos_of_mem_divisors hl) (by linarith)
          _ = 1 := Real.rpow_zero _
      have hp : ‖∏ p∈(n/l).primeFactors,bblrEtaCorrection p
          (α-β+γ-δ+2*u+2*v+s) (γ-δ+2*v) (α-β+γ-δ+2*u+2*v)‖≤
            (8:ℝ)^n.primeFactors.card := by
        calc
          _ ≤ ∏ p∈(n/l).primeFactors,‖bblrEtaCorrection p
              (α-β+γ-δ+2*u+2*v+s) (γ-δ+2*v) (α-β+γ-δ+2*u+2*v)‖ :=
            Finset.norm_prod_le _ _
          _ ≤ ∏ _p∈(n/l).primeFactors,(8:ℝ) := Finset.prod_le_prod₀
            (fun _ _ => norm_nonneg _) (fun p hp =>
              bblrEtaCorrection_norm_le_eight (Nat.prime_of_mem_primeFactors hp) hX hY hZ)
          _ = (8:ℝ)^(n/l).primeFactors.card := by simp
          _ ≤ (8:ℝ)^n.primeFactors.card := pow_le_pow_right₀ (by norm_num)
            (Finset.card_le_card (Nat.primeFactors_mono
              (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hl)) hn))
      exact (mul_le_mul hln hp (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
    _ = _ := by simp

/-- Uniform eta subpower decay, in the genuine domain visited by the
initial, jointly shifted, and single-residue secondary u/v lines. -/
theorem bblrEtaArithmetic_ratio_subpower_bound {ε : ℝ} (hε : 0<ε) :
    ∃ D : ℝ,0≤D ∧ ∀ α β γ δ u v s : ℂ, ∀ n : ℕ,n≠0 →
      1≤s.re → 0≤(1+γ-δ+2*v).re →
      1≤(2+α-β+γ-δ+2*u+2*v).re →
      ‖bblrEtaArithmetic α β γ δ u v s n‖≤D*(n:ℝ)^ε := by
  obtain ⟨D,hD,hb⟩ := Sechstmoment.divisor_prime_cost_subpower hε (by norm_num : (1:ℝ)≤8)
  refine ⟨D,hD,?_⟩
  intro α β γ δ u v s n hn hs hy hz
  apply (bblrEtaArithmetic_norm_le_divisor_prime_cost α β γ δ u v s hn ?_ ?_ ?_ ?_).trans
    (hb n hn)
  · simp only [add_re,sub_re,one_re] at hy ⊢
    linarith
  · have he : 1+(α-β+γ-δ+2*u+2*v+s)=
        (2+α-β+γ-δ+2*u+2*v)-1+s := by ring
    rw [he]
    simp only [add_re,sub_re,one_re] at hz ⊢
    linarith
  · convert hy using 1
    congr 1
    ring
  · convert hz using 1
    congr 1
    ring

theorem a03ZeroModeRatioEtaPair_subpower_bound {ε : ℝ} (hε : 0<ε) :
    ∃ D : ℝ,0≤D ∧ ∀ α : MomentShifts,∀ a b : ℕ,a≠0 → b≠0 →
      ∀ u v s : ℂ,1≤s.re →
      0≤(a03ZeroModeRatioDifferenceArgument α 0 u).re →
      0≤(a03ZeroModeRatioDifferenceArgument α 1 v).re →
      1≤(a03ZeroModeRatioEulerArgument α u v).re →
      ‖a03ZeroModeRatioEtaPair α a b u v s‖≤D*(a:ℝ)^ε*(b:ℝ)^ε := by
  obtain ⟨D,hD,hb⟩ := bblrEtaArithmetic_ratio_subpower_bound hε
  refine ⟨D^2,by positivity,?_⟩
  intro α a b ha hb0 u v s hs hu hv hA
  have ha' := hb (α 0) (α 1) (α 2) (α 3) u v s a ha hs
    (by simpa only [a03ZeroModeRatioDifferenceArgument_one] using hv) hA
  have hb' := hb (α 2) (α 3) (α 0) (α 1) v u s b hb0 hs
    (by simpa only [a03ZeroModeRatioDifferenceArgument_zero] using hu)
    (by convert hA using 1; unfold a03ZeroModeRatioEulerArgument; congr 1; ring)
  unfold a03ZeroModeRatioEtaPair
  rw [norm_mul]
  calc
    _ ≤ (D*(a:ℝ)^ε)*(D*(b:ℝ)^ε) := by gcongr
    _ = _ := by ring

end
end Sechstmoment.Source
