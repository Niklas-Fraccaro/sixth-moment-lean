import Sechstmoment.Numerator.U.Replacement.VStar.AFE

namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 1000000

def bblrVStarAFEProductSum (G : ℂ → ℂ) (α : MomentShifts) (t X : ℝ) : ℂ :=
  ∑ n∈bblrAFEProductBox X, bblrVStarAFESummand G α t n

def bblrVStarAFESpatialTail (G : ℂ → ℂ) (α : MomentShifts) (t X : ℝ) : ℂ :=
  ∑' n : Fin 4 → ℕ, if n∉bblrAFEProductBox X then bblrVStarAFESummand G α t n else 0

theorem bblrGaussianVStar_large_positive_line_norm_le (r : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ T : ℝ, ∀ σ : MomentShifts, ∀ t x : ℝ, 0≤t → 0<x →
      ‖bblrVStar (polarPoleKiller T σ) (x/t^2)‖≤
        C*polarGaussianConstant T σ (1+2*(r:ℝ))*(2+t)^(4*r+8)*x^(-(1+2*(r:ℝ))) := by
  let D : ℝ := gaussianTailConstant 48/(2*Real.pi)
  have hD : 0≤D := div_nonneg (gaussianTailConstant_nonneg 48) (by positivity)
  refine ⟨D,hD,?_⟩
  intro T σ t x ht hx
  by_cases ht₀ : t=0
  · subst t
    have hCG := polarGaussianConstant_nonneg T σ (1+2*(r:ℝ))
    have hb : 0≤D*polarGaussianConstant T σ (1+2*(r:ℝ))*(2+(0:ℝ))^(4*r+8)*x^(-(1+2*(r:ℝ))) := by positivity
    simpa [bblrVStar_zero] using hb
  · let c : ℝ := 1+2*(r:ℝ)
    have hc1 : 1≤c := by dsimp [c]; have hr : 0≤(r:ℝ) := Nat.cast_nonneg r; linarith
    have hc : 0<c := zero_lt_one.trans_le hc1
    have hCG := polarGaussianConstant_nonneg T σ c
    have he : (x/t^2)^(-c)=(t^2)^c*x^(-c) := by
      rw [Real.div_rpow hx.le (sq_nonneg t),Real.rpow_neg (sq_nonneg t),div_eq_mul_inv,inv_inv]
      ring
    have hpow : (t^2)^c≤(2+t)^(4*r+8) := by
      have hec : c=((1+2*r:ℕ):ℝ) := by dsimp [c]; push_cast; ring
      rw [hec,Real.rpow_natCast,←pow_mul]
      have hs : t^(2*(1+2*r))≤(2+t)^(2*(1+2*r)) :=
        pow_le_pow_left₀ ht (by linarith) _
      exact hs.trans (pow_le_pow_right₀ (by linarith : (1:ℝ)≤2+t) (by omega))
    have hv := bblrGaussianVStar_norm_le (div_pos hx (sq_pos_of_ne_zero ht₀)) hc T σ
    rw [he] at hv
    change ‖bblrVStar (polarPoleKiller T σ) (x/t^2)‖≤D*polarGaussianConstant T σ c*(2+t)^(4*r+8)*x^(-c)
    apply hv.trans
    have hd : D*polarGaussianConstant T σ c/c≤D*polarGaussianConstant T σ c :=
      div_le_self (mul_nonneg hD hCG) hc1
    have hp := mul_le_mul hd hpow (Real.rpow_nonneg (sq_nonneg t) c)
      (mul_nonneg hD hCG)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hx.le (-c))

theorem bblrVStarAFESpatialTail_absolute_norm_le (r : ℕ) (G : ℂ → ℂ) (α : MomentShifts)
    (hα : ∀ j, ‖α j‖≤1/4) (t : ℝ) {B X : ℝ} (hB : 0≤B) (hX : 0<X)
    (hV : ∀ x : ℝ, 0<x → ‖bblrVStar G (x/t^2)‖≤B*x^(-(1+2*(r:ℝ)))) :
    (∑' n : Fin 4 → ℕ, ‖if n∉bblrAFEProductBox X then bblrVStarAFESummand G α t n else 0‖)≤
      B*X^(-2*(r:ℝ))*(∑' n : Fin 4 → ℕ, bblrGaussianAFEQuadMajorant n) := by
  have hcoef : 0≤B*X^(-2*(r:ℝ)) := by positivity
  have hpoint (n : Fin 4 → ℕ) :
      ‖if n∉bblrAFEProductBox X then bblrVStarAFESummand G α t n else 0‖≤
        (B*X^(-2*(r:ℝ)))*bblrGaussianAFEQuadMajorant n := by
    by_cases hn : n∉bblrAFEProductBox X
    · simp only [ite_eq_left hn]
      have hx : X<(positiveQuadProduct n : ℝ) := by
        exact lt_of_not_ge (fun h => hn ((bblrAFEProductBox_mem_iff X n).mpr h))
      have hp : (positiveQuadProduct n : ℝ)^(-2*(r:ℝ))≤X^(-2*(r:ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hX hx.le (by have hr : 0≤(r:ℝ) := Nat.cast_nonneg r; linarith)
      exact (bblrVStarAFESummand_large_line_norm_le r G α hα t hB hV n).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hB)
          (bblrGaussianAFEQuadMajorant_nonneg n))
    · simp only [ite_eq_right hn,norm_zero]
      exact mul_nonneg hcoef (bblrGaussianAFEQuadMajorant_nonneg n)
  have hs := bblrGaussianAFEQuadMajorant_summable.mul_left (B*X^(-2*(r:ℝ)))
  have hf := hs.of_norm_bounded hpoint
  calc
    _ ≤ ∑' n : Fin 4 → ℕ, (B*X^(-2*(r:ℝ)))*bblrGaussianAFEQuadMajorant n :=
      hf.norm.tsum_le_tsum hpoint hs
    _ = _ := tsum_mul_left

theorem bblrVStarAFESpatialTail_norm_le (r : ℕ) (G : ℂ → ℂ) (α : MomentShifts)
    (hα : ∀ j, ‖α j‖≤1/4) (t : ℝ) {B X : ℝ} (hB : 0≤B) (hX : 0<X)
    (hV : ∀ x : ℝ, 0<x → ‖bblrVStar G (x/t^2)‖≤B*x^(-(1+2*(r:ℝ)))) :
    ‖bblrVStarAFESpatialTail G α t X‖≤
      B*X^(-2*(r:ℝ))*(∑' n : Fin 4 → ℕ, bblrGaussianAFEQuadMajorant n) := by
  have hcoef : 0≤B*X^(-2*(r:ℝ)) := by positivity
  have hpoint (n : Fin 4 → ℕ) :
      ‖if n∉bblrAFEProductBox X then bblrVStarAFESummand G α t n else 0‖≤
        (B*X^(-2*(r:ℝ)))*bblrGaussianAFEQuadMajorant n := by
    by_cases hn : n∉bblrAFEProductBox X
    · simp only [ite_eq_left hn]
      have hx : X<(positiveQuadProduct n : ℝ) := by
        exact lt_of_not_ge (fun h => hn ((bblrAFEProductBox_mem_iff X n).mpr h))
      have hp : (positiveQuadProduct n : ℝ)^(-2*(r:ℝ))≤X^(-2*(r:ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hX hx.le (by have hr : 0≤(r:ℝ) := Nat.cast_nonneg r; linarith)
      exact (bblrVStarAFESummand_large_line_norm_le r G α hα t hB hV n).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hB)
          (bblrGaussianAFEQuadMajorant_nonneg n))
    · simp only [ite_eq_right hn,norm_zero]
      exact mul_nonneg hcoef (bblrGaussianAFEQuadMajorant_nonneg n)
  have hs := bblrGaussianAFEQuadMajorant_summable.mul_left (B*X^(-2*(r:ℝ)))
  have hf := hs.of_norm_bounded hpoint
  unfold bblrVStarAFESpatialTail
  calc
    _ ≤ ∑' n : Fin 4 → ℕ, ‖if n∉bblrAFEProductBox X then bblrVStarAFESummand G α t n else 0‖ :=
      norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' n : Fin 4 → ℕ, (B*X^(-2*(r:ℝ)))*bblrGaussianAFEQuadMajorant n :=
      hf.norm.tsum_le_tsum hpoint hs
    _ = _ := tsum_mul_left

theorem bblrGaussianVStarAFESpatialTail_uniform_absolute_power_bound (K : Set MomentShifts)
    (δ : ℝ) (hδ : 0<δ)
    (hρ : ∀ σ∈K, ∀ k : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ k‖)
    {ε : ℝ} (hε : 0<ε) (N : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ α : MomentShifts,
      (∀ j, ‖α j‖≤1/4) → ∀ t∈Icc T (2*T),
      (∑' n : Fin 4 → ℕ, ‖if n∉bblrAFEProductBox (T^(2+ε))
        then bblrVStarAFESummand (polarPoleKiller T σ) α t n else 0‖)≤C*T^(-N) := by
  obtain ⟨r,hr⟩ := exists_nat_gt (max 0 ((N+9)/(2*ε)))
  have hrN : N+9<2*(r:ℝ)*ε := by
    have h := (le_max_right (0:ℝ) _).trans_lt hr
    rw [div_lt_iff₀ (by positivity : 0<2*ε)] at h
    nlinarith
  obtain ⟨D,hD,hV⟩ := bblrGaussianVStar_large_positive_line_norm_le r
  let c : ℝ := 1+2*(r:ℝ)
  let E : ℝ := Real.exp (c^2)*(1+|c|)^48*(1+1/δ^2)^24
  let J : ℝ := ∑' n : Fin 4 → ℕ, bblrGaussianAFEQuadMajorant n
  have hE : 0≤E := by dsimp [E]; positivity
  have hJ : 0≤J := tsum_nonneg bblrGaussianAFEQuadMajorant_nonneg
  have hlog : ∀ᶠ T : ℝ in atTop, (Real.log T)^48≤T := by
    have h := (log_pow_isLittleO_rpow 48 (δ := 1) zero_lt_one).bound zero_lt_one
    filter_upwards [h,eventually_gt_atTop (1:ℝ)] with T hT hpos
    simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_pos (zero_lt_one.trans hpos),
      abs_of_nonneg (by positivity : 0≤(Real.log T)^48),one_mul] using hT
  refine ⟨D*E*4^(4*r+8)*J,by positivity,?_⟩
  filter_upwards [hlog,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hlog hT hL
  intro σ hσ α hα t ht
  have hTpos : 0<T := zero_lt_one.trans hT
  have htpos : 0≤t := by linarith [ht.1]
  have hCG := polarGaussianConstant_nonneg T σ c
  have hCGb : polarGaussianConstant T σ c≤E*T :=
    (Sechstmoment.polarGaussianConstant_log_growth hT hL hδ σ c (hρ σ hσ)).trans
      (mul_le_mul_of_nonneg_left hlog hE)
  have htime : (2+t)^(4*r+8)≤4^(4*r+8)*T^(4*r+8) := by
    rw [← mul_pow]
    gcongr
    all_goals linarith [ht.1,ht.2]
  have hb := bblrVStarAFESpatialTail_absolute_norm_le r (polarPoleKiller T σ) α hα t
    (B := D*polarGaussianConstant T σ c*(2+t)^(4*r+8)) (by positivity)
    (Real.rpow_pos_of_pos hTpos (2+ε))
    (fun x hx => hV T σ t x (by linarith [ht.1]) hx)
  calc
    _ ≤ D*(E*T)*(4^(4*r+8)*T^(4*r+8))*(T^(2+ε))^(-2*(r:ℝ))*J := by
      apply hb.trans
      gcongr
    _ = (D*E*4^(4*r+8)*J)*T^(9-2*(r:ℝ)*ε) := by
      rw [← Real.rpow_mul hTpos.le,← Real.rpow_natCast T (4*r+8)]
      have hp : T*T^((4*r+8:ℕ):ℝ)*T^((2+ε)*(-2*(r:ℝ)))=T^(9-2*(r:ℝ)*ε) := by
        conv_lhs => arg 1; arg 1; rw [← Real.rpow_one T]
        rw [← Real.rpow_add hTpos,← Real.rpow_add hTpos]
        congr 1
        push_cast
        ring
      calc
        _ = (D*E*4^(4*r+8)*J)*(T*T^((4*r+8:ℕ):ℝ)*T^((2+ε)*(-2*(r:ℝ)))) := by ring
        _ = _ := by rw [hp]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT.le (by linarith)) (by positivity)
theorem bblrGaussianVStarAFESpatialTail_uniform_power_bound (K : Set MomentShifts)
    (δ : ℝ) (hδ : 0<δ)
    (hρ : ∀ σ∈K, ∀ k : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ k‖)
    {ε : ℝ} (hε : 0<ε) (N : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ α : MomentShifts,
      (∀ j, ‖α j‖≤1/4) → ∀ t∈Icc T (2*T),
      ‖bblrVStarAFESpatialTail (polarPoleKiller T σ) α t (T^(2+ε))‖≤C*T^(-N) := by
  obtain ⟨C,hC,hb⟩ := bblrGaussianVStarAFESpatialTail_uniform_absolute_power_bound K δ hδ hρ hε N
  refine ⟨C,hC,?_⟩
  filter_upwards [hb] with T hb
  intro σ hσ α hα t ht
  have hs := bblrGaussianVStarAFE_summable T σ α hα t
  have ho : Summable (fun n : Fin 4 → ℕ => if n∉bblrAFEProductBox (T^(2+ε))
      then bblrVStarAFESummand (polarPoleKiller T σ) α t n else 0) := by
    apply hs.norm.of_norm_bounded
    intro n
    by_cases hn : n∉bblrAFEProductBox (T^(2+ε)) <;> simp [hn]
  unfold bblrVStarAFESpatialTail
  exact (norm_tsum_le_tsum_norm ho.norm).trans (hb σ hσ α hα t ht)


end
end Sechstmoment
