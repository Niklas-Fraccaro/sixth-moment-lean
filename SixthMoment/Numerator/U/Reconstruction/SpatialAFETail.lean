import SixthMoment.Numerator.Polar.GaussianLogGrowth
import SixthMoment.Numerator.U.Reconstruction.RectangularAFEInterchange
import SixthMoment.Numerator.U.Separation.LogarithmicGaussianTail
import SixthMoment.Numerator.U.Separation.PositiveVContour


namespace SixthMoment.Source
open Complex Real MeasureTheory Filter Set
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 1000000

def bblrAFEProductBox (X : ℝ) : Finset (Fin 4 → ℕ) :=
  (Fintype.piFinset (fun _ : Fin 4 => Finset.range ⌊X⌋₊)).filter
    (fun n => (positiveQuadProduct n : ℝ)≤X)

theorem bblrAFEProductBox_mem_iff (X : ℝ) (n : Fin 4 → ℕ) :
    n∈bblrAFEProductBox X ↔ (positiveQuadProduct n : ℝ)≤X := by
  constructor
  · exact fun hn => (Finset.mem_filter.mp hn).2
  · intro hx
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr (fun j => Finset.mem_range.mpr ?_),hx⟩
    have hn : (n j+1 : ℝ)≤(positiveQuadProduct n : ℝ) := by
      rw [positiveQuadProduct_eq_prod]
      exact_mod_cast Finset.single_le_prod
        (s := Finset.univ) (f := fun i : Fin 4 => n i+1)
        (fun i _ => by omega) (Finset.mem_univ j)
    have hf := Nat.lt_floor_add_one X
    have hlt : (n j : ℝ)<(⌊X⌋₊ : ℝ) := by linarith
    exact_mod_cast hlt

def bblrAFEProductSum (G : ℂ → ℂ) (α : MomentShifts) (t X : ℝ) : ℂ :=
  ∑ n∈bblrAFEProductBox X, bblrAFESummand G α t n

def bblrAFESpatialTail (G : ℂ → ℂ) (α : MomentShifts) (t X : ℝ) : ℂ :=
  ∑' n : Fin 4 → ℕ, if n∉bblrAFEProductBox X then bblrAFESummand G α t n else 0

theorem bblrAFESum_product_add_spatial_tail (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (hα : ∀ j, -1/2<(α j).re) (t X : ℝ) :
    bblrAFESum G α t = bblrAFEProductSum G α t X+bblrAFESpatialTail G α t X := by
  have hs := SixthMoment.rectangular_actual_AFE_summable G α hG t hα
  have hi : Summable (fun n : Fin 4 → ℕ => if n∈bblrAFEProductBox X then bblrAFESummand G α t n else 0) := by
    apply hs.norm.of_norm_bounded
    intro n
    by_cases hn : n∈bblrAFEProductBox X <;> simp [hn]
  have ho : Summable (fun n : Fin 4 → ℕ => if n∉bblrAFEProductBox X then bblrAFESummand G α t n else 0) := by
    apply hs.norm.of_norm_bounded
    intro n
    by_cases hn : n∈bblrAFEProductBox X <;> simp [hn]
  have he : (∑' n : Fin 4 → ℕ, if n∈bblrAFEProductBox X then bblrAFESummand G α t n else 0) =
      bblrAFEProductSum G α t X := by
    unfold bblrAFEProductSum
    rw [tsum_eq_sum (s := bblrAFEProductBox X) (fun n hn => by simp [hn])]
    exact Finset.sum_congr rfl (fun n hn => by simp [hn])
  rw [← he,bblrAFESpatialTail,← hi.tsum_add ho]
  unfold bblrAFESum
  apply tsum_congr
  intro n
  by_cases hn : n∈bblrAFEProductBox X <;> simp [hn]

theorem bblrAFESpatialTail_time_stronglyMeasurable (G : ℂ → ℂ) (hG : Continuous G)
    (α : MomentShifts) (hα : ∀ j, -1/2<(α j).re) (X : ℝ) :
    StronglyMeasurable (fun t : ℝ => bblrAFESpatialTail G α t X) := by
  apply StronglyMeasurable.tsum
  intro n
  by_cases hn : n∉bblrAFEProductBox X
  · simpa only [ite_eq_left hn] using
      SixthMoment.rectangular_actual_AFE_summand_stronglyMeasurable G hG α hα n
  · simp only [ite_eq_right hn]
    exact stronglyMeasurable_const

theorem bblrAFESummand_large_line_norm_le (r : ℕ) (G : ℂ → ℂ) (α : MomentShifts)
    (hα : ∀ j, ‖α j‖≤1/4) (t : ℝ) {B : ℝ} (hB : 0≤B)
    (hV : ∀ x : ℝ, 0<x → ‖bblrV G α x t‖≤B*x^(-(1+2*(r:ℝ))))
    (n : Fin 4 → ℕ) :
    ‖bblrAFESummand G α t n‖≤
      (B*(positiveQuadProduct n : ℝ)^(-2*(r:ℝ)))*bblrGaussianAFEQuadMajorant n := by
  have hn (j : Fin 4) : 0<(n j+1 : ℝ) := by positivity
  have hx : 0<(positiveQuadProduct n : ℝ) := by unfold positiveQuadProduct; positivity
  have hden : 0<∏ j : Fin 4, (n j+1 : ℝ)^(1/2+(α j).re) :=
    Finset.prod_pos (fun j _ => Real.rpow_pos_of_pos (hn j) _)
  have he : ∏ j : Fin 4, (n j+1 : ℝ)^(3/2+(α j).re) =
      (positiveQuadProduct n : ℝ)*∏ j : Fin 4, (n j+1 : ℝ)^(1/2+(α j).re) := by
    have he' (j : Fin 4) : (n j+1 : ℝ)^(3/2+(α j).re) =
        (n j+1 : ℝ)*(n j+1 : ℝ)^(1/2+(α j).re) := by
      rw [show (3/2:ℝ)+(α j).re=1+(1/2+(α j).re) by ring,
        Real.rpow_add (hn j),Real.rpow_one]
    simp_rw [he']
    rw [Finset.prod_mul_distrib,positiveQuadProduct_eq_prod]
    push_cast
    rfl
  have hcp (j : Fin 4) : ‖(n j+1 : ℂ)^(1/2+α j)‖=(n j+1 : ℝ)^(1/2+(α j).re) := by
    rw [show (n j+1 : ℂ)=((n j+1 : ℝ):ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (hn j)]
    congr 1
    simp
  have hp (j : Fin 4) : 1/(n j+1 : ℝ)^(3/2+(α j).re)≤1/(n j+1 : ℝ)^(5/4:ℝ) := by
    have har := (abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))).1
    apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos (hn j) _)
    exact Real.rpow_le_rpow_of_exponent_le (by norm_cast; omega) (by linarith)
  have hpow : (positiveQuadProduct n : ℝ)^(-(1+2*(r:ℝ))) =
      (positiveQuadProduct n : ℝ)^(-2*(r:ℝ))/(positiveQuadProduct n : ℝ) := by
    rw [show -(1+2*(r:ℝ))=(-2*(r:ℝ))-1 by ring,Real.rpow_sub hx,Real.rpow_one]
  unfold bblrAFESummand
  rw [norm_div,norm_mul,bblrAFE_oscillation_norm_one,one_mul,norm_prod]
  simp_rw [hcp]
  calc
    _ ≤ (B*((positiveQuadProduct n : ℝ)^(-2*(r:ℝ))/(positiveQuadProduct n : ℝ)))/
        (∏ j : Fin 4, (n j+1 : ℝ)^(1/2+(α j).re)) := by
      rw [← hpow]
      exact div_le_div_of_nonneg_right (hV _ hx) hden.le
    _ = (B*(positiveQuadProduct n : ℝ)^(-2*(r:ℝ)))*
        ∏ j : Fin 4, 1/(n j+1 : ℝ)^(3/2+(α j).re) := by
      rw [Finset.prod_div_distrib,Finset.prod_const_one,he]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun j _ => hp j)) (by positivity)

theorem bblrAFESpatialTail_absolute_norm_le (r : ℕ) (G : ℂ → ℂ) (α : MomentShifts)
    (hα : ∀ j, ‖α j‖≤1/4) (t : ℝ) {B X : ℝ} (hB : 0≤B) (hX : 0<X)
    (hV : ∀ x : ℝ, 0<x → ‖bblrV G α x t‖≤B*x^(-(1+2*(r:ℝ)))) :
    (∑' n : Fin 4 → ℕ, ‖if n∉bblrAFEProductBox X then bblrAFESummand G α t n else 0‖)≤
      B*X^(-2*(r:ℝ))*(∑' n : Fin 4 → ℕ, bblrGaussianAFEQuadMajorant n) := by
  have hcoef : 0≤B*X^(-2*(r:ℝ)) := by positivity
  have hpoint (n : Fin 4 → ℕ) :
      ‖if n∉bblrAFEProductBox X then bblrAFESummand G α t n else 0‖≤
        (B*X^(-2*(r:ℝ)))*bblrGaussianAFEQuadMajorant n := by
    by_cases hn : n∉bblrAFEProductBox X
    · simp only [ite_eq_left hn]
      have hx : X<(positiveQuadProduct n : ℝ) := by
        exact lt_of_not_ge (fun h => hn ((bblrAFEProductBox_mem_iff X n).mpr h))
      have hp : (positiveQuadProduct n : ℝ)^(-2*(r:ℝ))≤X^(-2*(r:ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hX hx.le (by have hr : 0≤(r:ℝ) := Nat.cast_nonneg r; linarith)
      exact (bblrAFESummand_large_line_norm_le r G α hα t hB hV n).trans
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

theorem bblrAFESpatialTail_norm_le (r : ℕ) (G : ℂ → ℂ) (α : MomentShifts)
    (hα : ∀ j, ‖α j‖≤1/4) (t : ℝ) {B X : ℝ} (hB : 0≤B) (hX : 0<X)
    (hV : ∀ x : ℝ, 0<x → ‖bblrV G α x t‖≤B*x^(-(1+2*(r:ℝ)))) :
    ‖bblrAFESpatialTail G α t X‖≤
      B*X^(-2*(r:ℝ))*(∑' n : Fin 4 → ℕ, bblrGaussianAFEQuadMajorant n) := by
  have hcoef : 0≤B*X^(-2*(r:ℝ)) := by positivity
  have hpoint (n : Fin 4 → ℕ) :
      ‖if n∉bblrAFEProductBox X then bblrAFESummand G α t n else 0‖≤
        (B*X^(-2*(r:ℝ)))*bblrGaussianAFEQuadMajorant n := by
    by_cases hn : n∉bblrAFEProductBox X
    · simp only [ite_eq_left hn]
      have hx : X<(positiveQuadProduct n : ℝ) := by
        exact lt_of_not_ge (fun h => hn ((bblrAFEProductBox_mem_iff X n).mpr h))
      have hp : (positiveQuadProduct n : ℝ)^(-2*(r:ℝ))≤X^(-2*(r:ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hX hx.le (by have hr : 0≤(r:ℝ) := Nat.cast_nonneg r; linarith)
      exact (bblrAFESummand_large_line_norm_le r G α hα t hB hV n).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hB)
          (bblrGaussianAFEQuadMajorant_nonneg n))
    · simp only [ite_eq_right hn,norm_zero]
      exact mul_nonneg hcoef (bblrGaussianAFEQuadMajorant_nonneg n)
  have hs := bblrGaussianAFEQuadMajorant_summable.mul_left (B*X^(-2*(r:ℝ)))
  have hf := hs.of_norm_bounded hpoint
  unfold bblrAFESpatialTail
  calc
    _ ≤ ∑' n : Fin 4 → ℕ, ‖if n∉bblrAFEProductBox X then bblrAFESummand G α t n else 0‖ :=
      norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' n : Fin 4 → ℕ, (B*X^(-2*(r:ℝ)))*bblrGaussianAFEQuadMajorant n :=
      hf.norm.tsum_le_tsum hpoint hs
    _ = _ := tsum_mul_left

theorem bblrGaussianAFESpatialTail_uniform_absolute_power_bound (K : Set MomentShifts)
    (δ : ℝ) (hδ : 0<δ)
    (hρ : ∀ σ∈K, ∀ k : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ k‖)
    {ε : ℝ} (hε : 0<ε) (N : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ α : MomentShifts,
      (∀ j, ‖α j‖≤1/4) → ∀ t∈Icc T (2*T),
      (∑' n : Fin 4 → ℕ, ‖if n∉bblrAFEProductBox (T^(2+ε))
        then bblrAFESummand (polarPoleKiller T σ) α t n else 0‖)≤C*T^(-N) := by
  obtain ⟨r,hr⟩ := exists_nat_gt (max 0 ((N+9)/(2*ε)))
  have hrN : N+9<2*(r:ℝ)*ε := by
    have h := (le_max_right (0:ℝ) _).trans_lt hr
    rw [div_lt_iff₀ (by positivity : 0<2*ε)] at h
    nlinarith
  obtain ⟨D,hD,hV⟩ := bblrGaussianV_large_positive_line_norm_le r
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
    (SixthMoment.polarGaussianConstant_log_growth hT hL hδ σ c (hρ σ hσ)).trans
      (mul_le_mul_of_nonneg_left hlog hE)
  have htime : (2+t)^(4*r+8)≤4^(4*r+8)*T^(4*r+8) := by
    rw [← mul_pow]
    gcongr
    all_goals linarith [ht.1,ht.2]
  have hb := bblrAFESpatialTail_absolute_norm_le r (polarPoleKiller T σ) α hα t
    (B := D*polarGaussianConstant T σ c*(2+t)^(4*r+8)) (by positivity)
    (Real.rpow_pos_of_pos hTpos (2+ε))
    (fun x hx => hV T σ α hα t x (by linarith [ht.1]) hx)
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
theorem bblrGaussianAFESpatialTail_uniform_power_bound (K : Set MomentShifts)
    (δ : ℝ) (hδ : 0<δ)
    (hρ : ∀ σ∈K, ∀ k : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ k‖)
    {ε : ℝ} (hε : 0<ε) (N : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ α : MomentShifts,
      (∀ j, ‖α j‖≤1/4) → ∀ t∈Icc T (2*T),
      ‖bblrAFESpatialTail (polarPoleKiller T σ) α t (T^(2+ε))‖≤C*T^(-N) := by
  obtain ⟨r,hr⟩ := exists_nat_gt (max 0 ((N+9)/(2*ε)))
  have hrN : N+9<2*(r:ℝ)*ε := by
    have h := (le_max_right (0:ℝ) _).trans_lt hr
    rw [div_lt_iff₀ (by positivity : 0<2*ε)] at h
    nlinarith
  obtain ⟨D,hD,hV⟩ := bblrGaussianV_large_positive_line_norm_le r
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
    (SixthMoment.polarGaussianConstant_log_growth hT hL hδ σ c (hρ σ hσ)).trans
      (mul_le_mul_of_nonneg_left hlog hE)
  have htime : (2+t)^(4*r+8)≤4^(4*r+8)*T^(4*r+8) := by
    rw [← mul_pow]
    gcongr
    all_goals linarith [ht.1,ht.2]
  have hb := bblrAFESpatialTail_norm_le r (polarPoleKiller T σ) α hα t
    (B := D*polarGaussianConstant T σ c*(2+t)^(4*r+8)) (by positivity)
    (Real.rpow_pos_of_pos hTpos (2+ε))
    (fun x hx => hV T σ α hα t x (by linarith [ht.1]) hx)
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

end
end SixthMoment.Source
