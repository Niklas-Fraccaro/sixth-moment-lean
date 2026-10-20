import Sechstmoment.Numerator.U.Reconstruction.RectangularSmoothAFE
import Sechstmoment.Numerator.U.Reconstruction.SpatialAFETail


namespace Sechstmoment
open Complex Source Real MeasureTheory Filter Set
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 1000000

def rectangularAFEProductScaleGrid (X : ℝ) : Finset (Fin 4 → ℕ) :=
  (Fintype.piFinset (fun _ : Fin 4 =>
    Finset.range (⌊Real.log ((3/2:ℝ)^4*X)/Real.log (3/2:ℝ)⌋₊+1))).filter
      (fun k => (∏ j : Fin 4, rectangularAFESmoothScale (k j))≤X)

theorem rectangular_AFE_product_scale_grid_card_le (X : ℝ) :
    (rectangularAFEProductScaleGrid X).card≤
      (⌊Real.log ((3/2:ℝ)^4*X)/Real.log (3/2:ℝ)⌋₊+1)^4 := by
  apply (Finset.card_filter_le _ _).trans
  rw [Fintype.card_piFinset]
  simp

theorem rectangular_AFE_product_scale_grid_uniform_log_card {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop,
      ((rectangularAFEProductScaleGrid (T^(2+ε))).card : ℝ)≤C*(1+Real.log T)^4 := by
  have hq : 0<Real.log (3/2:ℝ) := Real.log_pos (by norm_num)
  let D : ℝ := 5+(2+ε)/Real.log (3/2:ℝ)
  have hD : 0≤D := by dsimp [D]; positivity
  refine ⟨D^4,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
  have ht : 0<T := zero_lt_one.trans_le hT
  have hL : 0≤Real.log T := Real.log_nonneg hT
  have he : Real.log ((3/2:ℝ)^4*T^(2+ε))/Real.log (3/2:ℝ)=
      4+(2+ε)/Real.log (3/2:ℝ)*Real.log T := by
    rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos ht _).ne',
      Real.log_pow,Real.log_rpow ht]
    field_simp
    ring
  have ha : 0≤Real.log ((3/2:ℝ)^4*T^(2+ε))/Real.log (3/2:ℝ) := by
    rw [he]
    positivity
  have hf := Nat.floor_le ha
  have hb : (⌊Real.log ((3/2:ℝ)^4*T^(2+ε))/Real.log (3/2:ℝ)⌋₊+1 : ℝ)≤
      D*(1+Real.log T) := by
    rw [he] at hf ⊢
    dsimp [D]
    have hd : 0≤(2+ε)/Real.log (3/2:ℝ) := by positivity
    nlinarith
  have hc : ((rectangularAFEProductScaleGrid (T^(2+ε))).card : ℝ)≤
      (⌊Real.log ((3/2:ℝ)^4*T^(2+ε))/Real.log (3/2:ℝ)⌋₊+1 : ℝ)^4 := by
    exact_mod_cast rectangular_AFE_product_scale_grid_card_le (T^(2+ε))
  calc
    _ ≤ _ := hc
    _ ≤ (D*(1+Real.log T))^4 := pow_le_pow_left₀ (by positivity) hb 4
    _ = _ := mul_pow _ _ _

theorem rectangular_AFE_product_scale_grid_mem_iff {X : ℝ} (_hX : 0<X)
    (k : Fin 4 → ℕ) :
    k∈rectangularAFEProductScaleGrid X ↔
      (∏ j : Fin 4, rectangularAFESmoothScale (k j))≤X := by
  constructor
  · exact fun hk => (Finset.mem_filter.mp hk).2
  · intro hk
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr (fun j => Finset.mem_range.mpr ?_),hk⟩
    have he : (∏ i : Fin 4, rectangularAFESmoothScale (k i)) =
        (∏ i : Fin 4, (3/2:ℝ)^(k i))/(3/2:ℝ)^4 := by
      unfold rectangularAFESmoothScale
      rw [Finset.prod_div_distrib]
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    rw [he] at hk
    have hprod : (∏ i : Fin 4, (3/2:ℝ)^(k i))≤(3/2:ℝ)^4*X := by
      have hh := (div_le_iff₀ (by positivity : 0<(3/2:ℝ)^4)).mp hk
      nlinarith
    have hj : (3/2:ℝ)^(k j)≤(∏ i : Fin 4, (3/2:ℝ)^(k i)) := by
      have h := Finset.prod_le_prod₀
        (s := Finset.univ)
        (f := fun i : Fin 4 => if i=j then (3/2:ℝ)^(k i) else 1)
        (g := fun i : Fin 4 => (3/2:ℝ)^(k i))
        (fun i _ => by split_ifs <;> positivity)
        (fun i _ => by
          by_cases hi : i=j
          · simp [hi]
          · simp only [ite_eq_right hi]
            exact one_le_pow₀ (by norm_num))
      simpa only [Fintype.prod_ite_eq'] using h
    have hlog := Real.log_le_log (pow_pos (by norm_num : (0:ℝ)<3/2) (k j)) (hj.trans hprod)
    rw [Real.log_pow] at hlog
    have hq : 0<Real.log (3/2:ℝ) := Real.log_pos (by norm_num)
    have hdiv : (k j : ℝ)≤Real.log ((3/2:ℝ)^4*X)/Real.log (3/2:ℝ) :=
      (le_div_iff₀ hq).mpr hlog
    have hf := Nat.lt_floor_add_one (Real.log ((3/2:ℝ)^4*X)/Real.log (3/2:ℝ))
    have hh : (k j : ℝ)<(⌊Real.log ((3/2:ℝ)^4*X)/Real.log (3/2:ℝ)⌋₊+1 : ℝ) := by
      linarith
    exact_mod_cast hh

theorem rectangular_AFE_smooth_weight_zero_above_grid {X : ℝ} (hX : 0<X)
    (n k : Fin 4 → ℕ) (hn : (positiveQuadProduct n : ℝ)≤X)
    (hk : k∉rectangularAFEProductScaleGrid X) :
    rectangularAFESmoothWeight k n=0 := by
  by_contra hw
  have hs (j : Fin 4) : rectangularAFESmoothScale (k j)≤(n j+1 : ℝ) := by
    have hj : rectangularSmoothBlockWeight ((3/2)*(n j+1 : ℝ)/(3/2)^(k j))≠0 :=
      (Finset.prod_ne_zero_iff.mp hw) j (Finset.mem_univ j)
    have hh : 1<(3/2)*(n j+1 : ℝ)/(3/2)^(k j) :=
      lt_of_not_ge (fun hh => hj (rectangularSmoothBlockWeight_zero_le hh))
    have hp := (lt_div_iff₀ (pow_pos (by norm_num : (0:ℝ)<3/2) (k j))).mp hh
    unfold rectangularAFESmoothScale
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<3/2)).mpr
    linarith
  have hprod : (∏ j : Fin 4, rectangularAFESmoothScale (k j))≤(positiveQuadProduct n : ℝ) := by
    rw [positiveQuadProduct_eq_prod]
    push_cast
    exact Finset.prod_le_prod₀ (fun j _ => by unfold rectangularAFESmoothScale; positivity)
      (fun j _ => hs j)
  exact hk ((rectangular_AFE_product_scale_grid_mem_iff hX k).mpr (hprod.trans hn))

theorem rectangular_AFE_smooth_grid_integer_product_le {X : ℝ} (k n : Fin 4 → ℕ)
    (hk : k∈rectangularAFEProductScaleGrid X) (hw : rectangularAFESmoothWeight k n≠0) :
    (positiveQuadProduct n : ℝ)≤16*X := by
  have hs (j : Fin 4) : (n j+1 : ℝ)≤2*rectangularAFESmoothScale (k j) := by
    have hj : rectangularSmoothBlockWeight ((3/2)*(n j+1 : ℝ)/(3/2)^(k j))≠0 :=
      (Finset.prod_ne_zero_iff.mp hw) j (Finset.mem_univ j)
    have hh : (3/2)*(n j+1 : ℝ)/(3/2)^(k j)<2 :=
      lt_of_not_ge (fun hh => hj (rectangularSmoothBlockWeight_zero_ge hh))
    have hp := (div_lt_iff₀ (pow_pos (by norm_num : (0:ℝ)<3/2) (k j))).mp hh
    unfold rectangularAFESmoothScale
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<3/2)).mpr
    linarith
  have hp : (positiveQuadProduct n : ℝ)≤∏ j : Fin 4, 2*rectangularAFESmoothScale (k j) := by
    rw [positiveQuadProduct_eq_prod]
    push_cast
    exact Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun j _ => hs j)
  have he : (∏ j : Fin 4, 2*rectangularAFESmoothScale (k j))=
      16*(∏ j : Fin 4, rectangularAFESmoothScale (k j)) := by
    rw [Finset.prod_mul_distrib]
    norm_num
  rw [he] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hk).2 (by norm_num))

def rectangularAFESmoothKeptWeight (X : ℝ) (n : Fin 4 → ℕ) : ℝ :=
  ∑ k∈rectangularAFEProductScaleGrid X, rectangularAFESmoothWeight k n

def rectangularAFESmoothTailWeight (X : ℝ) (n : Fin 4 → ℕ) : ℝ :=
  1-rectangularAFESmoothKeptWeight X n

theorem rectangular_AFE_smooth_kept_weight_bounds (X : ℝ) (n : Fin 4 → ℕ) :
    0≤rectangularAFESmoothKeptWeight X n ∧ rectangularAFESmoothKeptWeight X n≤1 := by
  refine ⟨Finset.sum_nonneg (fun k _ => rectangular_AFE_smooth_weight_nonneg k n),?_⟩
  have h := (rectangular_AFE_smooth_weight_hasSum n).summable.sum_le_tsum
    (rectangularAFEProductScaleGrid X) (fun k _ => rectangular_AFE_smooth_weight_nonneg k n)
  simpa only [rectangularAFESmoothKeptWeight,(rectangular_AFE_smooth_weight_hasSum n).tsum_eq] using h

theorem rectangular_AFE_smooth_tail_weight_bounds (X : ℝ) (n : Fin 4 → ℕ) :
    0≤rectangularAFESmoothTailWeight X n ∧ rectangularAFESmoothTailWeight X n≤1 := by
  have h := rectangular_AFE_smooth_kept_weight_bounds X n
  unfold rectangularAFESmoothTailWeight
  constructor <;> linarith

theorem rectangular_AFE_smooth_tail_weight_zero {X : ℝ} (hX : 0<X)
    (n : Fin 4 → ℕ) (hn : (positiveQuadProduct n : ℝ)≤X) :
    rectangularAFESmoothTailWeight X n=0 := by
  have h : (∑' k : Fin 4 → ℕ, rectangularAFESmoothWeight k n) =
      ∑ k∈rectangularAFEProductScaleGrid X, rectangularAFESmoothWeight k n :=
    tsum_eq_sum (fun k hk => rectangular_AFE_smooth_weight_zero_above_grid hX n k hn hk)
  rw [(rectangular_AFE_smooth_weight_hasSum n).tsum_eq] at h
  unfold rectangularAFESmoothTailWeight rectangularAFESmoothKeptWeight
  linarith

def rectangularAFESmoothProductGrid (G : ℂ → ℂ) (α : MomentShifts) (t X : ℝ) : ℂ :=
  ∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
    (rectangularAFESmoothWeight k n : ℂ)*bblrAFESummand G α t n

def rectangularAFESmoothProductTail (G : ℂ → ℂ) (α : MomentShifts) (t X : ℝ) : ℂ :=
  ∑' n : Fin 4 → ℕ, (rectangularAFESmoothTailWeight X n : ℂ)*bblrAFESummand G α t n

theorem rectangular_AFE_smooth_grid_series_identity (f : (Fin 4 → ℕ) → ℂ)
    (hf : Summable f) (X : ℝ) :
    (∑' n, f n) =
      (∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
        (rectangularAFESmoothWeight k n : ℂ)*f n)+
      (∑' n, (rectangularAFESmoothTailWeight X n : ℂ)*f n) := by
  have hs (k : Fin 4 → ℕ) : Summable (fun n => (rectangularAFESmoothWeight k n : ℂ)*f n) := by
    apply hf.norm.of_norm_bounded
    intro n
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (rectangular_AFE_smooth_weight_nonneg k n)]
    have hW : rectangularAFESmoothWeight k n≤1 := by
      unfold rectangularAFESmoothWeight
      have h := Finset.prod_le_prod₀
        (fun j (_ : j∈(Finset.univ : Finset (Fin 4))) => rectangularSmoothBlockWeight_nonneg _)
        (fun j (_ : j∈(Finset.univ : Finset (Fin 4))) => rectangularSmoothBlockWeight_le_one
          ((3/2)*(n j+1:ℝ)/(3/2)^(k j)))
      simpa only [Finset.prod_const_one] using h
    simpa using mul_le_mul_of_nonneg_right hW (norm_nonneg (f n))
  have hKeep : Summable (fun n => (rectangularAFESmoothKeptWeight X n : ℂ)*f n) := by
    apply hf.norm.of_norm_bounded
    intro n
    have hW := rectangular_AFE_smooth_kept_weight_bounds X n
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hW.1]
    simpa using mul_le_mul_of_nonneg_right hW.2 (norm_nonneg (f n))
  have hTail : Summable (fun n => (rectangularAFESmoothTailWeight X n : ℂ)*f n) := by
    apply hf.norm.of_norm_bounded
    intro n
    have hW := rectangular_AFE_smooth_tail_weight_bounds X n
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hW.1]
    simpa using mul_le_mul_of_nonneg_right hW.2 (norm_nonneg (f n))
  have he : (∑' n, (rectangularAFESmoothKeptWeight X n : ℂ)*f n) =
      ∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
        (rectangularAFESmoothWeight k n : ℂ)*f n := by
    unfold rectangularAFESmoothKeptWeight
    simp_rw [Complex.ofReal_sum,Finset.sum_mul]
    rw [Summable.tsum_finsetSum (fun k _ => hs k)]
    exact Finset.sum_congr rfl (fun k _ => rectangular_AFE_smooth_block_finite f k)
  rw [← he,← hKeep.tsum_add hTail]
  apply tsum_congr
  intro n
  unfold rectangularAFESmoothTailWeight
  push_cast
  ring

theorem rectangular_actual_AFE_smooth_product_grid (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (hα : ∀ j, -1/2<(α j).re) (t X : ℝ) :
    bblrAFESum G α t=rectangularAFESmoothProductGrid G α t X+
      rectangularAFESmoothProductTail G α t X :=
  rectangular_AFE_smooth_grid_series_identity _ (rectangular_actual_AFE_summable G α hG t hα) X

theorem rectangularAFESmoothProductTail_stronglyMeasurable (G : ℂ → ℂ) (hG : Continuous G)
    (α : MomentShifts) (hα : ∀ j, -1/2<(α j).re) (X : ℝ) :
    StronglyMeasurable (fun t : ℝ => rectangularAFESmoothProductTail G α t X) :=
  StronglyMeasurable.tsum (fun n =>
    (rectangular_actual_AFE_summand_stronglyMeasurable G hG α hα n).const_mul _)

theorem rectangularAFESmoothProductTail_uniform_power_bound (K : Set MomentShifts)
    (δ : ℝ) (hδ : 0<δ)
    (hρ : ∀ σ∈K, ∀ k : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ k‖)
    {ε : ℝ} (hε : 0<ε) (N : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ α : MomentShifts,
      (∀ j, ‖α j‖≤1/4) → ∀ t∈Icc T (2*T),
      ‖rectangularAFESmoothProductTail (polarPoleKiller T σ) α t (T^(2+ε))‖≤C*T^(-N) := by
  obtain ⟨C,hC,hb⟩ := bblrGaussianAFESpatialTail_uniform_absolute_power_bound K δ hδ hρ hε N
  refine ⟨C,hC,?_⟩
  filter_upwards [hb,eventually_gt_atTop (0:ℝ)] with T hb hT
  intro σ hσ α hα t ht
  have hreal : ∀ j, -1/2<(α j).re := by
    intro j
    have h := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hα j))).1
    linarith
  have hs := rectangular_actual_AFE_summable (polarPoleKiller T σ) α
    (polarPoleKiller_BBLREntireWeight T σ α) t hreal
  have hOutside : Summable (fun n : Fin 4 → ℕ =>
      if n∉bblrAFEProductBox (T^(2+ε)) then bblrAFESummand (polarPoleKiller T σ) α t n else 0) := by
    apply hs.norm.of_norm_bounded
    intro n
    by_cases hn : n∉bblrAFEProductBox (T^(2+ε))
    · simp only [ite_eq_left hn]
      exact le_rfl
    · simp only [ite_eq_right hn,norm_zero]
      exact norm_nonneg _
  have hpoint (n : Fin 4 → ℕ) :
      ‖(rectangularAFESmoothTailWeight (T^(2+ε)) n : ℂ)*
        bblrAFESummand (polarPoleKiller T σ) α t n‖≤
      ‖if n∉bblrAFEProductBox (T^(2+ε))
        then bblrAFESummand (polarPoleKiller T σ) α t n else 0‖ := by
    by_cases hn : n∈bblrAFEProductBox (T^(2+ε))
    · rw [rectangular_AFE_smooth_tail_weight_zero (Real.rpow_pos_of_pos hT (2+ε)) n
        ((bblrAFEProductBox_mem_iff _ n).mp hn)]
      simp [hn]
    · simp only [hn,not_false_eq_true,ite_true]
      have hW := rectangular_AFE_smooth_tail_weight_bounds (T^(2+ε)) n
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hW.1]
      simpa using mul_le_mul_of_nonneg_right hW.2 (norm_nonneg _)
  have hTail := hOutside.norm.of_norm_bounded hpoint
  unfold rectangularAFESmoothProductTail
  calc
    _ ≤ ∑' n : Fin 4 → ℕ, ‖(rectangularAFESmoothTailWeight (T^(2+ε)) n : ℂ)*
        bblrAFESummand (polarPoleKiller T σ) α t n‖ := norm_tsum_le_tsum_norm hTail.norm
    _ ≤ ∑' n : Fin 4 → ℕ, ‖if n∉bblrAFEProductBox (T^(2+ε))
        then bblrAFESummand (polarPoleKiller T σ) α t n else 0‖ :=
      hTail.norm.tsum_le_tsum hpoint hOutside.norm
    _ ≤ _ := hb σ hσ α hα t ht

end
end Sechstmoment
