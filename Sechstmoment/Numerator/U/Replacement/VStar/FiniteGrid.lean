import Sechstmoment.Numerator.U.Replacement.VStar.SpatialTail
import Sechstmoment.Numerator.U.Separation.SmallContour.GridBounds

namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 1000000

def rectangularVStarSmoothProductGrid (G : ℂ → ℂ) (α : MomentShifts) (t X : ℝ) : ℂ :=
  ∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
    (rectangularAFESmoothWeight k n:ℂ)*bblrVStarAFESummand G α t n

def rectangularVStarSmoothProductTail (G : ℂ → ℂ) (α : MomentShifts) (t X : ℝ) : ℂ :=
  ∑' n : Fin 4 → ℕ, (rectangularAFESmoothTailWeight X n:ℂ)*bblrVStarAFESummand G α t n

def rectangularVStarSmoothGridFrequencyTail (c T : ℝ) (σ α : MomentShifts)
    (t X R : ℝ) : ℂ :=
  ∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
    (rectangularAFESmoothWeight k n:ℂ)*
      (bblrVStarAFESummand (polarPoleKiller T σ) α t n-bblrGaussianVStarCoreSummand c T σ α t R n)

def rectangularFiniteSmallVStarRemainder (c T : ℝ) (σ α : MomentShifts) (t X R : ℝ) : ℂ :=
  rectangularVStarSmoothProductTail (polarPoleKiller T σ) α t X+
    rectangularVStarSmoothGridFrequencyTail c T σ α t X R

theorem rectangular_actual_VStar_finite_small_grid (c T : ℝ) (σ α : MomentShifts)
    (hα : ∀ j, ‖α j‖≤1/4) (t X R : ℝ) :
    bblrVStarAFESum (polarPoleKiller T σ) α t=
      rectangularFiniteSmallVStarCore c T σ α t X R+rectangularFiniteSmallVStarRemainder c T σ α t X R := by
  have he := rectangular_AFE_smooth_grid_series_identity
    (bblrVStarAFESummand (polarPoleKiller T σ) α t)
    (bblrGaussianVStarAFE_summable T σ α hα t) X
  change bblrVStarAFESum (polarPoleKiller T σ) α t=
    rectangularVStarSmoothProductGrid (polarPoleKiller T σ) α t X+
      rectangularVStarSmoothProductTail (polarPoleKiller T σ) α t X at he
  rw [he]
  unfold rectangularFiniteSmallVStarCore rectangularFiniteSmallVStarRemainder
    rectangularVStarSmoothGridFrequencyTail rectangularVStarSmoothProductGrid
  simp_rw [mul_sub,Finset.sum_sub_distrib]
  ring

theorem rectangularVStarSmoothProductTail_time_stronglyMeasurable (G : ℂ → ℂ)
    (hG : Continuous G) (α : MomentShifts) (X : ℝ) :
    StronglyMeasurable (fun t : ℝ => rectangularVStarSmoothProductTail G α t X) :=
  StronglyMeasurable.tsum (fun n => (bblrVStarAFESummand_time_stronglyMeasurable G hG α n).const_mul _)

theorem rectangularFiniteSmallVStarCore_time_stronglyMeasurable {c : ℝ} (hc : 0<c)
    (T : ℝ) (σ α : MomentShifts) (X R : ℝ) :
    StronglyMeasurable (fun t : ℝ => rectangularFiniteSmallVStarCore c T σ α t X R) := by
  have he : (fun t : ℝ => rectangularFiniteSmallVStarCore c T σ α t X R)=
      ∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
        fun t : ℝ => (rectangularAFESmoothWeight k n:ℂ)*bblrGaussianVStarCoreSummand c T σ α t R n := by
    funext t
    simp only [rectangularFiniteSmallVStarCore,Finset.sum_apply]
  rw [he]
  apply Finset.stronglyMeasurable_sum
  intro k _
  apply Finset.stronglyMeasurable_sum
  intro n _
  exact (bblrGaussianVStarCoreSummand_time_stronglyMeasurable hc T σ α R n).const_mul _

theorem rectangularFiniteSmallVStarRemainder_time_stronglyMeasurable {c : ℝ} (hc : 0<c)
    (T : ℝ) (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) (X R : ℝ) :
    StronglyMeasurable (fun t : ℝ => rectangularFiniteSmallVStarRemainder c T σ α t X R) := by
  have he : (fun t : ℝ => rectangularFiniteSmallVStarRemainder c T σ α t X R)=
      (fun t : ℝ => bblrVStarAFESum (polarPoleKiller T σ) α t)-
        (fun t : ℝ => rectangularFiniteSmallVStarCore c T σ α t X R) := by
    funext t
    have h := rectangular_actual_VStar_finite_small_grid c T σ α hα t X R
    simp only [Pi.sub_apply]
    linear_combination -h
  rw [he]
  exact (bblrVStarAFESum_time_stronglyMeasurable _ (polarPoleKiller_differentiable T σ).continuous α).sub
    (rectangularFiniteSmallVStarCore_time_stronglyMeasurable hc T σ α X R)

theorem bblrGaussianVStarTail_uniform_logarithmic_bound {c θ : ℝ}
    (hc : 0<c) (hc1 : c≤1) (hθ : 0<θ) (K : Set MomentShifts)
    (δ : ℝ) (hδ : 0<δ)
    (hρ : ∀ σ∈K, ∀ k : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ k‖) (N : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ t∈Icc T (2*T),
      ∀ x : ℝ, 1≤x → ‖bblrGaussianVStarTail c T σ x t (θ*Real.log T)‖≤C*T^(-N) := by
  let D : ℝ := gaussianTailConstant 48/(2*Real.pi)
  let E : ℝ := Real.exp (c^2)*(1+|c|)^48*(1+1/δ^2)^24
  have hD : 0≤D := div_nonneg (gaussianTailConstant_nonneg 48) (by positivity)
  have hE : 0≤E := by dsimp [E]; positivity
  have hlog : ∀ᶠ T : ℝ in atTop, (Real.log T)^48≤T := by
    have h := (log_pow_isLittleO_rpow 48 (δ := 1) zero_lt_one).bound zero_lt_one
    filter_upwards [h,eventually_gt_atTop (1:ℝ)] with T hT hpos
    simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_pos (zero_lt_one.trans hpos),
      abs_of_nonneg (by positivity : 0≤(Real.log T)^48),one_mul] using hT
  refine ⟨D*E*4/c,by positivity,?_⟩
  filter_upwards [hlog,polynomial_gaussian_logarithmic_eventually_le hθ 3 N,
    eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with T hlog hdec hT hL
  intro σ hσ t ht x hx
  have hTp : 0<T := zero_lt_one.trans hT
  have htp : 0<t := hTp.trans_le ht.1
  have hx0 : 0<x := zero_lt_one.trans_le hx
  have hCG := polarGaussianConstant_nonneg T σ c
  have hCGb : polarGaussianConstant T σ c≤E*T :=
    (Sechstmoment.polarGaussianConstant_log_growth hT hL hδ σ c (hρ σ hσ)).trans
      (mul_le_mul_of_nonneg_left hlog hE)
  have hscaled : (x/t^2)^(-c)≤4*T^2 := by
    have he : (x/t^2)^(-c)=(t^2)^c*x^(-c) := by
      rw [Real.div_rpow hx0.le (sq_nonneg t) (-c),Real.rpow_neg (sq_nonneg t) c,div_inv_eq_mul]
      exact mul_comm _ _
    rw [he]
    have htime : (t^2)^c≤t^2 := by
      calc
        _ ≤ (t^2)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by nlinarith only [ht.1,hT]) hc1
        _ = _ := Real.rpow_one _
    have hxpow := Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith : -c≤0)
    calc
      _ ≤ t^2*1 := mul_le_mul htime hxpow (Real.rpow_nonneg hx0.le _) (sq_nonneg t)
      _ ≤ _ := by nlinarith only [ht.1,ht.2,hT]
  have hb := bblrGaussianVStarTail_norm_le hc hx0 htp.ne'
    (mul_nonneg hθ.le (Real.log_nonneg hT.le)) T σ
  have hdecNat : T^3*Real.exp (-(1/2)*(θ*Real.log T)^2)≤T^(-N) := by
    rw [show T^(3:ℝ)=T^3 from Real.rpow_natCast T 3] at hdec
    exact hdec
  calc
    _ ≤ D*(E*T)/c*(4*T^2)*Real.exp (-(1/2)*(θ*Real.log T)^2) := by
      apply hb.trans
      gcongr
    _ = (D*E*4/c)*(T^3*Real.exp (-(1/2)*(θ*Real.log T)^2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecNat (by positivity)

theorem bblrVStarAFESummand_sub_core_norm_le {c t : ℝ}
    (hc : 0<c) (ht : t≠0) (T : ℝ) (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4)
    (R : ℝ) (n : Fin 4 → ℕ) :
    ‖bblrVStarAFESummand (polarPoleKiller T σ) α t n-bblrGaussianVStarCoreSummand c T σ α t R n‖≤
      ‖bblrGaussianVStarTail c T σ (positiveQuadProduct n) t R‖ := by
  have hx : 0<(positiveQuadProduct n:ℝ) := by unfold positiveQuadProduct; positivity
  have hden : 1≤‖∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j)‖ := by
    rw [norm_prod]
    apply Finset.one_le_prod₀
    intro j _
    have hn : 0<(n j+1:ℝ) := by positivity
    have he : 0≤1/2+(α j).re := by
      have h := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hα j))).1
      linarith
    rw [show (n j+1:ℂ)=((n j+1:ℝ):ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hn]
    simp only [Complex.add_re,Complex.div_ofNat_re,Complex.one_re]
    exact Real.one_le_rpow (by norm_cast; omega) he
  have he : bblrVStarAFESummand (polarPoleKiller T σ) α t n-bblrGaussianVStarCoreSummand c T σ α t R n=
      rectangularAFEOscillation t n*bblrGaussianVStarTail c T σ (positiveQuadProduct n) t R/
        ∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j) := by
    unfold bblrVStarAFESummand bblrGaussianVStarCoreSummand
    rw [bblrGaussianVStar_core_add_tail hc hx ht T σ R]
    ring
  rw [he,norm_div,norm_mul]
  have hosc : ‖rectangularAFEOscillation t n‖=1 := by
    simpa only [rectangularAFEOscillation] using bblrAFE_oscillation_norm_one n t
  rw [hosc,one_mul]
  exact div_le_self (norm_nonneg _) hden

theorem rectangularVStarSmoothGridFrequencyTail_uniform_rapid_bound
    {c ε θ : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 0<ε) (hθ : 0<θ)
    (K : Set MomentShifts) (δ : ℝ) (hδ : 0<δ)
    (hρ : ∀ σ∈K, ∀ k : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ k‖) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ α : MomentShifts,
      (∀ j, ‖α j‖≤1/4) → ∀ t∈Icc T (2*T),
      ‖rectangularVStarSmoothGridFrequencyTail c T σ α t (T^(2+ε)) (θ*Real.log T)‖≤C*T^(-M) := by
  obtain ⟨C,hC,hV⟩ := bblrGaussianVStarTail_uniform_logarithmic_bound hc hc1 hθ K δ hδ hρ (M+3+ε)
  obtain ⟨D,hD,hcard⟩ := rectangular_small_contour_grid_uniform_polynomial_card hε
  refine ⟨C*D,mul_nonneg hC hD,?_⟩
  filter_upwards [hV,hcard,eventually_gt_atTop (1:ℝ)] with T hV hcard hT
  intro σ hσ α hα t ht
  have hTp : 0<T := zero_lt_one.trans hT
  have htp : 0<t := hTp.trans_le ht.1
  have hB : 0≤C*T^(-(M+3+ε)) := by positivity
  have hp (k n : Fin 4 → ℕ) :
      ‖(rectangularAFESmoothWeight k n:ℂ)*
        (bblrVStarAFESummand (polarPoleKiller T σ) α t n-
          bblrGaussianVStarCoreSummand c T σ α t (θ*Real.log T) n)‖≤C*T^(-(M+3+ε)) := by
    have hx : 1≤(positiveQuadProduct n:ℝ) := by
      have hp : 0 < positiveQuadProduct n := by unfold positiveQuadProduct; positivity
      exact_mod_cast hp
    have hb := (bblrVStarAFESummand_sub_core_norm_le hc htp.ne' T σ α hα _ n).trans (hV σ hσ t ht _ hx)
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (rectangular_AFE_smooth_weight_nonneg k n)]
    calc
      _ ≤ rectangularAFESmoothWeight k n*(C*T^(-(M+3+ε))) :=
        mul_le_mul_of_nonneg_left hb (rectangular_AFE_smooth_weight_nonneg k n)
      _ ≤ _ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (rectangular_small_contour_smooth_weight_le_one k n) hB
  have he : ‖rectangularVStarSmoothGridFrequencyTail c T σ α t (T^(2+ε)) (θ*Real.log T)‖≤
      (C*T^(-(M+3+ε)))*(∑ k∈rectangularAFEProductScaleGrid (T^(2+ε)), ((rectangularAFESmoothBox k).card:ℝ)) := by
    unfold rectangularVStarSmoothGridFrequencyTail
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ k∈rectangularAFEProductScaleGrid (T^(2+ε)), ∑ n∈rectangularAFESmoothBox k, C*T^(-(M+3+ε)) := by
        apply Finset.sum_le_sum
        intro k _
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n _ => hp k n))
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
  calc
    _ ≤ (C*T^(-(M+3+ε)))*(D*T^(3+ε)) := he.trans (mul_le_mul_of_nonneg_left hcard hB)
    _ = _ := by
      rw [mul_assoc,mul_left_comm (T^(-(M+3+ε))) D,←mul_assoc,←Real.rpow_add hTp]
      congr 1
      ring

theorem rectangularVStarSmoothProductTail_uniform_power_bound (K : Set MomentShifts)
    (δ : ℝ) (hδ : 0<δ)
    (hρ : ∀ σ∈K, ∀ k : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ k‖)
    {ε : ℝ} (hε : 0<ε) (N : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ α : MomentShifts,
      (∀ j, ‖α j‖≤1/4) → ∀ t∈Icc T (2*T),
      ‖rectangularVStarSmoothProductTail (polarPoleKiller T σ) α t (T^(2+ε))‖≤C*T^(-N) := by
  obtain ⟨C,hC,hb⟩ := bblrGaussianVStarAFESpatialTail_uniform_absolute_power_bound K δ hδ hρ hε N
  refine ⟨C,hC,?_⟩
  filter_upwards [hb,eventually_gt_atTop (0:ℝ)] with T hb hT
  intro σ hσ α hα t ht
  have hreal : ∀ j, -1/2<(α j).re := by
    intro j
    have h := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hα j))).1
    linarith
  have hs := bblrGaussianVStarAFE_summable T σ α hα t
  have hOutside : Summable (fun n : Fin 4 → ℕ =>
      if n∉bblrAFEProductBox (T^(2+ε)) then bblrVStarAFESummand (polarPoleKiller T σ) α t n else 0) := by
    apply hs.norm.of_norm_bounded
    intro n
    by_cases hn : n∉bblrAFEProductBox (T^(2+ε))
    · simp only [ite_eq_left hn]
      exact le_rfl
    · simp only [ite_eq_right hn,norm_zero]
      exact norm_nonneg _
  have hpoint (n : Fin 4 → ℕ) :
      ‖(rectangularAFESmoothTailWeight (T^(2+ε)) n : ℂ)*
        bblrVStarAFESummand (polarPoleKiller T σ) α t n‖≤
      ‖if n∉bblrAFEProductBox (T^(2+ε))
        then bblrVStarAFESummand (polarPoleKiller T σ) α t n else 0‖ := by
    by_cases hn : n∈bblrAFEProductBox (T^(2+ε))
    · rw [rectangular_AFE_smooth_tail_weight_zero (Real.rpow_pos_of_pos hT (2+ε)) n
        ((bblrAFEProductBox_mem_iff _ n).mp hn)]
      simp [hn]
    · simp only [hn,not_false_eq_true,ite_true]
      have hW := rectangular_AFE_smooth_tail_weight_bounds (T^(2+ε)) n
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hW.1]
      simpa using mul_le_mul_of_nonneg_right hW.2 (norm_nonneg _)
  have hTail := hOutside.norm.of_norm_bounded hpoint
  unfold rectangularVStarSmoothProductTail
  calc
    _ ≤ ∑' n : Fin 4 → ℕ, ‖(rectangularAFESmoothTailWeight (T^(2+ε)) n : ℂ)*
        bblrVStarAFESummand (polarPoleKiller T σ) α t n‖ := norm_tsum_le_tsum_norm hTail.norm
    _ ≤ ∑' n : Fin 4 → ℕ, ‖if n∉bblrAFEProductBox (T^(2+ε))
        then bblrVStarAFESummand (polarPoleKiller T σ) α t n else 0‖ :=
      hTail.norm.tsum_le_tsum hpoint hOutside.norm
    _ ≤ _ := hb σ hσ α hα t ht


theorem rectangularFiniteSmallVStarRemainder_uniform_rapid_bound
    {c ε θ : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 0<ε) (hθ : 0<θ)
    (K : Set MomentShifts) (δ : ℝ) (hδ : 0<δ)
    (hρ : ∀ σ∈K, ∀ k : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ k‖) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ α : MomentShifts,
      (∀ j, ‖α j‖≤1/4) → ∀ t∈Icc T (2*T),
      ‖rectangularFiniteSmallVStarRemainder c T σ α t (T^(2+ε)) (θ*Real.log T)‖≤C*T^(-M) := by
  obtain ⟨C₀,hC₀,h₀⟩ := rectangularVStarSmoothProductTail_uniform_power_bound K δ hδ hρ hε M
  obtain ⟨C₁,hC₁,h₁⟩ := rectangularVStarSmoothGridFrequencyTail_uniform_rapid_bound hc hc1 hε hθ K δ hδ hρ M
  refine ⟨C₀+C₁,add_nonneg hC₀ hC₁,?_⟩
  filter_upwards [h₀,h₁] with T h₀ h₁
  intro σ hσ α hα t ht
  unfold rectangularFiniteSmallVStarRemainder
  calc
    _ ≤ ‖rectangularVStarSmoothProductTail (polarPoleKiller T σ) α t (T^(2+ε))‖+
        ‖rectangularVStarSmoothGridFrequencyTail c T σ α t (T^(2+ε)) (θ*Real.log T)‖ := norm_add_le _ _
    _ ≤ C₀*T^(-M)+C₁*T^(-M) := add_le_add (h₀ σ hσ α hα t ht) (h₁ σ hσ α hα t ht)
    _ = _ := by ring

theorem bblrVStarAFESum_uniform_finite_small_error
    {c ε θ : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 0<ε) (hθ : 0<θ)
    (K : Set MomentShifts) (δ : ℝ) (hδ : 0<δ)
    (hρ : ∀ σ∈K, ∀ k : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ k‖) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ α : MomentShifts,
      (∀ j, ‖α j‖≤1/4) → ∀ t∈Icc T (2*T),
      ‖bblrVStarAFESum (polarPoleKiller T σ) α t-
        rectangularFiniteSmallVStarCore c T σ α t (T^(2+ε)) (θ*Real.log T)‖≤C*T^(-M) := by
  obtain ⟨C,hC,hb⟩ := rectangularFiniteSmallVStarRemainder_uniform_rapid_bound hc hc1 hε hθ K δ hδ hρ M
  refine ⟨C,hC,?_⟩
  filter_upwards [hb] with T hb
  intro σ hσ α hα t ht
  rw [rectangular_actual_VStar_finite_small_grid c T σ α hα t _ _,add_sub_cancel_left]
  exact hb σ hσ α hα t ht

theorem bblrGaussianVStarAFESum_uniform_polynomial_bound
    (K : Set MomentShifts) (δ : ℝ) (hδ : 0<δ)
    (hρ : ∀ σ∈K, ∀ k : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ k‖) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ α : MomentShifts,
      (∀ j, ‖α j‖≤1/4) → ∀ t∈Icc T (2*T),
      ‖bblrVStarAFESum (polarPoleKiller T σ) α t‖≤C*T^(3:ℝ) := by
  let D : ℝ := gaussianTailConstant 48/(2*Real.pi)
  let E : ℝ := Real.exp 1*2^48*(1+1/δ^2)^24
  let J : ℝ := ∑' n : Fin 4 → ℕ, bblrGaussianAFEQuadMajorant n
  have hD : 0≤D := div_nonneg (gaussianTailConstant_nonneg 48) (by positivity)
  have hE : 0≤E := by dsimp [E]; positivity
  have hJ : 0≤J := tsum_nonneg bblrGaussianAFEQuadMajorant_nonneg
  have hlog : ∀ᶠ T : ℝ in atTop, (Real.log T)^48≤T := by
    have h := (log_pow_isLittleO_rpow 48 (δ := 1) zero_lt_one).bound zero_lt_one
    filter_upwards [h,eventually_gt_atTop (1:ℝ)] with T hT hpos
    simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_pos (zero_lt_one.trans hpos),
      abs_of_nonneg (by positivity : 0≤(Real.log T)^48),one_mul] using hT
  refine ⟨D*E*4*J,by positivity,?_⟩
  filter_upwards [hlog,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hlog hT hL
  intro σ hσ α hα t ht
  have hCG := polarGaussianConstant_nonneg T σ 1
  have hCGb : polarGaussianConstant T σ 1≤E*T := by
    apply (Source.polarGaussianConstant_log_growth hT hL hδ σ (hρ σ hσ)).trans
    exact mul_le_mul_of_nonneg_left hlog hE
  have htime : t^2≤4*T^2 := by nlinarith [ht.1,ht.2]
  calc
    _ ≤ (D*polarGaussianConstant T σ 1*t^2)*J := bblrGaussianVStarAFESum_norm_le T σ α hα t
    _ ≤ (D*(E*T)*(4*T^2))*J := by gcongr
    _ = _ := by rw [show T^(3:ℝ)=T^3 from (Real.rpow_natCast T 3)]; ring

end
end Sechstmoment
