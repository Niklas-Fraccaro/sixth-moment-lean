import Sechstmoment.Numerator.U.Separation.AmplifiedSmoothGrid


namespace Sechstmoment
open Complex Source Real MeasureTheory Filter Set
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 1000000

theorem rectangular_smooth_grid_eq_tsum_kept (f : (Fin 4 → ℕ) → ℂ)
    (hf : Summable f) (X : ℝ) :
    (∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
      (rectangularAFESmoothWeight k n : ℂ)*f n) =
      ∑' n, (rectangularAFESmoothKeptWeight X n : ℂ)*f n := by
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
  symm
  unfold rectangularAFESmoothKeptWeight
  simp_rw [Complex.ofReal_sum,Finset.sum_mul]
  rw [Summable.tsum_finsetSum (fun k _ => hs k)]
  exact Finset.sum_congr rfl (fun k _ => rectangular_AFE_smooth_block_finite f k)

theorem rectangular_smooth_grid_norm_le_tsum_norm (f : (Fin 4 → ℕ) → ℂ)
    (hf : Summable f) (X : ℝ) :
    ‖∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
      (rectangularAFESmoothWeight k n : ℂ)*f n‖≤∑' n, ‖f n‖ := by
  have hp (n : Fin 4 → ℕ) : ‖(rectangularAFESmoothKeptWeight X n : ℂ)*f n‖≤‖f n‖ := by
    have hW := rectangular_AFE_smooth_kept_weight_bounds X n
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hW.1]
    simpa using mul_le_mul_of_nonneg_right hW.2 (norm_nonneg (f n))
  have hs := hf.norm.of_norm_bounded hp
  rw [rectangular_smooth_grid_eq_tsum_kept f hf X]
  exact (norm_tsum_le_tsum_norm hs.norm).trans (hs.norm.tsum_le_tsum hp hf.norm)

def rectangularFiniteGaussianCore (T : ℝ) (σ α : MomentShifts) (t X R : ℝ) : ℂ :=
  ∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
    (rectangularAFESmoothWeight k n : ℂ)*bblrGaussianAFECoreSummand T σ α t R n

def rectangularSmoothGridFrequencyTail (T : ℝ) (σ α : MomentShifts) (t X R : ℝ) : ℂ :=
  ∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
    (rectangularAFESmoothWeight k n : ℂ)*bblrGaussianAFETailSummand T σ α t R n

def rectangularFiniteGaussianRemainder (T : ℝ) (σ α : MomentShifts) (t X R : ℝ) : ℂ :=
  rectangularAFESmoothProductTail (polarPoleKiller T σ) α t X+
    rectangularSmoothGridFrequencyTail T σ α t X R

theorem rectangular_smooth_grid_core_add_frequency_tail (T : ℝ) (σ α : MomentShifts)
    (hα : ∀ j, ‖α j‖≤1/4) (t X R : ℝ) :
    rectangularAFESmoothProductGrid (polarPoleKiller T σ) α t X=
      rectangularFiniteGaussianCore T σ α t X R+
        rectangularSmoothGridFrequencyTail T σ α t X R := by
  unfold rectangularAFESmoothProductGrid rectangularFiniteGaussianCore rectangularSmoothGridFrequencyTail
  simp_rw [bblrGaussianAFESummand_core_add_tail T σ α t R hα,mul_add,
    Finset.sum_add_distrib]

theorem rectangular_actual_AFE_finite_gaussian_grid (T : ℝ) (σ α : MomentShifts)
    (hα : ∀ j, ‖α j‖≤1/4) (t X R : ℝ) :
    bblrAFESum (polarPoleKiller T σ) α t=
      rectangularFiniteGaussianCore T σ α t X R+
        rectangularFiniteGaussianRemainder T σ α t X R := by
  have hr : ∀ j, -1/2<(α j).re := by
    intro j
    have h := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hα j))).1
    linarith
  rw [rectangular_actual_AFE_smooth_product_grid _ _ (polarPoleKiller_BBLREntireWeight T σ _) hr t X,
    rectangular_smooth_grid_core_add_frequency_tail T σ α hα t X R]
  unfold rectangularFiniteGaussianRemainder
  ring

theorem rectangularSmoothGridFrequencyTail_time_stronglyMeasurable
    (T : ℝ) (σ α : MomentShifts) (hα : ∀ j, -1/2<(α j).re) (X R : ℝ) :
    StronglyMeasurable (fun t : ℝ => rectangularSmoothGridFrequencyTail T σ α t X R) := by
  have he : (fun t : ℝ => rectangularSmoothGridFrequencyTail T σ α t X R) =
      ∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
        fun t : ℝ => (rectangularAFESmoothWeight k n : ℂ)*bblrGaussianAFETailSummand T σ α t R n := by
    funext t
    simp only [Finset.sum_apply,rectangularSmoothGridFrequencyTail]
  rw [he]
  apply Finset.stronglyMeasurable_sum
  intro k _
  apply Finset.stronglyMeasurable_sum
  intro n _
  have hc : Continuous (fun t : ℝ => rectangularAFEOscillation t n) := by
    unfold rectangularAFEOscillation
    apply Continuous.const_cpow
    · fun_prop
    · apply Or.inl
      have h₁ : (((n 0+1)*(n 1+1) : ℕ) : ℂ)≠0 := by
        exact_mod_cast Nat.mul_ne_zero (Nat.succ_ne_zero (n 0)) (Nat.succ_ne_zero (n 1))
      have h₂ : (((n 2+1)*(n 3+1) : ℕ) : ℂ)≠0 := by
        exact_mod_cast Nat.mul_ne_zero (Nat.succ_ne_zero (n 2)) (Nat.succ_ne_zero (n 3))
      exact div_ne_zero h₁ h₂
  have hm := bblrGaussianVTail_time_stronglyMeasurable T σ α hα (positiveQuadProduct n)
    R (by unfold positiveQuadProduct; positivity)
  have hs : StronglyMeasurable (fun t : ℝ => bblrGaussianAFETailSummand T σ α t R n) := by
    simpa only [bblrGaussianAFETailSummand,rectangularAFEOscillation,div_eq_mul_inv,
      Pi.mul_apply] using (hc.stronglyMeasurable.mul hm).mul_const
        (∏ j : Fin 4, (n j+1 : ℂ)^(1/2+α j))⁻¹
  exact hs.const_mul _

theorem rectangularFiniteGaussianRemainder_time_stronglyMeasurable
    (T : ℝ) (σ α : MomentShifts) (hα : ∀ j, -1/2<(α j).re) (X R : ℝ) :
    StronglyMeasurable (fun t : ℝ => rectangularFiniteGaussianRemainder T σ α t X R) :=
  (rectangularAFESmoothProductTail_stronglyMeasurable (polarPoleKiller T σ)
    (polarPoleKiller_differentiable T σ).continuous α hα X).add
      (rectangularSmoothGridFrequencyTail_time_stronglyMeasurable T σ α hα X R)

theorem rectangularSmoothGridFrequencyTail_uniform_power_bound
    (K : Set MomentShifts) (δ : ℝ) (hδ : 0<δ)
    (hρ : ∀ σ∈K, ∀ k : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ k‖)
    {θ : ℝ} (hθ : 0<θ) (N : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ α : MomentShifts,
      (∀ j, ‖α j‖≤1/4) → ∀ t∈Icc T (2*T), ∀ X : ℝ,
      ‖rectangularSmoothGridFrequencyTail T σ α t X (θ*Real.log T)‖≤C*T^(-N) := by
  obtain ⟨A,hA⟩ := exists_nat_gt N
  obtain ⟨D,hD,hb⟩ := bblrGaussianVTail_uniform_logarithmic_power_bound K δ hδ hρ hθ A
  let S : ℝ := ∑' n, bblrGaussianAFEQuadMajorant n
  have hS : 0≤S := tsum_nonneg bblrGaussianAFEQuadMajorant_nonneg
  refine ⟨D*S,by positivity,?_⟩
  filter_upwards [hb,eventually_gt_atTop (1:ℝ)] with T hb hT
  intro σ hσ α hα t ht X
  have htpos : 0≤t := by linarith [ht.1]
  have hR : 0≤θ*Real.log T := mul_nonneg hθ.le (Real.log_nonneg hT.le)
  have hs := bblrGaussianAFETailSummand_summable T σ α t (θ*Real.log T) htpos hR hα
  have hp := bblrGaussianAFETailSummand_norm_le T σ α t (θ*Real.log T) hα
    (B := D*T^(-(A:ℝ))) (by positivity) (fun x hx => hb σ hσ α hα t ht x hx)
  unfold rectangularSmoothGridFrequencyTail
  calc
    _ ≤ ∑' n, ‖bblrGaussianAFETailSummand T σ α t (θ*Real.log T) n‖ :=
      rectangular_smooth_grid_norm_le_tsum_norm _ hs X
    _ ≤ ∑' n, (D*T^(-(A:ℝ)))*bblrGaussianAFEQuadMajorant n :=
      hs.norm.tsum_le_tsum hp (bblrGaussianAFEQuadMajorant_summable.mul_left _)
    _ = (D*S)*T^(-(A:ℝ)) := by rw [tsum_mul_left]; dsimp [S]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT.le (by linarith)) (by positivity)

theorem rectangularFiniteGaussianRemainder_uniform_power_bound
    (K : Set MomentShifts) (δ : ℝ) (hδ : 0<δ)
    (hρ : ∀ σ∈K, ∀ k : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ k‖)
    {ε θ : ℝ} (hε : 0<ε) (hθ : 0<θ) (N : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ α : MomentShifts,
      (∀ j, ‖α j‖≤1/4) → ∀ t∈Icc T (2*T),
      ‖rectangularFiniteGaussianRemainder T σ α t (T^(2+ε)) (θ*Real.log T)‖≤C*T^(-N) := by
  obtain ⟨C₁,hC₁,h₁⟩ := rectangularAFESmoothProductTail_uniform_power_bound K δ hδ hρ hε N
  obtain ⟨C₂,hC₂,h₂⟩ := rectangularSmoothGridFrequencyTail_uniform_power_bound K δ hδ hρ hθ N
  refine ⟨C₁+C₂,add_nonneg hC₁ hC₂,?_⟩
  filter_upwards [h₁,h₂] with T h₁ h₂
  intro σ hσ α hα t ht
  unfold rectangularFiniteGaussianRemainder
  calc
    _ ≤ ‖rectangularAFESmoothProductTail (polarPoleKiller T σ) α t (T^(2+ε))‖+
      ‖rectangularSmoothGridFrequencyTail T σ α t (T^(2+ε)) (θ*Real.log T)‖ := norm_add_le _ _
    _ ≤ C₁*T^(-N)+C₂*T^(-N) := add_le_add (h₁ σ hσ α hα t ht) (h₂ σ hσ α hα t ht _)
    _ = _ := by ring

end
end Sechstmoment
