import Sechstmoment.Numerator.U.Replacement.VStar.DiagonalFiniteGrid

namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 1000000

theorem bblrVStarSelectedGridFrequencyTail_uniform_rapid_bound
    {c ε θ : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 0<ε) (hθ : 0<θ)
    (K : Set MomentShifts) (δ : ℝ) (hδ : 0<δ)
    (hρ : ∀ σ∈K, ∀ k : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ k‖) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ α : MomentShifts,
      (∀ j, ‖α j‖≤1/4) → ∀ t∈Icc T (2*T), ∀ (diagonal : Bool) (u w : ℕ),
      ‖bblrVStarSelectedGridFrequencyTail diagonal c T σ α u w t
        (T^(2+ε)) (θ*Real.log T)‖≤C*T^(-M) := by
  obtain ⟨C,hC,hV⟩ := bblrGaussianVStarTail_uniform_logarithmic_bound hc hc1 hθ K δ hδ hρ (M+3+ε)
  obtain ⟨D,hD,hcard⟩ := rectangular_small_contour_grid_uniform_polynomial_card hε
  refine ⟨C*D,mul_nonneg hC hD,?_⟩
  filter_upwards [hV,hcard,eventually_gt_atTop (1:ℝ)] with T hV hcard hT
  intro σ hσ α hα t ht diagonal u w
  have hTp : 0<T := zero_lt_one.trans hT
  have htp : 0<t := hTp.trans_le ht.1
  have hB : 0≤C*T^(-(M+3+ε)) := by positivity
  have hp (k n : Fin 4 → ℕ) :
      ‖(rectangularAFESmoothWeight k n:ℂ)*
        (if (diagonalQuadRelation (u+1) (w+1) n ↔ diagonal=true)
          then bblrVStarAFESummand (polarPoleKiller T σ) α t n-
            bblrGaussianVStarCoreSummand c T σ α t (θ*Real.log T) n
          else 0)‖≤C*T^(-(M+3+ε)) := by
    by_cases hn : (diagonalQuadRelation (u+1) (w+1) n ↔ diagonal=true)
    · simp only [hn,ite_true]
      have hx : 1≤(positiveQuadProduct n:ℝ) := by
        have hp : 0 < positiveQuadProduct n := by unfold positiveQuadProduct; positivity
        exact_mod_cast hp
      have hb := (bblrVStarAFESummand_sub_core_norm_le hc htp.ne' T σ α hα _ n).trans
        (hV σ hσ t ht _ hx)
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (rectangular_AFE_smooth_weight_nonneg k n)]
      calc
        _ ≤ rectangularAFESmoothWeight k n*(C*T^(-(M+3+ε))) :=
          mul_le_mul_of_nonneg_left hb (rectangular_AFE_smooth_weight_nonneg k n)
        _ ≤ _ := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right
            (rectangular_small_contour_smooth_weight_le_one k n) hB
    · simpa only [hn,ite_false,mul_zero,norm_zero] using hB
  have he : ‖bblrVStarSelectedGridFrequencyTail diagonal c T σ α u w t
      (T^(2+ε)) (θ*Real.log T)‖≤
      (C*T^(-(M+3+ε)))*(∑ k∈rectangularAFEProductScaleGrid (T^(2+ε)),
        ((rectangularAFESmoothBox k).card:ℝ)) := by
    unfold bblrVStarSelectedGridFrequencyTail
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ k∈rectangularAFEProductScaleGrid (T^(2+ε)), ∑ n∈rectangularAFESmoothBox k,
          C*T^(-(M+3+ε)) := by
        apply Finset.sum_le_sum
        intro k _
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n _ => hp k n))
      _ = _ := by
        simp only [Finset.sum_const,nsmul_eq_mul,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  calc
    _ ≤ (C*T^(-(M+3+ε)))*(D*T^(3+ε)) := he.trans (mul_le_mul_of_nonneg_left hcard hB)
    _ = _ := by
      rw [mul_assoc,mul_left_comm (T^(-(M+3+ε))) D,←mul_assoc,←Real.rpow_add hTp]
      congr 1
      ring

theorem bblrVStarSelectedSmoothProductTail_uniform_power_bound (K : Set MomentShifts)
    (δ : ℝ) (hδ : 0<δ)
    (hρ : ∀ σ∈K, ∀ k : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ k‖)
    {ε : ℝ} (hε : 0<ε) (N : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ α : MomentShifts,
      (∀ j, ‖α j‖≤1/4) → ∀ t∈Icc T (2*T), ∀ (diagonal : Bool) (u w : ℕ),
      ‖bblrVStarSelectedSmoothProductTail diagonal (polarPoleKiller T σ) α u w t
        (T^(2+ε))‖≤C*T^(-N) := by
  obtain ⟨C,hC,hb⟩ := bblrGaussianVStarAFESpatialTail_uniform_absolute_power_bound K δ hδ hρ hε N
  refine ⟨C,hC,?_⟩
  filter_upwards [hb,eventually_gt_atTop (0:ℝ)] with T hb hT
  intro σ hσ α hα t ht diagonal u w
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
        (if (diagonalQuadRelation (u+1) (w+1) n ↔ diagonal=true)
          then bblrVStarAFESummand (polarPoleKiller T σ) α t n else 0)‖≤
      ‖if n∉bblrAFEProductBox (T^(2+ε))
        then bblrVStarAFESummand (polarPoleKiller T σ) α t n else 0‖ := by
    by_cases hsel : (diagonalQuadRelation (u+1) (w+1) n ↔ diagonal=true)
    · simp only [hsel,ite_true]
      by_cases hn : n∈bblrAFEProductBox (T^(2+ε))
      · rw [rectangular_AFE_smooth_tail_weight_zero (Real.rpow_pos_of_pos hT (2+ε)) n
          ((bblrAFEProductBox_mem_iff _ n).mp hn)]
        simp [hn]
      · simp only [hn,not_false_eq_true,ite_true]
        have hW := rectangular_AFE_smooth_tail_weight_bounds (T^(2+ε)) n
        rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hW.1]
        simpa using mul_le_mul_of_nonneg_right hW.2 (norm_nonneg _)
    · simp only [hsel,ite_false,mul_zero,norm_zero]
      exact norm_nonneg _
  have hTail := hOutside.norm.of_norm_bounded hpoint
  unfold bblrVStarSelectedSmoothProductTail
  calc
    _ ≤ ∑' n : Fin 4 → ℕ, ‖(rectangularAFESmoothTailWeight (T^(2+ε)) n : ℂ)*
        (if (diagonalQuadRelation (u+1) (w+1) n ↔ diagonal=true)
          then bblrVStarAFESummand (polarPoleKiller T σ) α t n else 0)‖ :=
      norm_tsum_le_tsum_norm hTail.norm
    _ ≤ ∑' n : Fin 4 → ℕ, ‖if n∉bblrAFEProductBox (T^(2+ε))
        then bblrVStarAFESummand (polarPoleKiller T σ) α t n else 0‖ :=
      hTail.norm.tsum_le_tsum hpoint hOutside.norm
    _ ≤ _ := hb σ hσ α hα t ht

theorem bblrVStarSelectedFiniteRemainder_uniform_rapid_bound
    {c ε θ : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 0<ε) (hθ : 0<θ)
    (K : Set MomentShifts) (δ : ℝ) (hδ : 0<δ)
    (hρ : ∀ σ∈K, ∀ k : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ k‖) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ α : MomentShifts,
      (∀ j, ‖α j‖≤1/4) → ∀ t∈Icc T (2*T), ∀ (diagonal : Bool) (u w : ℕ),
      ‖bblrVStarSelectedFiniteRemainder diagonal c T σ α u w t
        (T^(2+ε)) (θ*Real.log T)‖≤C*T^(-M) := by
  obtain ⟨C₀,hC₀,h₀⟩ := bblrVStarSelectedSmoothProductTail_uniform_power_bound K δ hδ hρ hε M
  obtain ⟨C₁,hC₁,h₁⟩ := bblrVStarSelectedGridFrequencyTail_uniform_rapid_bound hc hc1 hε hθ K δ hδ hρ M
  refine ⟨C₀+C₁,add_nonneg hC₀ hC₁,?_⟩
  filter_upwards [h₀,h₁] with T h₀ h₁
  intro σ hσ α hα t ht diagonal u w
  unfold bblrVStarSelectedFiniteRemainder
  calc
    _ ≤ ‖bblrVStarSelectedSmoothProductTail diagonal (polarPoleKiller T σ) α u w t (T^(2+ε))‖+
        ‖bblrVStarSelectedGridFrequencyTail diagonal c T σ α u w t
          (T^(2+ε)) (θ*Real.log T)‖ := norm_add_le _ _
    _ ≤ C₀*T^(-M)+C₁*T^(-M) :=
      add_le_add (h₀ σ hσ α hα t ht diagonal u w) (h₁ σ hσ α hα t ht diagonal u w)
    _ = _ := by ring

end
end Sechstmoment
