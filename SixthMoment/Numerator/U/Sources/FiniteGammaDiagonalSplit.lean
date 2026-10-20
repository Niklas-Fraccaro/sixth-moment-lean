import SixthMoment.Numerator.U.Replacement.ReplacementMomentMellin
import SixthMoment.Numerator.U.Sources.FiniteGammaDiagonalDefinitions

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03ActualFiniteFullMellinGrid (dual : Bool) (c T a b u v : ℝ)
    (f g Φ : ℝ→ℝ) (σ α : MomentShifts) : ℂ :=
  ∑ p∈Finset.range ⌊T^a⌋₊,∑ q∈Finset.range ⌊T^b⌋₊,
    ∑ k∈rectangularAFEProductScaleGrid (T^(2+u)),∑ n∈rectangularAFESmoothBox k,
      (rectangularAFESmoothWeight k n:ℂ)*(∫ t : ℝ,
        rectangularMomentPairWeight T f g Φ p q t*
        (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
        rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I))

def a03ActualFiniteFullGammaMoment (dual : Bool) (c T a b u θ : ℝ)
    (σ : MomentShifts) (f g Φ : ℝ→ℝ) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫ v in Icc (-θ*Real.log T) (θ*Real.log T),
    a03ActualFiniteFullMellinGrid dual c T a b u v f g Φ σ
      (a03SourceShifts dual T σ)

theorem a03ActualFiniteFullMellinGrid_eq_diagonal_and_offdiagonal
    (dual : Bool) (c T a b u v : ℝ) (f g Φ : ℝ→ℝ) (σ α : MomentShifts) :
    a03ActualFiniteFullMellinGrid dual c T a b u v f g Φ σ α=
      a03ActualFiniteDiagonalMellinGrid dual c T a b u v f g Φ σ α+
        ∑ positive : Bool,a03ActualFiniteOffdiagonalMellinGrid dual positive c T a b u v f g Φ σ α := by
  simp only [Fintype.sum_bool]
  unfold a03ActualFiniteFullMellinGrid a03ActualFiniteDiagonalMellinGrid
    a03ActualFiniteOffdiagonalMellinGrid
  simp_rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro n _
  rcases lt_trichotomy ((p+1)*(n 0+1)*(n 1+1)) ((q+1)*(n 2+1)*(n 3+1)) with hn|hn|hn
  · simp [diagonalQuadRelation,rectangularPositiveQuadGap,rectangularNegativeQuadGap,
      hn,ne_of_lt hn,not_lt_of_ge hn.le]
  · simp [diagonalQuadRelation,rectangularPositiveQuadGap,rectangularNegativeQuadGap,hn]
  · simp [diagonalQuadRelation,rectangularPositiveQuadGap,rectangularNegativeQuadGap,
      hn,ne_of_gt hn,not_lt_of_ge hn.le]

theorem a03FiniteGammaWeightedKernel_continuous {c T : ℝ} (hc : 0<c)
    (dual : Bool) (σ α : MomentShifts) (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4)
    (hα : ∀ j,‖α j‖≤1/4) (n : Fin 4→ℕ) :
    Continuous (fun p : ℝ×ℝ =>
      (if dual then bblrDualMultiplier p.2 (rawMomentShifts T σ) else 1)*
      rectangularAFEMellinKernel (polarPoleKiller T σ) α p.2 n ((c:ℂ)+(p.1:ℂ)*I)) := by
  have hk := a03_actual_small_Mellin_kernel_joint_continuous hc T σ α hα n
  cases dual
  · simpa only [Bool.false_eq_true,ite_false,one_mul] using hk
  · exact ((rectangular_dual_multiplier_continuous _ (fun j =>
      lt_of_le_of_lt ((Complex.abs_re_le_norm _).trans (hσ j)) (by norm_num))).comp continuous_snd).mul hk

theorem a03FiniteGammaTerm_mellin_integrableOn {c T : ℝ} (hc : 0<c) (hT : 0<T)
    (dual : Bool) (σ α : MomentShifts) (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4)
    (hα : ∀ j,‖α j‖≤1/4) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (p q : ℕ) (k n : Fin 4→ℕ) (R : ℝ) :
    IntegrableOn (fun v : ℝ => (rectangularAFESmoothWeight k n:ℂ)*(∫ t : ℝ,
      rectangularMomentPairWeight T f g Φ p q t*
      (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
      rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I))) (Icc (-R) R) := by
  have hi := (a03_pair_compact_time_contour_integrable hT f g Φ hΦ p q R _
    (a03FiniteGammaWeightedKernel_continuous hc dual σ α hσ hα n).continuousOn).integral_prod_left
  simpa only [IntegrableOn,mul_assoc] using hi.const_mul (rectangularAFESmoothWeight k n:ℂ)

theorem a03ActualFiniteDiagonalMellinGrid_integrableOn {c T : ℝ} (hc : 0<c) (hT : 0<T)
    (dual : Bool) (a b u R : ℝ) (σ α : MomentShifts)
    (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4) (hα : ∀ j,‖α j‖≤1/4)
    (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    IntegrableOn (fun v : ℝ => a03ActualFiniteDiagonalMellinGrid dual c T a b u v f g Φ σ α)
      (Icc (-R) R) := by
  unfold a03ActualFiniteDiagonalMellinGrid
  apply integrable_finsetSum
  intro p _
  apply integrable_finsetSum
  intro q _
  apply integrable_finsetSum
  intro k _
  apply integrable_finsetSum
  intro n _
  by_cases hsel : diagonalQuadRelation (p+1) (q+1) n
  · simp only [hsel,ite_true]
    exact a03FiniteGammaTerm_mellin_integrableOn hc hT dual σ α hσ hα f g Φ hΦ p q k n R
  · simp only [hsel,ite_false]
    exact integrable_zero _ _ _

theorem a03ActualFiniteOffdiagonalMellinGrid_integrableOn {c T : ℝ} (hc : 0<c) (hT : 0<T)
    (dual positive : Bool) (a b u R : ℝ) (σ α : MomentShifts)
    (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4) (hα : ∀ j,‖α j‖≤1/4)
    (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    IntegrableOn (fun v : ℝ => a03ActualFiniteOffdiagonalMellinGrid dual positive c T a b u v f g Φ σ α)
      (Icc (-R) R) := by
  unfold a03ActualFiniteOffdiagonalMellinGrid
  apply integrable_finsetSum
  intro p _
  apply integrable_finsetSum
  intro q _
  apply integrable_finsetSum
  intro k _
  apply integrable_finsetSum
  intro n _
  by_cases hsel : (if positive then rectangularPositiveQuadGap (p+1) (q+1) n
      else rectangularNegativeQuadGap (p+1) (q+1) n)
  · simp only [hsel,ite_true]
    exact a03FiniteGammaTerm_mellin_integrableOn hc hT dual σ α hσ hα f g Φ hΦ p q k n R
  · simp only [hsel,ite_false]
    exact integrable_zero _ _ _

theorem a03ActualFiniteFullGammaMoment_eq_diagonal_and_offdiagonal {c T : ℝ}
    (hc : 0<c) (hT : 0<T) (dual : Bool) (a b u θ : ℝ) (σ : MomentShifts)
    (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    a03ActualFiniteFullGammaMoment dual c T a b u θ σ f g Φ=
      a03ActualFiniteDiagonalGammaMoment dual c T a b u θ σ f g Φ+
        a03ActualFiniteOffdiagonalGammaMoment dual c T a b u θ σ f g Φ := by
  have hα : ∀ j,‖a03SourceShifts dual T σ j‖≤1/4 := by
    cases dual
    · exact hσ
    · exact bblrSixShifts_norm_le _ hσ 1
  have hd := a03ActualFiniteDiagonalMellinGrid_integrableOn hc hT dual a b u (θ*Real.log T)
    σ _ hσ hα f g Φ hΦ
  have ho := integrable_finsetSum (Finset.univ : Finset Bool) (fun positive _ =>
    a03ActualFiniteOffdiagonalMellinGrid_integrableOn hc hT dual positive a b u (θ*Real.log T)
      σ _ hσ hα f g Φ hΦ)
  unfold a03ActualFiniteFullGammaMoment a03ActualFiniteDiagonalGammaMoment a03ActualFiniteOffdiagonalGammaMoment
  simp_rw [a03ActualFiniteFullMellinGrid_eq_diagonal_and_offdiagonal]
  simp only [neg_mul]
  rw [integral_add hd ho,mul_add]


def a03ActualFiniteGammaBranchIntegrand (dual : Bool) (c T u θ : ℝ)
    (σ : MomentShifts) (f g Φ : ℝ→ℝ) (t : ℝ) : ℂ :=
  rectangularMomentWeight T f g Φ t*
    (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
      rectangularFiniteSmallGaussianCore c T σ (a03SourceShifts dual T σ) t
        (T^(2+u)) (θ*Real.log T)

theorem a03ActualFiniteGammaBranchIntegrand_eq_Mellin (dual : Bool)
    (c T u θ : ℝ) (σ : MomentShifts) (f g Φ : ℝ→ℝ) (t : ℝ) :
    a03ActualFiniteGammaBranchIntegrand dual c T u θ σ f g Φ t=
      rectangularMomentWeight T f g Φ t*
        (∑ k∈rectangularAFEProductScaleGrid (T^(2+u)),∑ n∈rectangularAFESmoothBox k,
          (rectangularAFESmoothWeight k n:ℂ)*(1/(2*Real.pi):ℂ)*
            ∫ v in Icc (-(θ*Real.log T)) (θ*Real.log T),
              (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
                rectangularAFEMellinKernel (polarPoleKiller T σ) (a03SourceShifts dual T σ)
                  t n ((c:ℂ)+(v:ℂ)*I)) := by
  unfold a03ActualFiniteGammaBranchIntegrand rectangularFiniteSmallGaussianCore
  simp_rw [rectangular_actual_small_Gaussian_core_summand_Mellin,integral_const_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem a03ActualFiniteGammaBranchIntegrand_integrable {c T : ℝ} (hc : 0<c) (hT : 1<T)
    (dual : Bool) (a b u θ : ℝ) (σ : MomentShifts)
    (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4) (f g Φ : ℝ→ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) :
    Integrable (a03ActualFiniteGammaBranchIntegrand dual c T u θ σ f g Φ) := by
  have hα : ∀ j,‖a03SourceShifts dual T σ j‖≤1/4 := by
    cases dual
    · exact hσ
    · exact bblrSixShifts_norm_le _ hσ 1
  have hW := rectangular_moment_weight_continuous hT a b f g Φ
    (rectangular_supported_profile_zero_above f hf) (rectangular_supported_profile_zero_above g hg) hΦ
  have hs (t : ℝ) (ht : t∉Icc T (2*T)) : rectangularMomentWeight T f g Φ t=0 := by
    unfold rectangularMomentWeight
    have hPhi : Φ (t/T)=0 := by
      by_contra hn
      have hs : t/T∈tsupport Φ := subset_tsupport Φ (by simpa only [Function.mem_support] using hn)
      have hh := hΦ.2 hs
      exact ht ⟨by simpa using (le_div_iff₀ (zero_lt_one.trans hT)).mp hh.1,
        (div_le_iff₀ (zero_lt_one.trans hT)).mp hh.2⟩
    simp only [hPhi,Complex.ofReal_zero,zero_mul]
  change Integrable (fun t : ℝ => a03ActualFiniteGammaBranchIntegrand dual c T u θ σ f g Φ t)
  simp_rw [a03ActualFiniteGammaBranchIntegrand_eq_Mellin,Finset.mul_sum]
  apply integrable_finsetSum
  intro k _
  apply integrable_finsetSum
  intro n _
  have hi := (a03_compact_time_contour_time_integrable _ hW hs (θ*Real.log T) _
    (a03FiniteGammaWeightedKernel_continuous hc dual σ _ hσ hα n).continuousOn).const_mul
      ((rectangularAFESmoothWeight k n:ℂ)*(1/(2*Real.pi):ℂ))
  convert hi using 1
  funext t
  ring

theorem a03ActualFiniteFullGammaMoment_eq_time {c T : ℝ} (hc : 0<c) (hT : 1<T)
    (dual : Bool) (a b u θ : ℝ) (σ : MomentShifts)
    (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4) (f g Φ : ℝ→ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) :
    (∫ t : ℝ,a03ActualFiniteGammaBranchIntegrand dual c T u θ σ f g Φ t)=
      a03ActualFiniteFullGammaMoment dual c T a b u θ σ f g Φ := by
  have hα : ∀ j,‖a03SourceShifts dual T σ j‖≤1/4 := by
    cases dual
    · exact hσ
    · exact bblrSixShifts_norm_le _ hσ 1
  simp_rw [a03ActualFiniteGammaBranchIntegrand_eq_Mellin]
  have he := a03_actual_finite_time_contour_fubini hT a b (T^(2+u)) (θ*Real.log T)
    f g Φ hf hg hΦ _ (fun n =>
      (a03FiniteGammaWeightedKernel_continuous hc dual σ _ hσ hα n).continuousOn)
  simpa only [a03ActualFiniteFullGammaMoment,a03ActualFiniteFullMellinGrid,mul_assoc,neg_mul] using he

theorem rectangularFiniteSmallGaussianGridMoment_eq_diagonal_and_offdiagonal {c T : ℝ}
    (hc : 0<c) (hT : 1<T) (a b u θ : ℝ) (σ : MomentShifts)
    (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4) (f g Φ : ℝ→ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) :
    rectangularFiniteSmallGaussianGridMoment c T σ f g Φ (T^(2+u)) (θ*Real.log T)=
      (a03ActualFiniteDiagonalGammaMoment false c T a b u θ σ f g Φ+
        a03ActualFiniteOffdiagonalGammaMoment false c T a b u θ σ f g Φ)+
      (a03ActualFiniteDiagonalGammaMoment true c T a b u θ σ f g Φ+
        a03ActualFiniteOffdiagonalGammaMoment true c T a b u θ σ f g Φ) := by
  have he : rectangularFiniteSmallGaussianGridIntegrand c T σ f g Φ (T^(2+u)) (θ*Real.log T)=
      (fun t : ℝ => a03ActualFiniteGammaBranchIntegrand false c T u θ σ f g Φ t)+
        (fun t : ℝ => a03ActualFiniteGammaBranchIntegrand true c T u θ σ f g Φ t) := by
    funext t
    simp only [rectangularFiniteSmallGaussianGridIntegrand,a03ActualFiniteGammaBranchIntegrand,
      a03SourceShifts,Bool.false_eq_true,ite_false,ite_true,Pi.add_apply,mul_one]
    ring
  unfold rectangularFiniteSmallGaussianGridMoment
  rw [he]
  simp only [Pi.add_apply]
  rw [integral_add
    (a03ActualFiniteGammaBranchIntegrand_integrable hc hT false a b u θ σ hσ f g Φ hf hg hΦ)
    (a03ActualFiniteGammaBranchIntegrand_integrable hc hT true a b u θ σ hσ f g Φ hf hg hΦ)]
  rw [a03ActualFiniteFullGammaMoment_eq_time hc hT false a b u θ σ hσ f g Φ hf hg hΦ,
    a03ActualFiniteFullGammaMoment_eq_time hc hT true a b u θ σ hσ f g Φ hf hg hΦ,
    a03ActualFiniteFullGammaMoment_eq_diagonal_and_offdiagonal hc (zero_lt_one.trans hT) false a b u θ σ hσ f g Φ hΦ,
    a03ActualFiniteFullGammaMoment_eq_diagonal_and_offdiagonal hc (zero_lt_one.trans hT) true a b u θ σ hσ f g Φ hΦ]

end
end SixthMoment
