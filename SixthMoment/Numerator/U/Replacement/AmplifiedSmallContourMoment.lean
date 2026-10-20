import SixthMoment.Numerator.U.Separation.AmplifiedFiniteGaussianGrid
import SixthMoment.Numerator.U.Separation.SmallContour.GridRapid
import SixthMoment.Numerator.U.Separation.TimeFarContourBudget

namespace SixthMoment
open Complex Source Real MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def rectangularFiniteSmallGaussianGridIntegrand (c T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ → ℝ) (X R t : ℝ) : ℂ :=
  rectangularMomentWeight T f g Φ t*
    (rectangularFiniteSmallGaussianCore c T σ (rawMomentShifts T σ) t X R+
      bblrDualMultiplier t (rawMomentShifts T σ)*
        rectangularFiniteSmallGaussianCore c T σ
          (bblrSixShifts (rawMomentShifts T σ) 1) t X R)

def rectangularFiniteSmallGaussianGridMoment (c T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ → ℝ) (X R : ℝ) : ℂ :=
  ∫ t : ℝ, rectangularFiniteSmallGaussianGridIntegrand c T σ f g Φ X R t

def rectangularSmallContourCombinedError (c T : ℝ) (σ : MomentShifts)
    (X R t : ℝ) : ℂ :=
  (rectangularFiniteGaussianCore T σ (rawMomentShifts T σ) t X R-
    rectangularFiniteSmallGaussianCore c T σ (rawMomentShifts T σ) t X R)+
    bblrDualMultiplier t (rawMomentShifts T σ)*
      (rectangularFiniteGaussianCore T σ (bblrSixShifts (rawMomentShifts T σ) 1) t X R-
        rectangularFiniteSmallGaussianCore c T σ
          (bblrSixShifts (rawMomentShifts T σ) 1) t X R)

theorem rectangularFiniteSmallGaussianCore_time_stronglyMeasurable
    {c : ℝ} (hc : 0<c) (T : ℝ) (σ α : MomentShifts)
    (hα : ∀ j, ‖α j‖≤1/4) (X R : ℝ) :
    StronglyMeasurable (fun t : ℝ => rectangularFiniteSmallGaussianCore c T σ α t X R) := by
  have hi (n : Fin 4 → ℕ) : StronglyMeasurable (fun t : ℝ =>
      ∫ v in Icc (-R) R,
        rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)) :=
    (a03_actual_small_Mellin_kernel_joint_continuous hc T σ α hα n).stronglyMeasurable.integral_prod_left'
  have he : (fun t : ℝ => rectangularFiniteSmallGaussianCore c T σ α t X R)=
      ∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
        fun t : ℝ => (rectangularAFESmoothWeight k n:ℂ)*(1/(2*Real.pi):ℂ)*
          ∫ v in Icc (-R) R,
            rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I) := by
    funext t
    simp only [Finset.sum_apply,rectangularFiniteSmallGaussianCore,
      rectangular_actual_small_Gaussian_core_summand_Mellin,mul_assoc]
  rw [he]
  apply Finset.stronglyMeasurable_sum
  intro k _
  apply Finset.stronglyMeasurable_sum
  intro n _
  exact (hi n).const_mul _

theorem rectangularFiniteSmallGaussianCore_one_eq (T : ℝ) (σ α : MomentShifts)
    (t X R : ℝ) :
    rectangularFiniteSmallGaussianCore 1 T σ α t X R=rectangularFiniteGaussianCore T σ α t X R := by
  rfl

theorem rectangularSmallContourCombinedError_stronglyMeasurable
    {c : ℝ} (hc : 0<c) (T : ℝ) (σ : MomentShifts)
    (hα : ∀ j, ‖rawMomentShifts T σ j‖≤1/4) (X R : ℝ) :
    StronglyMeasurable (rectangularSmallContourCombinedError c T σ X R) := by
  have hd : ∀ j, ‖bblrSixShifts (rawMomentShifts T σ) 1 j‖≤1/4 := by
    intro j
    fin_cases j <;> simp [bblrSixShifts] <;>
      first | simpa using hα 0 | simpa using hα 1 | simpa using hα 2 | simpa using hα 3
  have hb (α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) :
      StronglyMeasurable (fun t : ℝ => rectangularFiniteGaussianCore T σ α t X R) := by
    simpa only [← rectangularFiniteSmallGaussianCore_one_eq] using
      rectangularFiniteSmallGaussianCore_time_stronglyMeasurable zero_lt_one T σ α hα X R
  have hs : ∀ j, |(rawMomentShifts T σ j).re|<1/2 := fun j =>
    ((Complex.abs_re_le_norm _).trans (hα j)).trans_lt (by norm_num)
  exact ((hb _ hα).sub (rectangularFiniteSmallGaussianCore_time_stronglyMeasurable hc T σ _ hα X R)).add
    ((rectangular_dual_multiplier_continuous _ hs).stronglyMeasurable.mul
      ((hb _ hd).sub (rectangularFiniteSmallGaussianCore_time_stronglyMeasurable hc T σ _ hd X R)))

theorem rectangularSmallContourCombinedError_uniform_rapid
    {c η θ : ℝ} (hc : 0<c) (hc1 : c≤1) (hη : 0<η) (hθ : 0<θ)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ t∈Icc T (2*T),
      ‖rectangularSmallContourCombinedError c T σ (T^(2+η)) (θ*Real.log T) t‖≤C*T^(-M) := by
  obtain ⟨C,hC,hcT⟩ := rectangular_actual_finite_small_contour_uniform_rapid_error
    hc hc1 hη hθ K δ hδ hroot M
  obtain ⟨D,hD,hdT⟩ := bblrDualMultiplier_uniform_normalized_bound K hK
  refine ⟨C*(1+D),by positivity,?_⟩
  filter_upwards [hcT,hdT,compactNormalizedShifts_eventually_norm_small K hK (1/4)
    (by norm_num),eventually_gt_atTop (0:ℝ)] with T hcT hdT hs hT
  intro σ hσ t ht
  have hα := hs σ hσ
  have hd : ∀ j, ‖bblrSixShifts (rawMomentShifts T σ) 1 j‖≤1/4 := by
    intro j
    fin_cases j <;> simp [bblrSixShifts] <;>
      first | simpa using hα 0 | simpa using hα 1 | simpa using hα 2 | simpa using hα 3
  unfold rectangularSmallContourCombinedError
  calc
    _≤‖rectangularFiniteGaussianCore T σ (rawMomentShifts T σ) t (T^(2+η)) (θ*Real.log T)-
      rectangularFiniteSmallGaussianCore c T σ (rawMomentShifts T σ) t (T^(2+η)) (θ*Real.log T)‖+
      ‖bblrDualMultiplier t (rawMomentShifts T σ)*
        (rectangularFiniteGaussianCore T σ (bblrSixShifts (rawMomentShifts T σ) 1) t (T^(2+η)) (θ*Real.log T)-
          rectangularFiniteSmallGaussianCore c T σ (bblrSixShifts (rawMomentShifts T σ) 1) t (T^(2+η)) (θ*Real.log T))‖ := norm_add_le _ _
    _≤C*T^(-M)+D*(C*T^(-M)) := by
      rw [norm_mul]
      gcongr
      · exact hcT σ hσ _ hα t ht
      · exact hdT σ hσ t ht
      · exact hcT σ hσ _ hd t ht
    _=C*(1+D)*T^(-M) := by ring

theorem rectangularSmallContourMomentError_uniform_rapid
    {c η θ : ℝ} (hc : 0<c) (hc1 : c≤1) (hη : 0<η) (hθ : 0<θ)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖)
    (a b : ℝ) (f g Φ : ℝ → ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K,
      Integrable (fun t : ℝ => rectangularMomentWeight T f g Φ t*
        rectangularSmallContourCombinedError c T σ (T^(2+η)) (θ*Real.log T) t) ∧
      ‖rectangularAmplifiedError T f g Φ
        (rectangularSmallContourCombinedError c T σ (T^(2+η)) (θ*Real.log T))‖≤C*T^(-M) := by
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgb⟩ := rectangular_supported_profile_bounded g hg
  obtain ⟨P,hP,hΦb⟩ := rectangular_supported_weight_bounded Φ hΦ
  obtain ⟨C,hC,hb⟩ := rectangularSmallContourCombinedError_uniform_rapid
    hc hc1 hη hθ K hK δ hδ hroot (1+a+b+M)
  refine ⟨P*F*G*C,by positivity,?_⟩
  filter_upwards [hb,compactNormalizedShifts_eventually_norm_small K hK (1/4)
    (by norm_num),eventually_gt_atTop (1:ℝ)] with T hb hs hT
  intro σ hσ
  have hfs := rectangular_supported_profile_zero_above f hf
  have hgs := rectangular_supported_profile_zero_above g hg
  refine ⟨rectangular_amplified_error_integrable hT hF hG hP hC a b f g Φ _ hfs hgs
    hfb hgb hΦ hΦb (rectangularSmallContourCombinedError_stronglyMeasurable hc T σ (hs σ hσ) _ _)
      (hb σ hσ),?_⟩
  have he := rectangular_amplified_error_norm_le hT hF hG hP hC a b f g Φ _ hfs hgs
    hfb hgb hΦ hΦb (hb σ hσ)
  convert he using 1
  congr 1
  ring

theorem rectangularFiniteSmallGaussianGridMoment_uniform_actual_error
    (hsource : BBLRv1FixedApproximateFEInput)
    {c η θ : ℝ} (hc : 0<c) (hc1 : c≤1) (hη : 0<η) (hθ : 0<θ)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖)
    (a b : ℝ) (f g Φ : ℝ → ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K,
      Integrable (rectangularFiniteSmallGaussianGridIntegrand c T σ f g Φ (T^(2+η)) (θ*Real.log T)) ∧
      ‖twistedFourthMoment T (rawMomentShifts T σ) f g Φ-
        rectangularFiniteSmallGaussianGridMoment c T σ f g Φ (T^(2+η)) (θ*Real.log T)‖≤C*T^(-M) := by
  obtain ⟨A,hA,haT⟩ := rectangularFiniteGaussianGridMoment_uniform_actual_error
    hsource K hK δ hδ hroot hη hθ a b f g Φ hf hg hΦ M
  obtain ⟨B,hB,hbT⟩ := rectangularSmallContourMomentError_uniform_rapid
    hc hc1 hη hθ K hK δ hδ hroot a b f g Φ hf hg hΦ M
  have hr := rectangularFiniteGaussianGridMoment_actual_reconstruction
    K hK δ hδ hroot hη hθ a b f g Φ hf hg hΦ
  refine ⟨A+B,add_nonneg hA hB,?_⟩
  filter_upwards [haT,hbT,hr] with T haT hbT hr
  intro σ hσ
  have he : rectangularFiniteSmallGaussianGridIntegrand c T σ f g Φ (T^(2+η)) (θ*Real.log T)=
      fun t : ℝ => rectangularFiniteGaussianGridIntegrand T σ f g Φ (T^(2+η)) (θ*Real.log T) t-
        rectangularMomentWeight T f g Φ t*
          rectangularSmallContourCombinedError c T σ (T^(2+η)) (θ*Real.log T) t := by
    funext t
    unfold rectangularFiniteSmallGaussianGridIntegrand rectangularFiniteGaussianGridIntegrand
      rectangularSmallContourCombinedError
    ring
  have hi := (hr σ hσ).1
  have hE := (hbT σ hσ).1
  refine ⟨by rw [he]; exact hi.sub hE,?_⟩
  have hm : rectangularFiniteSmallGaussianGridMoment c T σ f g Φ (T^(2+η)) (θ*Real.log T)=
      rectangularFiniteGaussianGridMoment T σ f g Φ (T^(2+η)) (θ*Real.log T)-
        rectangularAmplifiedError T f g Φ
          (rectangularSmallContourCombinedError c T σ (T^(2+η)) (θ*Real.log T)) := by
    unfold rectangularFiniteSmallGaussianGridMoment
    rw [he,integral_sub hi hE]
    rfl
  rw [hm,sub_sub_eq_add_sub,add_sub_right_comm]
  calc
    _≤‖twistedFourthMoment T (rawMomentShifts T σ) f g Φ-
        rectangularFiniteGaussianGridMoment T σ f g Φ (T^(2+η)) (θ*Real.log T)‖+
      ‖rectangularAmplifiedError T f g Φ
        (rectangularSmallContourCombinedError c T σ (T^(2+η)) (θ*Real.log T))‖ := norm_add_le _ _
    _≤A*T^(-M)+B*T^(-M) := add_le_add (haT σ hσ) (hbT σ hσ).2
    _=(A+B)*T^(-M) := by ring

end
end SixthMoment
