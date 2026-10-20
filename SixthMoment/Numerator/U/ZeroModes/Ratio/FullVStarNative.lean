import SixthMoment.Numerator.U.ZeroModes.FullVStarNative

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 300000

def a03RatioLeadingBranchProfile (dual : Bool) (Φ : ℝ→ℂ) (T : ℝ) (σ : MomentShifts) : ℝ→ℂ :=
  if dual then a03ProfileProduct Φ (bblrDualLeadingMultiplier T σ) else Φ

theorem a03RatioLeadingBranchProfile_continuous {Φ : ℝ→ℂ} (hΦ : Continuous Φ)
    (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) {T : ℝ} (hT : 0<T) (σ : MomentShifts) (dual : Bool) :
    Continuous (a03RatioLeadingBranchProfile dual Φ T σ) := by
  cases dual
  · exact hΦ
  · exact a03DualLeadingSupportedProfile_continuous hΦ hSupp hT σ

theorem a03RatioLeadingBranchProfile_support (dual : Bool) (Φ : ℝ→ℂ) (T : ℝ) (σ : MomentShifts) :
    tsupport (a03RatioLeadingBranchProfile dual Φ T σ)⊆tsupport Φ := by
  cases dual
  · exact Subset.rfl
  · exact a03_profile_product_tsupport _ _

def a03SourceSpectralActualRatioLinearZero (dual : Bool) (Φ : ℝ→ℂ)
    (T c : ℝ) (σ α : MomentShifts) (tM tN r s : ℝ) (m n : Bool) (q : QuadraticScales)
    (a b : ℕ→ℂ) (w : ℝ) : ℂ :=
  a03ZeroModeMellinScaleFactor (phasePairSwapScales m n q) α ((c:ℂ)+(w:ℂ)*I)*
    a03SixTensorPhysicalZeroMode
      (fun y => a03RatioEuclideanMultiplier (rawMomentShifts T σ) tM tN y*
        a03ZeroModeLinearKernel dual Φ c ⟨T,σ,α,w,r,s⟩ y) m n q a b

def a03PhysicalActualRatioLinearVStarZeroMode (dual : Bool) (Φ : ℝ→ℂ)
    (T : ℝ) (σ α : MomentShifts) (tM tN r s : ℝ) (m n : Bool) (q : QuadraticScales)
    (a b : ℕ→ℂ) : ℂ :=
  a03PhysicalLinearVStarZeroMode (a03RatioLeadingBranchProfile dual Φ T σ) T σ α r s
    (a03RatioEuclideanMultiplier (rawMomentShifts T σ) tM tN) m n q a b

theorem a03SourceSpectralActualRatioLinearZero_eq_native (dual : Bool) (Φ : ℝ→ℂ)
    (T c : ℝ) (σ α : MomentShifts) (tM tN r s : ℝ) (m n : Bool) (q : QuadraticScales)
    (a b : ℕ→ℂ) (w : ℝ) :
    a03SourceSpectralActualRatioLinearZero dual Φ T c σ α tM tN r s m n q a b w=
      a03SourceSpectralNativeLinearZero (a03RatioLeadingBranchProfile dual Φ T σ) T c σ α r s
        (a03RatioEuclideanMultiplier (rawMomentShifts T σ) tM tN) m n q a b w := by
  cases dual <;> rfl

theorem a03ActualRatioMultiplier_norm_le {T κ : ℝ}
    (hT : 1<T) (hL : 1≤Real.log T) (hκ : 0<κ) (σ : MomentShifts)
    (hroot : ∀j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) (tM tN : ℝ)
    (y : A03SixTensorSpace) :
    ‖a03RatioEuclideanMultiplier (rawMomentShifts T σ) tM tN y‖≤
      a03RatioMultiplierDerivativeBudget κ 0*(Real.log T)^8 := by
  simpa only [norm_iteratedFDeriv_zero] using
    a03RatioEuclideanMultiplier_uniform_derivative_bound hT hL hκ σ hroot tM tN 0 y

theorem a03SourceSpectralActualRatioLinearZero_full_eq_VStar
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T c κ : ℝ} (hT : 1<T) (hL : 1≤Real.log T) (hc : 0<c) (hκ : 0<κ)
    (σ α : MomentShifts) (hroot : ∀j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    (hα : ∀ j,‖α j‖≤1/4) (dual : Bool) (tM tN r s : ℝ)
    (m n : Bool) (q : QuadraticScales) (hq : ∀ j,0<q.size j) (a b : ℕ→ℂ) :
    (1/(2*Real.pi):ℂ)*(∫w : ℝ,
      a03SourceSpectralActualRatioLinearZero dual Φ T c σ α tM tN r s m n q a b w)=
      a03PhysicalActualRatioLinearVStarZeroMode dual Φ T σ α tM tN r s m n q a b := by
  simp_rw [a03SourceSpectralActualRatioLinearZero_eq_native]
  exact a03SourceSpectralNativeLinearZero_full_eq_VStar
    (a03RatioLeadingBranchProfile_continuous hΦ hSupp (zero_lt_one.trans hT) σ dual)
    ((a03RatioLeadingBranchProfile_support dual Φ T σ).trans hSupp)
    (zero_lt_one.trans hT) hc σ α hα r s _
    (a03RatioEuclideanMultiplier_contDiff _ _ _).continuous.measurable
    (a03ActualRatioMultiplier_norm_le hT hL hκ σ hroot tM tN) m n q hq a b

theorem a03SourceSpectralActualRatioLinearZero_set_integrable
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T c κ : ℝ} (hT : 1<T) (hL : 1≤Real.log T) (hc : 0<c) (hκ : 0<κ)
    (σ α : MomentShifts) (hroot : ∀j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    (hα : ∀ j,‖α j‖≤1/4) (dual : Bool) (tM tN r s : ℝ)
    (m n : Bool) (q : QuadraticScales) (hM₂ : 0<q.M₂)
    (hq : ∀ j,0<a03ZeroModeQuadScales (phasePairSwapScales m n q) j)
    (a b : ℕ→ℂ) (S : Set ℝ) :
    IntegrableOn (a03SourceSpectralActualRatioLinearZero dual Φ T c σ α tM tN r s m n q a b) S := by
  have he : a03SourceSpectralActualRatioLinearZero dual Φ T c σ α tM tN r s m n q a b=
      a03SourceSpectralNativeLinearZero (a03RatioLeadingBranchProfile dual Φ T σ) T c σ α r s
        (a03RatioEuclideanMultiplier (rawMomentShifts T σ) tM tN) m n q a b :=
    funext (fun w => a03SourceSpectralActualRatioLinearZero_eq_native dual Φ T c σ α tM tN r s m n q a b w)
  rw [he]
  exact a03SourceSpectralNativeLinearZero_set_integrable
    (a03RatioLeadingBranchProfile_continuous hΦ hSupp (zero_lt_one.trans hT) σ dual)
    ((a03RatioLeadingBranchProfile_support dual Φ T σ).trans hSupp)
    (zero_lt_one.trans hT) hc σ α hα r s _
    (a03RatioEuclideanMultiplier_contDiff _ _ _).continuous.measurable
    (a03ActualRatioMultiplier_norm_le hT hL hκ σ hroot tM tN) m n q hM₂ hq a b S

end
end SixthMoment
