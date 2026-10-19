import Sechstmoment.Numerator.U.ZeroModes.Ratio.FourGammaZeroJoin
import Sechstmoment.Numerator.U.ZeroModes.Ratio.GCDVStarCoordinates
import Sechstmoment.Numerator.U.ZeroModes.Ratio.ZeroReplacementMoment

/-! Exact full-height reconstruction of the actual finite seven-dyadic
ratio linear zero moment by the literal retained common-X GCD V* sum.
All signs, good-block selectors, singleton scales and amplifier weights
are the actual ones used by the source estimate. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03ActualRetainedRatioGCDVStarBlock (dual positive : Bool) (Φ : ℝ→ℂ)
    (T s εsource : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ)
    (i : (Fin 3→ℕ)×(Fin 4→ℕ)) : ℂ :=
  let A := rectangularAFESmoothScale (i.1 0)
  let B := rectangularAFESmoothScale (i.1 1)
  let H := rectangularAFESmoothScale (i.1 2)
  let q := phaseActualScales A B H i.2
  if a03ActualRatioSourceGoodBlock T s εsource f g i then
    (T:ℂ)*a03RetainedRatioGCDVStarZeroMode dual Φ T σ α (rectangularGapSign positive) q
      (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B)
  else 0

def a03ActualRetainedRatioGCDVStarFinite (dual : Bool) (Φ : ℝ→ℂ)
    (T a b s u εsource : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∑ positive : Bool,∑ i∈a03ActualSourceBlockGrid (T^a) (T^b)
    (8*T^((a+b)/2+s+u/2)) (T^(2+u)),a03ActualRetainedRatioGCDVStarBlock dual positive Φ T s εsource σ α f g i

def a03ActualRatioSourceLinearZeroFullMoment (dual : Bool) (Φ : ℝ→ℂ)
    (c T a b s u εsource : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫v : ℝ,a03ActualRatioSourceLinearZeroFinite dual Φ c T a b s u εsource v σ α f g

theorem a03ActualRatioSourceLinearZeroBlock_eq_spectral (dual positive : Bool)
    (Φ : ℝ→ℂ) (c T s εsource v : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ)
    (i : (Fin 3→ℕ)×(Fin 4→ℕ)) :
    a03ActualRatioSourceLinearZeroBlock dual positive Φ c T s εsource v σ α f g i=
      if a03ActualRatioSourceGoodBlock T s εsource f g i then
        (T:ℂ)*a03SourceSpectralActualRatioLinearZero dual Φ T c σ α
          (Real.log (rectangularAFESmoothScale (i.2 0)/rectangularAFESmoothScale (i.2 1)))
          (Real.log (rectangularAFESmoothScale (i.2 2)/rectangularAFESmoothScale (i.2 3)))
          ((rectangularAFESmoothScale (i.1 2))/(rectangularAFESmoothScale (i.1 1)*
            (rectangularAFESmoothScale (i.2 2)*rectangularAFESmoothScale (i.2 3))))
          (rectangularGapSign positive) false false
          (phaseActualScales (rectangularAFESmoothScale (i.1 0)) (rectangularAFESmoothScale (i.1 1))
            (rectangularAFESmoothScale (i.1 2)) i.2)
          (phaseActualAmplifierCoefficient T f (rectangularAFESmoothScale (i.1 0)))
          (phaseActualAmplifierCoefficient T g (rectangularAFESmoothScale (i.1 1))) v else 0 := by
  unfold a03ActualRatioSourceLinearZeroBlock
  dsimp only
  by_cases hgood : a03ActualRatioSourceGoodBlock T s εsource f g i
  · simp only [hgood,ite_true]
    unfold a03SourceSpectralActualRatioLinearZero a03EndpointPhysicalUnsortedZeroMode
      a03RatioSourceLinearRawFamilyKernel a03ZeroModeMellinScaleFactor a03SourceMellinScaleFactor
    simp [phaseActualNearTensorData,phasePairSwapScales,a03ZeroModeQuadScales,phaseActualScales,mul_assoc]
    left
    left
    apply Finset.prod_congr rfl
    intro j _
    fin_cases j <;> rfl
  · simp only [hgood,ite_false]

theorem a03ActualRatioSourceLinearZeroBlock_integrable
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T c κ : ℝ} (hT : 1<T) (hL : 1≤Real.log T) (hc : 0<c) (hκ : 0<κ)
    (σ α : MomentShifts) (hroot : ∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    (hα : ∀ j,‖α j‖≤1/4) (dual positive : Bool) (s εsource : ℝ)
    (f g : ℝ→ℝ) (i : (Fin 3→ℕ)×(Fin 4→ℕ)) :
    Integrable (fun v => a03ActualRatioSourceLinearZeroBlock dual positive Φ c T s εsource v σ α f g i) := by
  simp_rw [a03ActualRatioSourceLinearZeroBlock_eq_spectral]
  by_cases hgood : a03ActualRatioSourceGoodBlock T s εsource f g i
  · simp only [hgood,ite_true]
    have hq : ∀j,0<a03ZeroModeQuadScales (phasePairSwapScales false false
        (phaseActualScales (rectangularAFESmoothScale (i.1 0)) (rectangularAFESmoothScale (i.1 1))
          (rectangularAFESmoothScale (i.1 2)) i.2)) j := by
      intro j
      fin_cases j <;> simp [phasePairSwapScales,a03ZeroModeQuadScales,phaseActualScales] <;>
        exact boundaryActual_scale_pos _
    have hi := a03SourceSpectralActualRatioLinearZero_set_integrable hΦ hSupp hT hL hc hκ σ α hroot hα dual
      (Real.log (rectangularAFESmoothScale (i.2 0)/rectangularAFESmoothScale (i.2 1)))
      (Real.log (rectangularAFESmoothScale (i.2 2)/rectangularAFESmoothScale (i.2 3)))
      ((rectangularAFESmoothScale (i.1 2))/(rectangularAFESmoothScale (i.1 1)*
        (rectangularAFESmoothScale (i.2 2)*rectangularAFESmoothScale (i.2 3))))
      (rectangularGapSign positive) false false
      (phaseActualScales (rectangularAFESmoothScale (i.1 0)) (rectangularAFESmoothScale (i.1 1))
        (rectangularAFESmoothScale (i.1 2)) i.2) (boundaryActual_scale_pos _) hq
      (phaseActualAmplifierCoefficient T f (rectangularAFESmoothScale (i.1 0)))
      (phaseActualAmplifierCoefficient T g (rectangularAFESmoothScale (i.1 1))) univ
    simpa only [IntegrableOn,Measure.restrict_univ] using hi.const_mul (T:ℂ)
  · simp only [hgood,ite_false]
    exact integrable_zero _ _ _

theorem a03ActualRatioSourceLinearZeroBlock_full_eq_retained_GCD
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T c κ : ℝ} (hT : 1<T) (hL : 1≤Real.log T) (hc : 0<c) (hκ : 0<κ)
    (σ α : MomentShifts) (hroot : ∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    (hα : ∀ j,‖α j‖≤1/4) (dual positive : Bool) (s εsource : ℝ)
    (f g : ℝ→ℝ) (i : (Fin 3→ℕ)×(Fin 4→ℕ)) :
    (1/(2*Real.pi):ℂ)*(∫v : ℝ,a03ActualRatioSourceLinearZeroBlock dual positive Φ c T s εsource v σ α f g i)=
      a03ActualRetainedRatioGCDVStarBlock dual positive Φ T s εsource σ α f g i := by
  simp_rw [a03ActualRatioSourceLinearZeroBlock_eq_spectral]
  unfold a03ActualRetainedRatioGCDVStarBlock
  dsimp only
  by_cases hgood : a03ActualRatioSourceGoodBlock T s εsource f g i
  · simp only [hgood,ite_true,integral_const_mul]
    rw [show (1/(2*Real.pi):ℂ)*((T:ℂ)*∫v : ℝ,_)=
      (T:ℂ)*((1/(2*Real.pi):ℂ)*∫v : ℝ,_) by ring]
    congr 1
    exact a03_actual_ratio_native_full_eq_retained_GCD_VStar hΦ hSupp hT hL hc hκ σ α hroot hα dual
      (rectangularGapSign positive) _ (boundaryActual_scales_pos _ _ _ i.2
        (boundaryActual_scale_pos _) (boundaryActual_scale_pos _) (boundaryActual_scale_pos _)) _ _
  · simp only [hgood,ite_false,integral_zero,mul_zero]

theorem a03ActualRatioSourceLinearZeroFinite_integrable
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T c κ : ℝ} (hT : 1<T) (hL : 1≤Real.log T) (hc : 0<c) (hκ : 0<κ)
    (σ α : MomentShifts) (hroot : ∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    (hα : ∀ j,‖α j‖≤1/4) (dual : Bool) (a b s u εsource : ℝ) (f g : ℝ→ℝ) :
    Integrable (fun v => a03ActualRatioSourceLinearZeroFinite dual Φ c T a b s u εsource v σ α f g) := by
  unfold a03ActualRatioSourceLinearZeroFinite
  apply integrable_finsetSum
  intro positive _
  apply integrable_finsetSum
  intro i _
  exact a03ActualRatioSourceLinearZeroBlock_integrable hΦ hSupp hT hL hc hκ σ α hroot hα dual positive s εsource f g i

/-- Actual full-height finite seven-grid reconstruction. The restored
source factor T and the four dyadic Mellin powers are consumed exactly by
the native positive-line V* reconstruction before summation. -/
theorem a03_actual_ratio_source_linear_full_moment_eq_retained_GCD
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T c κ : ℝ} (hT : 1<T) (hL : 1≤Real.log T) (hc : 0<c) (hκ : 0<κ)
    (σ α : MomentShifts) (hroot : ∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    (hα : ∀ j,‖α j‖≤1/4) (dual : Bool) (a b s u εsource : ℝ) (f g : ℝ→ℝ) :
    a03ActualRatioSourceLinearZeroFullMoment dual Φ c T a b s u εsource σ α f g=
      a03ActualRetainedRatioGCDVStarFinite dual Φ T a b s u εsource σ α f g := by
  unfold a03ActualRatioSourceLinearZeroFullMoment a03ActualRatioSourceLinearZeroFinite
    a03ActualRetainedRatioGCDVStarFinite
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro positive _
    rw [integral_finsetSum]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact a03ActualRatioSourceLinearZeroBlock_full_eq_retained_GCD hΦ hSupp hT hL hc hκ σ α hroot hα dual positive s εsource f g i
    · intro i _
      exact a03ActualRatioSourceLinearZeroBlock_integrable hΦ hSupp hT hL hc hκ σ α hroot hα dual positive s εsource f g i
  · intro positive _
    apply integrable_finsetSum
    intro i _
    exact a03ActualRatioSourceLinearZeroBlock_integrable hΦ hSupp hT hL hc hκ σ α hroot hα dual positive s εsource f g i

def a03ActualFourRatioLinearZeroFullMoment (dual : Bool) (Φ : ℝ→ℂ)
    (c T a b s u εsource : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∑ m : Bool,∑ n : Bool,a03ActualRatioSourceLinearZeroFullMoment dual Φ c T a b s u εsource σ
    (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g

def a03ActualFourRetainedRatioGCDVStarFinite (dual : Bool) (Φ : ℝ→ℂ)
    (T a b s u εsource : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∑ m : Bool,∑ n : Bool,a03ActualRetainedRatioGCDVStarFinite dual Φ T a b s u εsource σ
    (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g

theorem a03_actual_four_ratio_linear_full_eq_retained_GCD
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T c κ : ℝ} (hT : 1<T) (hL : 1≤Real.log T) (hc : 0<c) (hκ : 0<κ)
    (σ : MomentShifts) (hroot : ∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4) (dual : Bool)
    (a b s u εsource : ℝ) (f g : ℝ→ℝ) :
    a03ActualFourRatioLinearZeroFullMoment dual Φ c T a b s u εsource σ f g=
      a03ActualFourRetainedRatioGCDVStarFinite dual Φ T a b s u εsource σ f g := by
  unfold a03ActualFourRatioLinearZeroFullMoment a03ActualFourRetainedRatioGCDVStarFinite
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  exact a03_actual_ratio_source_linear_full_moment_eq_retained_GCD hΦ hSupp hT hL hc hκ σ _ hroot
    (a03SourceChamberShifts_norm_le_quarter dual σ hσ m n) dual a b s u εsource f g

end
end Sechstmoment
