import Sechstmoment.Denominator.Balanced.CauchyIntegration
import Sechstmoment.Denominator.Balanced.GaussianPhysicalTimeMean

/-! The direct and pure-power dual sharp D01 endpoints combine into the
actual centered nine-edge exponential integral. Profile caps prove every
required edge and image-measure integrability statement. The physical
Gaussian means reach this endpoint through the proved moving-cut limit. -/

namespace Sechstmoment
open MeasureTheory Filter Set Complex
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 0

def d02BalancedDirectShift (σ : Fin 2 → ℂ) : PolarShiftSpace :=
  (![σ 0,0,0],![σ 1,0,0])

def d02BalancedDualShift (σ : Fin 2 → ℂ) : PolarShiftSpace :=
  (![-σ 1,0,0],![-σ 0,0,0])

theorem d02BalancedDirectShift_weight (σ : Fin 2 → ℂ) (y : D01LogSpace) :
    d01ComplexLaplaceWeight (d02BalancedDirectShift σ) y =
      Complex.exp (-(σ 0*(y.1 0:ℂ)+σ 1*(y.2 0:ℂ))) := by
  simp [d02BalancedDirectShift,d01ComplexLaplaceWeight,Fin.sum_univ_three]

theorem d02BalancedDualShift_weight (σ : Fin 2 → ℂ) (y : D01LogSpace) :
    d01ComplexLaplaceWeight (d02BalancedDualShift σ) y =
      Complex.exp (σ 1*(y.1 0:ℂ)+σ 0*(y.2 0:ℂ)) := by
  simp [d02BalancedDualShift,d01ComplexLaplaceWeight,Fin.sum_univ_three]
  congr 1
  ring

theorem d02BalancedDirectDual_weight (σ : Fin 2 → ℂ) (y : D01LogSpace) :
    Complex.exp ((σ 0+σ 1)/2) *
      (d01ComplexLaplaceWeight (d02BalancedDirectShift σ) y+
        Complex.exp (-(σ 0+σ 1))*d01ComplexLaplaceWeight (d02BalancedDualShift σ) y) =
      d02BalancedLogExponentialWeight σ y := by
  rw [d02BalancedDirectShift_weight,d02BalancedDualShift_weight,mul_add]
  simp_rw [← Complex.exp_add]
  unfold d02BalancedLogExponentialWeight
  congr 1 <;> congr 1 <;> ring

theorem d02BalancedFourProfile_rowColumnSums (ρ : Fin 4 → ℝ → ℝ) (x : D01EdgeSpace) :
    d02FourProfileProduct (fun i t => (ρ i t:ℂ)) (d01RowColumnSums x) =
      (d02BalancedEdgeProfile ρ x:ℂ) := by
  simp [d02FourProfileProduct,d02BalancedEdgeProfile,d02BalancedProfileCoordinates,
    Fin.prod_univ_four]

theorem d02BalancedSharpWeight_indicator (ρ : Fin 4 → ℝ → ℝ)
    (w : D01LogSpace → ℂ) (x : D01EdgeSpace) :
    d01NonnegativeOrthant.indicator (fun x => w (d01RowColumnSums x)*
      d02SharpLogTest (d02FourProfileProduct (fun i t => (ρ i t:ℂ)))
        (d01RowColumnSums x)) x = d02BalancedWeightedEdgeIntegrand ρ w x := by
  by_cases hx : x∈d01NonnegativeOrthant
  · rw [indicator_of_mem hx]
    by_cases hc : d02ZetaLogSum (d01RowColumnSums x)≤1
    · have hs : d01RowColumnSums x∈d02SharpLogRegion := hc
      have he : x∈d02BalancedEdgeCut := ⟨hx,hc⟩
      rw [d02SharpLogTest,indicator_of_mem hs,d02BalancedWeightedEdgeIntegrand,
        indicator_of_mem he,d02BalancedFourProfile_rowColumnSums]
      exact mul_comm _ _
    · have hs : d01RowColumnSums x∉d02SharpLogRegion := hc
      have he : x∉d02BalancedEdgeCut := fun h => hc h.2
      rw [d02SharpLogTest,indicator_of_notMem hs,d02BalancedWeightedEdgeIntegrand,
        indicator_of_notMem he,mul_zero]
  · have he : x∉d02BalancedEdgeCut := fun h => hx h.1
    rw [indicator_of_notMem hx,d02BalancedWeightedEdgeIntegrand,indicator_of_notMem he]

theorem d02BalancedSharpWeight_edgeIntegral (ρ : Fin 4 → ℝ → ℝ)
    (w : D01LogSpace → ℂ) :
    (∫ x : D01EdgeSpace, w (d01RowColumnSums x)*
      d02SharpLogTest (d02FourProfileProduct (fun i t => (ρ i t:ℂ)))
        (d01RowColumnSums x) ∂volume.restrict d01NonnegativeOrthant) =
      ∫ x : D01EdgeSpace, d02BalancedWeightedEdgeIntegrand ρ w x := by
  rw [← integral_indicator d01NonnegativeOrthant_measurable]
  exact integral_congr_ae (ae_of_all _ (d02BalancedSharpWeight_indicator ρ w))

theorem d02BalancedSharpWeight_edgeIntegrable
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ) (w : D01LogSpace → ℂ)
    (hρc : ∀ i, Continuous (ρ i))
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i)) (hw : Continuous w) :
    Integrable (fun x : D01EdgeSpace => w (d01RowColumnSums x)*
      d02SharpLogTest (d02FourProfileProduct (fun i t => (ρ i t:ℂ)))
        (d01RowColumnSums x)) d01EdgeMeasure := by
  have hi := d02BalancedWeightedEdgeIntegrand_integrable ρ A w hρc hρcap hw
  have hi' : Integrable (d01NonnegativeOrthant.indicator (fun x : D01EdgeSpace =>
      w (d01RowColumnSums x)*
        d02SharpLogTest (d02FourProfileProduct (fun i t => (ρ i t:ℂ)))
          (d01RowColumnSums x))) :=
    hi.congr (ae_of_all _ (fun x => (d02BalancedSharpWeight_indicator ρ w x).symm))
  exact (integrable_indicator_iff d01NonnegativeOrthant_measurable).1 hi'

theorem d02BalancedSharpWeight_stronglyMeasurable
    (ρ : Fin 4 → ℝ → ℝ) (w : D01LogSpace → ℂ)
    (hρc : ∀ i, Continuous (ρ i)) (hw : Continuous w) :
    StronglyMeasurable (fun y => w y*
      d02SharpLogTest (d02FourProfileProduct (fun i t => (ρ i t:ℂ))) y) :=
  hw.stronglyMeasurable.mul
    ((d02FourProfileProduct_continuous (fun i t => (ρ i t:ℂ))
      (fun i => Complex.continuous_ofReal.comp (hρc i))).stronglyMeasurable.indicator
        d02SharpLogRegion_measurable)

theorem d02BalancedSharpWeight_limitIntegrable
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ) (w : D01LogSpace → ℂ)
    (hρc : ∀ i, Continuous (ρ i))
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i)) (hw : Continuous w) :
    Integrable (fun y => w y*
      d02SharpLogTest (d02FourProfileProduct (fun i t => (ρ i t:ℂ))) y) d01LimitMeasure := by
  unfold d01LimitMeasure
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  apply (integrable_map_measure
    (d02BalancedSharpWeight_stronglyMeasurable ρ w hρc hw).aestronglyMeasurable
    d01RowColumnSums_continuous.measurable.aemeasurable).mpr
  simpa only [Function.comp_def] using
    d02BalancedSharpWeight_edgeIntegrable ρ A w hρc hρcap hw

theorem d02BalancedSharpWeight_limitIntegral
    (ρ : Fin 4 → ℝ → ℝ) (w : D01LogSpace → ℂ)
    (hρc : ∀ i, Continuous (ρ i)) (hw : Continuous w) :
    (∫ y, w y*d02SharpLogTest (d02FourProfileProduct (fun i t => (ρ i t:ℂ))) y
      ∂d01LimitMeasure) =
      (arithmeticFactor:ℂ)*(∫ x : D01EdgeSpace, d02BalancedWeightedEdgeIntegrand ρ w x) := by
  rw [d01LimitMeasure_integral (d02BalancedSharpWeight_stronglyMeasurable ρ w hρc hw),
    d01EdgeMeasure,d02BalancedSharpWeight_edgeIntegral]
  exact Complex.real_smul

/-- This equality combines the direct and dual endpoint integrals only
after both actual sharp edge integrands have been proved integrable. -/
theorem d02BalancedDirectDual_edgeIntegral
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ) (σ : Fin 2 → ℂ)
    (hρc : ∀ i, Continuous (ρ i))
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i)) :
    Complex.exp ((σ 0+σ 1)/2)*
      ((∫ x : D01EdgeSpace, d02BalancedWeightedEdgeIntegrand ρ
        (d01ComplexLaplaceWeight (d02BalancedDirectShift σ)) x)+
        Complex.exp (-(σ 0+σ 1))*(∫ x : D01EdgeSpace, d02BalancedWeightedEdgeIntegrand ρ
          (d01ComplexLaplaceWeight (d02BalancedDualShift σ)) x)) =
      d02BalancedShiftedEdgeIntegral ρ σ := by
  have h₀ := d02BalancedWeightedEdgeIntegrand_integrable ρ A _ hρc hρcap
    (d01ComplexLaplaceWeight_continuous (d02BalancedDirectShift σ))
  have h₁ := d02BalancedWeightedEdgeIntegrand_integrable ρ A _ hρc hρcap
    (d01ComplexLaplaceWeight_continuous (d02BalancedDualShift σ))
  rw [← integral_const_mul (Complex.exp (-(σ 0+σ 1))),
    ← integral_add h₀ (h₁.const_mul _),← integral_const_mul]
  unfold d02BalancedShiftedEdgeIntegral
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x∈d02BalancedEdgeCut
  · simp only [d02BalancedWeightedEdgeIntegrand,indicator_of_mem hx]
    calc
      _ = (d02BalancedEdgeProfile ρ x:ℂ)*
          (Complex.exp ((σ 0+σ 1)/2)*
            (d01ComplexLaplaceWeight (d02BalancedDirectShift σ) (d01RowColumnSums x)+
              Complex.exp (-(σ 0+σ 1))*
                d01ComplexLaplaceWeight (d02BalancedDualShift σ) (d01RowColumnSums x))) := by ring
      _ = _ := by rw [d02BalancedDirectDual_weight]
  · simp [d02BalancedWeightedEdgeIntegrand,indicator_of_notMem hx]

theorem d02BalancedDirectDual_sharpEndpoint
    (c : ℂ) (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ) (σ : Fin 2 → ℂ)
    (hρc : ∀ i, Continuous (ρ i))
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i)) :
    Complex.exp ((σ 0+σ 1)/2)*
      (c*(∫ x : D01EdgeSpace, d01ComplexLaplaceWeight (d02BalancedDirectShift σ)
        (d01RowColumnSums x)*
          d02SharpLogTest (d02FourProfileProduct (fun i t => (ρ i t:ℂ)))
            (d01RowColumnSums x) ∂volume.restrict d01NonnegativeOrthant)+
        Complex.exp (-(σ 0+σ 1))*(c*(∫ x : D01EdgeSpace,
          d01ComplexLaplaceWeight (d02BalancedDualShift σ) (d01RowColumnSums x)*
            d02SharpLogTest (d02FourProfileProduct (fun i t => (ρ i t:ℂ)))
              (d01RowColumnSums x) ∂volume.restrict d01NonnegativeOrthant))) =
      c*d02BalancedShiftedEdgeIntegral ρ σ := by
  rw [d02BalancedSharpWeight_edgeIntegral,d02BalancedSharpWeight_edgeIntegral]
  calc
    _ = c*(Complex.exp ((σ 0+σ 1)/2)*
      ((∫ x : D01EdgeSpace, d02BalancedWeightedEdgeIntegrand ρ
        (d01ComplexLaplaceWeight (d02BalancedDirectShift σ)) x)+
        Complex.exp (-(σ 0+σ 1))*(∫ x : D01EdgeSpace, d02BalancedWeightedEdgeIntegrand ρ
          (d01ComplexLaplaceWeight (d02BalancedDualShift σ)) x))) := by ring
    _ = _ := by rw [d02BalancedDirectDual_edgeIntegral ρ A σ hρc hρcap]

theorem d02BalancedDirectDual_limitMeasureEndpoint
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ) (σ : Fin 2 → ℂ)
    (hρc : ∀ i, Continuous (ρ i))
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i)) :
    Complex.exp ((σ 0+σ 1)/2)*
      ((∫ y, d01ComplexLaplaceWeight (d02BalancedDirectShift σ) y*
        d02SharpLogTest (d02FourProfileProduct (fun i t => (ρ i t:ℂ))) y ∂d01LimitMeasure)+
        Complex.exp (-(σ 0+σ 1))*(∫ y, d01ComplexLaplaceWeight (d02BalancedDualShift σ) y*
          d02SharpLogTest (d02FourProfileProduct (fun i t => (ρ i t:ℂ))) y ∂d01LimitMeasure)) =
      (arithmeticFactor:ℂ)*d02BalancedShiftedEdgeIntegral ρ σ := by
  rw [d01LimitMeasure_integral (d02BalancedSharpWeight_stronglyMeasurable ρ _ hρc
    (d01ComplexLaplaceWeight_continuous (d02BalancedDirectShift σ))),
    d01LimitMeasure_integral (d02BalancedSharpWeight_stronglyMeasurable ρ _ hρc
      (d01ComplexLaplaceWeight_continuous (d02BalancedDualShift σ)))]
  simp only [d01EdgeMeasure,Complex.real_smul]
  exact d02BalancedDirectDual_sharpEndpoint (arithmeticFactor:ℂ) ρ A σ hρc hρcap

private theorem d02BalancedHeightMass_comm (Φ : ℝ → ℝ) :
    ((∫ τ : ℝ, Φ τ : ℝ):ℂ)*(arithmeticFactor:ℂ) =
      ((arithmeticFactor*(∫ τ : ℝ, Φ τ):ℝ):ℂ) := by
  push_cast
  ring

theorem d02BalancedShiftedPhysicalHeightMean_limit
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ) (σ : Fin 2 → ℂ) (Φ : ℝ → ℝ)
    (hρc : ∀ i, Continuous (ρ i))
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i))
    (hΦc : Continuous Φ) (hΦs : tsupport Φ⊆Icc (1:ℝ) 2) :
    Tendsto (fun T : ℝ => Complex.exp ((σ 0+σ 1)/2)*
      (d02GaussianDiagonalPhysicalHeightMean T (fun i t => (ρ i t:ℂ))
        (d02BalancedDirectShift σ) Φ+
        Complex.exp (-(σ 0+σ 1))*d02GaussianDiagonalPhysicalHeightMean T
          (fun i t => (ρ i t:ℂ)) (d02BalancedDualShift σ) Φ)) atTop
      (𝓝 (((arithmeticFactor*(∫ τ : ℝ, Φ τ):ℝ):ℂ)*d02BalancedShiftedEdgeIntegral ρ σ)) := by
  have hcap : ∀ i t, (ρ i t:ℂ)≠0 → t∈Icc 0 (A i) := by
    intro i t hn
    apply hρcap i t
    intro hz
    exact hn (by rw [hz]; simp)
  have h₀ := d02GaussianDiagonalPhysicalHeightMean_limit_fixed_shifts
    (fun i t => (ρ i t:ℂ)) A (d02BalancedDirectShift σ) Φ
    (fun i => Complex.continuous_ofReal.comp (hρc i)) hcap hΦc hΦs
  have h₁ := d02GaussianDiagonalPhysicalHeightMean_limit_fixed_shifts
    (fun i t => (ρ i t:ℂ)) A (d02BalancedDualShift σ) Φ
    (fun i => Complex.continuous_ofReal.comp (hρc i)) hcap hΦc hΦs
  rw [d02BalancedHeightMass_comm] at h₀ h₁
  have h := (h₀.add (h₁.const_mul (Complex.exp (-(σ 0+σ 1))))).const_mul
    (Complex.exp ((σ 0+σ 1)/2))
  rw [d02BalancedDirectDual_sharpEndpoint _ ρ A σ hρc hρcap] at h
  exact h

theorem d02BalancedShiftedTruncatedPhysicalHeightMean_limit
    {δ : ℝ} (hδ : 0≤δ) (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (σ : Fin 2 → ℂ) (Φ : ℝ → ℝ)
    (hρc : ∀ i, Continuous (ρ i))
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i))
    (hΦc : Continuous Φ) (hΦs : tsupport Φ⊆Icc (1:ℝ) 2) :
    Tendsto (fun T : ℝ => Complex.exp ((σ 0+σ 1)/2)*
      (d02GaussianTruncatedDiagonalPhysicalHeightMean δ T (fun i t => (ρ i t:ℂ))
        (d02BalancedDirectShift σ) Φ+
        Complex.exp (-(σ 0+σ 1))*d02GaussianTruncatedDiagonalPhysicalHeightMean δ T
          (fun i t => (ρ i t:ℂ)) (d02BalancedDualShift σ) Φ)) atTop
      (𝓝 (((arithmeticFactor*(∫ τ : ℝ, Φ τ):ℝ):ℂ)*d02BalancedShiftedEdgeIntegral ρ σ)) := by
  have hcap : ∀ i t, (ρ i t:ℂ)≠0 → t∈Icc 0 (A i) := by
    intro i t hn
    apply hρcap i t
    intro hz
    exact hn (by rw [hz]; simp)
  have h₀ := d02GaussianTruncatedDiagonalPhysicalHeightMean_limit_fixed_shifts hδ
    (fun i t => (ρ i t:ℂ)) A (d02BalancedDirectShift σ) Φ
    (fun i => Complex.continuous_ofReal.comp (hρc i)) hcap hΦc hΦs
  have h₁ := d02GaussianTruncatedDiagonalPhysicalHeightMean_limit_fixed_shifts hδ
    (fun i t => (ρ i t:ℂ)) A (d02BalancedDualShift σ) Φ
    (fun i => Complex.continuous_ofReal.comp (hρc i)) hcap hΦc hΦs
  rw [d02BalancedHeightMass_comm] at h₀ h₁
  have h := (h₀.add (h₁.const_mul (Complex.exp (-(σ 0+σ 1))))).const_mul
    (Complex.exp ((σ 0+σ 1)/2))
  rw [d02BalancedDirectDual_sharpEndpoint _ ρ A σ hρc hρcap] at h
  exact h

end
end Sechstmoment
