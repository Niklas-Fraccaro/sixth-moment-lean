import Mathlib.MeasureTheory.Integral.Prod
import Sechstmoment.Denominator.Balanced.GaussianSharpProfiles


namespace Sechstmoment
open MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section
set_option maxHeartbeats 0

def d02GaussianPhysicalOffset (τ : ℝ) : ℝ :=
  Real.log (2*Real.pi)-Real.log τ

theorem d02GaussianPhysicalOffset_eq_log_ratio {τ : ℝ} (hτ : 0 < τ) :
    d02GaussianPhysicalOffset τ = Real.log (2*Real.pi/τ) := by
  rw [Real.log_div (by positivity : 2*Real.pi ≠ 0) hτ.ne']
  rfl

theorem d02GaussianV0_physical_log_identity {T τ : ℝ} (hT : 0 < T)
    (hτ : 0 < τ) (q : ℝ) :
    d02GaussianV0 (2*Real.pi*Real.exp (Real.log T*q)/(T*τ)) =
      d02GaussianLogWeight (Real.log T) q (d02GaussianPhysicalOffset τ) := by
  rw [d02GaussianPhysicalOffset_eq_log_ratio hτ]
  simpa only [Real.exp_log hT] using
    d02GaussianV0_logarithmic_identity (Real.log T) q hτ

theorem d02GaussianV0_physical_logPoint_identity {L τ : ℝ} (hL : 0 < L)
    (hτ : 0 < τ) (x : DiagonalSixIndices) :
    d02GaussianV0 (2*Real.pi*((d01LeftIndices x 0 : ℝ)*(d01RightIndices x 0 : ℝ))/
      (Real.exp L*τ)) =
      d02GaussianLogWeight L (d02LogCutCoordinate (d01LogPoint L x))
        (d02GaussianPhysicalOffset τ) := by
  have hp : 0 < (d01LeftIndices x 0 : ℝ)*(d01RightIndices x 0 : ℝ) :=
    mul_pos (by exact_mod_cast d01LeftIndices_pos x 0)
      (by exact_mod_cast d01RightIndices_pos x 0)
  have he : Real.exp (L*d02LogCutCoordinate (d01LogPoint L x)) =
      (d01LeftIndices x 0 : ℝ)*(d01RightIndices x 0 : ℝ) := by
    rw [d02LogCutCoordinate_logPoint, mul_div_cancel₀ _ hL.ne', Real.exp_log hp]
  rw [d02GaussianPhysicalOffset_eq_log_ratio hτ]
  simpa only [he] using d02GaussianV0_logarithmic_identity L
    (d02LogCutCoordinate (d01LogPoint L x)) hτ

def d02PhysicalGaussianDiagonalIntegral (L : ℝ) (ρ : Fin 4 → ℝ → ℂ)
    (ab : PolarShiftSpace) (τ : ℝ) : ℂ :=
  ∫ y, d01ComplexLaplaceWeight ab y*d02FourProfileProduct ρ y*
    (d02GaussianV0 (2*Real.pi*Real.exp (L*d02LogCutCoordinate y)/
      (Real.exp L*τ)) : ℂ) ∂d01DiagonalMeasure L

theorem d02PhysicalGaussianDiagonalIntegral_tsum {L τ : ℝ} (hL : 0 < L)
    (hτ : 0 < τ) (ρ : Fin 4 → ℝ → ℂ) (ab : PolarShiftSpace) :
    d02PhysicalGaussianDiagonalIntegral L ρ ab τ =
      ∑' x : DiagonalSixIndices, d01AtomicWeight L x •
        (d01ComplexLaplaceWeight ab (d01LogPoint L x)*
          d02FourProfileProduct ρ (d01LogPoint L x)*
            (d02GaussianV0 (2*Real.pi*((d01LeftIndices x 0 : ℝ)*
              (d01RightIndices x 0 : ℝ))/(Real.exp L*τ)) : ℂ)) := by
  rw [d02PhysicalGaussianDiagonalIntegral, d01DiagonalMeasure_integral hL.le]
  apply tsum_congr
  intro x
  rw [d02GaussianV0_logarithmic_identity L _ hτ,
    ← d02GaussianPhysicalOffset_eq_log_ratio hτ,
    ← d02GaussianV0_physical_logPoint_identity hL hτ x]

def d02PhysicalGaussianDiagonalTimeMean (L : ℝ) (ρ : Fin 4 → ℝ → ℂ)
    (ab : PolarShiftSpace) (Φ : ℝ → ℝ) : ℂ :=
  ∫ τ : ℝ, (Φ τ : ℂ)*d02PhysicalGaussianDiagonalIntegral L ρ ab τ

def d02GaussianDiagonalPhysicalHeightMean (T : ℝ) (ρ : Fin 4 → ℝ → ℂ)
    (ab : PolarShiftSpace) (Φ : ℝ → ℝ) : ℂ :=
  (∫ t : ℝ, (Φ (t/T) : ℂ)*
    (∫ y, d01ComplexLaplaceWeight ab y*d02FourProfileProduct ρ y*
      (d02GaussianV0 (2*Real.pi*Real.exp (Real.log T*d02LogCutCoordinate y)/t) : ℂ)
        ∂d01DiagonalMeasure (Real.log T))) / (T : ℂ)

theorem d02GaussianDiagonalPhysicalHeightMean_eq {T : ℝ} (hT : 0 < T)
    (ρ : Fin 4 → ℝ → ℂ) (ab : PolarShiftSpace) (Φ : ℝ → ℝ) :
    d02GaussianDiagonalPhysicalHeightMean T ρ ab Φ =
      d02PhysicalGaussianDiagonalTimeMean (Real.log T) ρ ab Φ := by
  have hden (t : ℝ) : Real.exp (Real.log T)*(t/T) = t := by
    rw [Real.exp_log hT]
    field_simp [hT.ne']
  have he : (∫ t : ℝ, (Φ (t/T) : ℂ)*
      (∫ y, d01ComplexLaplaceWeight ab y*d02FourProfileProduct ρ y*
        (d02GaussianV0 (2*Real.pi*Real.exp (Real.log T*d02LogCutCoordinate y)/t) : ℂ)
          ∂d01DiagonalMeasure (Real.log T))) =
      ∫ t : ℝ, (Φ (t/T) : ℂ)*d02PhysicalGaussianDiagonalIntegral (Real.log T) ρ ab (t/T) := by
    apply integral_congr_ae
    exact ae_of_all _ (fun t => by simp only [d02PhysicalGaussianDiagonalIntegral,hden])
  unfold d02GaussianDiagonalPhysicalHeightMean
  rw [he, Measure.integral_comp_div
    (fun τ : ℝ => (Φ τ : ℂ)*d02PhysicalGaussianDiagonalIntegral (Real.log T) ρ ab τ) T,
    abs_of_pos hT, Complex.real_smul]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hT.ne')

theorem d02PhysicalGaussianDiagonalIntegral_measurable (L : ℝ)
    (ρ : Fin 4 → ℝ → ℂ) (ab : PolarShiftSpace)
    (hρc : ∀ k, Continuous (ρ k)) :
    Measurable (d02PhysicalGaussianDiagonalIntegral L ρ ab) := by
  let _ : SFinite (d01DiagonalMeasure L) := by
    unfold d01DiagonalMeasure
    infer_instance
  have harg : Measurable (fun p : ℝ × D01LogSpace =>
      2*Real.pi*Real.exp (L*d02LogCutCoordinate p.2)/(Real.exp L*p.1)) := by
    apply Measurable.div
    · exact measurable_const.mul (Real.measurable_exp.comp
        (measurable_const.mul (d02LogCutCoordinate_continuous.measurable.comp measurable_snd)))
    · exact measurable_const.mul measurable_fst
  have hV : Measurable (fun p : ℝ × D01LogSpace =>
      (d02GaussianV0 (2*Real.pi*Real.exp (L*d02LogCutCoordinate p.2)/
        (Real.exp L*p.1)) : ℂ)) :=
    Complex.measurable_ofReal.comp (d02GaussianTail_antitone.measurable.comp
      ((Real.measurable_log.comp harg).div_const 2))
  have hf : Measurable (fun p : ℝ × D01LogSpace =>
      d01ComplexLaplaceWeight ab p.2*d02FourProfileProduct ρ p.2*
        (d02GaussianV0 (2*Real.pi*Real.exp (L*d02LogCutCoordinate p.2)/
          (Real.exp L*p.1)) : ℂ)) :=
    (((d01ComplexLaplaceWeight_continuous ab).measurable.comp measurable_snd).mul
      ((d02FourProfileProduct_continuous ρ hρc).measurable.comp measurable_snd)).mul hV
  exact hf.stronglyMeasurable.integral_prod_right'.measurable

private theorem d02_time_mean_error_bound
    (G : ℝ → ℂ) (S : ℂ) (Φ : ℝ → ℝ) (hGm : Measurable G)
    (hΦc : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc (1:ℝ) 2)
    {δ : ℝ} (hδ : 0 ≤ δ) (hcut : ∀ τ ∈ Icc (1:ℝ) 2, ‖G τ-S‖ ≤ δ) :
    Integrable (fun τ : ℝ => (Φ τ : ℂ)*G τ) ∧
    ‖(∫ τ : ℝ, (Φ τ : ℂ)*G τ)-((∫ τ : ℝ, Φ τ : ℝ) : ℂ)*S‖ ≤
      δ*(∫ τ : ℝ, |Φ τ|) := by
  have hΦK : HasCompactSupport Φ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport Φ).trans hΦs)
  have hΦi : Integrable Φ := hΦc.integrable_of_hasCompactSupport hΦK
  have hΦCi : Integrable (fun τ : ℝ => (Φ τ : ℂ)) := hΦi.ofReal
  have hmajor : Integrable (fun τ : ℝ => δ*|Φ τ|) := hΦi.abs.const_mul δ
  have hdom : ∀ τ : ℝ,
      ‖(Φ τ : ℂ)*(G τ-S)‖ ≤ δ*|Φ τ| := by
    intro τ
    by_cases hΦτ : Φ τ = 0
    · calc
        _ = 0 := by simp [hΦτ]
        _ ≤ _ := mul_nonneg hδ (abs_nonneg _)
    have hτ : τ ∈ Icc (1:ℝ) 2 := hΦs (subset_tsupport Φ hΦτ)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hcut τ hτ) (abs_nonneg _)).trans_eq (mul_comm _ _)
  have hEi : Integrable (fun τ : ℝ =>
      (Φ τ : ℂ)*(G τ-S)) := by
    apply hmajor.mono'
      ((Complex.measurable_ofReal.comp hΦc.measurable).mul
        (hGm.sub measurable_const)).aestronglyMeasurable
    exact ae_of_all _ hdom
  have hSi : Integrable (fun τ : ℝ => (Φ τ : ℂ)*S) := hΦCi.mul_const S
  have hGi : Integrable (fun τ : ℝ =>
      (Φ τ : ℂ)*G τ) := by
    apply (hEi.add hSi).congr
    exact ae_of_all _ (fun τ => by
      change (Φ τ : ℂ)*(G τ-S)+(Φ τ : ℂ)*S = (Φ τ : ℂ)*G τ
      ring)
  refine ⟨hGi, ?_⟩
  have he : (∫ τ : ℝ, (Φ τ : ℂ)*G τ)-
      ((∫ τ : ℝ, Φ τ : ℝ) : ℂ)*S =
      ∫ τ : ℝ, (Φ τ : ℂ)*(G τ-S) := by
    rw [← integral_complex_ofReal (f := Φ) (μ := volume),
      ← integral_mul_const S (fun τ : ℝ => (Φ τ : ℂ)), ← integral_sub hGi hSi]
    apply integral_congr_ae
    exact ae_of_all _ (fun τ => by ring)
  change ‖(∫ τ : ℝ, (Φ τ : ℂ)*G τ)-((∫ τ : ℝ, Φ τ : ℝ) : ℂ)*S‖ ≤ _
  rw [he]
  simpa only [integral_const_mul] using norm_integral_le_of_norm_le hmajor (ae_of_all _ hdom)


private theorem d02_physical_time_mean_error_bound
    (L : ℝ) (ρ : Fin 4 → ℝ → ℂ) (ab : PolarShiftSpace) (Φ : ℝ → ℝ)
    (hρc : ∀ k, Continuous (ρ k)) (hΦc : Continuous Φ)
    (hΦs : tsupport Φ ⊆ Icc (1:ℝ) 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcut : ∀ τ ∈ Icc (1:ℝ) 2,
      ‖d02PhysicalGaussianDiagonalIntegral L ρ ab τ-
        ∫ y, d01ComplexLaplaceWeight ab y*d02SharpLogTest (d02FourProfileProduct ρ) y
          ∂d01DiagonalMeasure L‖ ≤ δ) :
    Integrable (fun τ : ℝ => (Φ τ : ℂ)*d02PhysicalGaussianDiagonalIntegral L ρ ab τ) ∧
    ‖d02PhysicalGaussianDiagonalTimeMean L ρ ab Φ-
      ((∫ τ : ℝ, Φ τ : ℝ) : ℂ)*
        (∫ y, d01ComplexLaplaceWeight ab y*d02SharpLogTest (d02FourProfileProduct ρ) y
          ∂d01DiagonalMeasure L)‖ ≤ δ*(∫ τ : ℝ, |Φ τ|) := by
  exact d02_time_mean_error_bound (d02PhysicalGaussianDiagonalIntegral L ρ ab)
    (∫ y, d01ComplexLaplaceWeight ab y*d02SharpLogTest (d02FourProfileProduct ρ) y
      ∂d01DiagonalMeasure L) Φ (d02PhysicalGaussianDiagonalIntegral_measurable L ρ ab hρc)
    hΦc hΦs hδ hcut

theorem d02PhysicalGaussianDiagonalTimeMean_sharp_uniform
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ) (Φ : ℝ → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hOffset : |Real.log (2*Real.pi)|+Real.log 2 ≤ C)
    (hρc : ∀ k, Continuous (ρ k))
    (hρcap : ∀ k t, ρ k t ≠ 0 → t ∈ Icc 0 (a k))
    (hΦc : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc (1:ℝ) 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ ab : PolarShiftSpace,
      (∀ i, -C ≤ (ab.1 i).re) → (∀ i, -C ≤ (ab.2 i).re) →
      Integrable (fun τ : ℝ => (Φ τ : ℂ)*d02PhysicalGaussianDiagonalIntegral L ρ ab τ) ∧
      ‖d02PhysicalGaussianDiagonalTimeMean L ρ ab Φ-
        ((∫ τ : ℝ, Φ τ : ℝ) : ℂ)*
          (∫ y, d01ComplexLaplaceWeight ab y*d02SharpLogTest (d02FourProfileProduct ρ) y
            ∂d01DiagonalMeasure L)‖ < ε := by
  have hρK : ∀ k, HasCompactSupport (ρ k) := by
    intro k
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := 0) (b := a k))
    intro t ht
    exact hρcap k t ht
  choose b hb using fun k => (hρK k).exists_bound_of_continuous (hρc k)
  have hb0 : ∀ k, 0 ≤ b k := fun k => (norm_nonneg (ρ k 0)).trans (hb k 0)
  let M := ∫ τ : ℝ, |Φ τ|
  have hM0 : 0 ≤ M := integral_nonneg (fun _ => abs_nonneg _)
  let δ := ε/(M+1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  filter_upwards [d02DiagonalMeasure_shifted_four_profile_physical_gaussian_sharp_uniform
    ρ a b hC hOffset hρc hρcap hb0 hb hδ] with L hL
  intro ab ha hbshift
  have h := d02_physical_time_mean_error_bound L ρ ab Φ hρc hΦc hΦs hδ.le
    (fun τ hτ => (hL ab τ ha hbshift hτ).le)
  refine ⟨h.1, h.2.trans_lt ?_⟩
  change δ*M < ε
  have he : δ*(M+1) = ε := by
    dsimp [δ]
    exact div_mul_cancel₀ ε (by linarith : M+1 ≠ 0)
  nlinarith

theorem d02PhysicalGaussianDiagonalTimeMean_limit
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ) (ab : PolarShiftSpace) (Φ : ℝ → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hOffset : |Real.log (2*Real.pi)|+Real.log 2 ≤ C)
    (hρc : ∀ k, Continuous (ρ k))
    (hρcap : ∀ k t, ρ k t ≠ 0 → t ∈ Icc 0 (a k))
    (ha : ∀ i, -C ≤ (ab.1 i).re) (hbshift : ∀ i, -C ≤ (ab.2 i).re)
    (hΦc : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc (1:ℝ) 2) :
    Tendsto (fun L : ℝ => d02PhysicalGaussianDiagonalTimeMean L ρ ab Φ) atTop
      (𝓝 (((∫ τ : ℝ, Φ τ : ℝ) : ℂ)*(arithmeticFactor : ℂ)*
        ∫ x : D01EdgeSpace, d01ComplexLaplaceWeight ab (d01RowColumnSums x)*
          d02SharpLogTest (d02FourProfileProduct ρ) (d01RowColumnSums x)
            ∂volume.restrict d01NonnegativeOrthant)) := by
  have herr : Tendsto (fun L : ℝ => d02PhysicalGaussianDiagonalTimeMean L ρ ab Φ-
      ((∫ τ : ℝ, Φ τ : ℝ) : ℂ)*
        (∫ y, d01ComplexLaplaceWeight ab y*d02SharpLogTest (d02FourProfileProduct ρ) y
          ∂d01DiagonalMeasure L)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [d02PhysicalGaussianDiagonalTimeMean_sharp_uniform ρ a Φ hC hOffset
      hρc hρcap hΦc hΦs hε] with L hL
    simpa only [dist_zero_right] using (hL ab ha hbshift).2
  have hsharp := (d02DiagonalMeasure_four_profile_sharp_log_limit ρ a
    (d01ComplexLaplaceWeight ab) hρc hρcap (d01ComplexLaplaceWeight_continuous ab)).const_mul
      (((∫ τ : ℝ, Φ τ : ℝ) : ℂ))
  simpa only [sub_add_cancel, zero_add, mul_assoc] using herr.add hsharp

theorem d02PhysicalGaussianDiagonalTimeMean_height_limit
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ) (ab : PolarShiftSpace) (Φ : ℝ → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hOffset : |Real.log (2*Real.pi)|+Real.log 2 ≤ C)
    (hρc : ∀ k, Continuous (ρ k))
    (hρcap : ∀ k t, ρ k t ≠ 0 → t ∈ Icc 0 (a k))
    (ha : ∀ i, -C ≤ (ab.1 i).re) (hbshift : ∀ i, -C ≤ (ab.2 i).re)
    (hΦc : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc (1:ℝ) 2) :
    Tendsto (fun T : ℝ => d02PhysicalGaussianDiagonalTimeMean (Real.log T) ρ ab Φ) atTop
      (𝓝 (((∫ τ : ℝ, Φ τ : ℝ) : ℂ)*(arithmeticFactor : ℂ)*
        ∫ x : D01EdgeSpace, d01ComplexLaplaceWeight ab (d01RowColumnSums x)*
          d02SharpLogTest (d02FourProfileProduct ρ) (d01RowColumnSums x)
            ∂volume.restrict d01NonnegativeOrthant)) :=
  (d02PhysicalGaussianDiagonalTimeMean_limit ρ a ab Φ hC hOffset hρc hρcap
    ha hbshift hΦc hΦs).comp Real.tendsto_log_atTop

theorem d02GaussianDiagonalPhysicalHeightMean_limit
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ) (ab : PolarShiftSpace) (Φ : ℝ → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hOffset : |Real.log (2*Real.pi)|+Real.log 2 ≤ C)
    (hρc : ∀ k, Continuous (ρ k))
    (hρcap : ∀ k t, ρ k t ≠ 0 → t ∈ Icc 0 (a k))
    (ha : ∀ i, -C ≤ (ab.1 i).re) (hbshift : ∀ i, -C ≤ (ab.2 i).re)
    (hΦc : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc (1:ℝ) 2) :
    Tendsto (fun T : ℝ => d02GaussianDiagonalPhysicalHeightMean T ρ ab Φ) atTop
      (𝓝 (((∫ τ : ℝ, Φ τ : ℝ) : ℂ)*(arithmeticFactor : ℂ)*
        ∫ x : D01EdgeSpace, d01ComplexLaplaceWeight ab (d01RowColumnSums x)*
          d02SharpLogTest (d02FourProfileProduct ρ) (d01RowColumnSums x)
            ∂volume.restrict d01NonnegativeOrthant)) := by
  apply (d02PhysicalGaussianDiagonalTimeMean_height_limit ρ a ab Φ hC hOffset hρc hρcap
    ha hbshift hΦc hΦs).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  exact (d02GaussianDiagonalPhysicalHeightMean_eq hT ρ ab Φ).symm

theorem d02GaussianDiagonalPhysicalHeightMean_limit_fixed_shifts
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ) (ab : PolarShiftSpace) (Φ : ℝ → ℝ)
    (hρc : ∀ k, Continuous (ρ k))
    (hρcap : ∀ k t, ρ k t ≠ 0 → t ∈ Icc 0 (a k))
    (hΦc : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc (1:ℝ) 2) :
    Tendsto (fun T : ℝ => d02GaussianDiagonalPhysicalHeightMean T ρ ab Φ) atTop
      (𝓝 (((∫ τ : ℝ, Φ τ : ℝ) : ℂ)*(arithmeticFactor : ℂ)*
        ∫ x : D01EdgeSpace, d01ComplexLaplaceWeight ab (d01RowColumnSums x)*
          d02SharpLogTest (d02FourProfileProduct ρ) (d01RowColumnSums x)
            ∂volume.restrict d01NonnegativeOrthant)) := by
  let R := ∑ i : Fin 3, (|(ab.1 i).re|+|(ab.2 i).re|)
  let C := max (|Real.log (2*Real.pi)|+Real.log 2) R
  have hR0 : 0 ≤ R := Finset.sum_nonneg (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hRC : R ≤ C := le_max_right _ _
  have hC : 0 ≤ C := hR0.trans hRC
  have ha : ∀ i, -C ≤ (ab.1 i).re := by
    intro i
    have hs : |(ab.1 i).re|+|(ab.2 i).re| ≤ R :=
      Finset.single_le_sum
        (fun j _ => add_nonneg (abs_nonneg (ab.1 j).re) (abs_nonneg (ab.2 j).re))
        (Finset.mem_univ i)
    have hi : |(ab.1 i).re| ≤ R :=
      (le_add_of_nonneg_right (abs_nonneg (ab.2 i).re)).trans hs
    exact (neg_le_neg (hi.trans hRC)).trans (neg_abs_le _)
  have hb : ∀ i, -C ≤ (ab.2 i).re := by
    intro i
    have hs : |(ab.1 i).re|+|(ab.2 i).re| ≤ R :=
      Finset.single_le_sum
        (fun j _ => add_nonneg (abs_nonneg (ab.1 j).re) (abs_nonneg (ab.2 j).re))
        (Finset.mem_univ i)
    have hi : |(ab.2 i).re| ≤ R :=
      (le_add_of_nonneg_left (abs_nonneg (ab.1 i).re)).trans hs
    exact (neg_le_neg (hi.trans hRC)).trans (neg_abs_le _)
  exact d02GaussianDiagonalPhysicalHeightMean_limit ρ a ab Φ hC (le_max_left _ _)
    hρc hρcap ha hb hΦc hΦs

theorem d02PhysicalGaussianDiagonalIntegral_eventually_uniform_norm_bound
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hOffset : |Real.log (2*Real.pi)|+Real.log 2 ≤ C)
    (hρc : ∀ k, Continuous (ρ k))
    (hρcap : ∀ k t, ρ k t ≠ 0 → t ∈ Icc 0 (a k)) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ L : ℝ in atTop, ∀ (ab : PolarShiftSpace) (τ : ℝ),
      (∀ i, -C ≤ (ab.1 i).re) → (∀ i, -C ≤ (ab.2 i).re) → τ ∈ Icc (1:ℝ) 2 →
      ‖d02PhysicalGaussianDiagonalIntegral L ρ ab τ‖ ≤ B := by
  have hρK : ∀ k, HasCompactSupport (ρ k) := by
    intro k
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := 0) (b := a k))
    intro t ht
    exact hρcap k t ht
  choose b hb using fun k => (hρK k).exists_bound_of_continuous (hρc k)
  have hb0 : ∀ k, 0 ≤ b k := fun k => (norm_nonneg (ρ k 0)).trans (hb k 0)
  let K := (b 0*b 1*b 2*b 3*Real.exp (C*d02ProfileCapSum a))*
    Real.exp (d02ProfileCapSum a)*Real.exp (C+1)
  let A := ∫ _y : D01LogSpace, (1:ℝ) ∂d02TiltedLimitMeasure
  let B := 1+K*(A+1)
  have hprod0 : 0 ≤ b 0*b 1*b 2*b 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (hb0 0) (hb0 1)) (hb0 2)) (hb0 3)
  have hK0 : 0 ≤ K := mul_nonneg
    (mul_nonneg (mul_nonneg hprod0 (Real.exp_pos _).le) (Real.exp_pos _).le)
    (Real.exp_pos _).le
  have hA0 : 0 ≤ A := integral_nonneg (fun _ => by norm_num)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  have hmass := d02TiltedDiagonalMeasure_mass_tendsto.eventually_lt_const
    (show (∫ _y : D01LogSpace, (1:ℝ) ∂d02TiltedLimitMeasure) < A+1 by
      dsimp [A]; linarith)
  filter_upwards [hmass, eventually_gt_atTop (0:ℝ),
    d02DiagonalMeasure_shifted_four_profile_physical_gaussian_sharp_uniform ρ a b hC hOffset
      hρc hρcap hb0 hb (by norm_num : (0:ℝ) < 1)] with L hMass hL hError
  intro ab τ ha hbshift hτ
  let S := ∫ y, d01ComplexLaplaceWeight ab y*d02SharpLogTest (d02FourProfileProduct ρ) y
    ∂d01DiagonalMeasure L
  have hS : ‖S‖ ≤ K*(A+1) :=
    (d02DiagonalMeasure_shifted_four_profile_sharp_norm_bound ρ a b hC hL
      hρcap hb0 hb ab ha hbshift).trans
        (mul_le_mul_of_nonneg_left hMass.le hK0)
  have hE : ‖d02PhysicalGaussianDiagonalIntegral L ρ ab τ-S‖ ≤ 1 :=
    (hError ab τ ha hbshift hτ).le
  calc
    _ = ‖(d02PhysicalGaussianDiagonalIntegral L ρ ab τ-S)+S‖ := by rw [sub_add_cancel]
    _ ≤ ‖d02PhysicalGaussianDiagonalIntegral L ρ ab τ-S‖+‖S‖ := norm_add_le _ _
    _ ≤ 1+K*(A+1) := add_le_add hE hS
    _ = B := rfl

theorem d02PhysicalGaussianDiagonalTimeMean_eventually_uniform_norm_bound
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ) (Φ : ℝ → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hOffset : |Real.log (2*Real.pi)|+Real.log 2 ≤ C)
    (hρc : ∀ k, Continuous (ρ k))
    (hρcap : ∀ k t, ρ k t ≠ 0 → t ∈ Icc 0 (a k))
    (hΦc : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc (1:ℝ) 2) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ L : ℝ in atTop, ∀ ab : PolarShiftSpace,
      (∀ i, -C ≤ (ab.1 i).re) → (∀ i, -C ≤ (ab.2 i).re) →
      Integrable (fun τ : ℝ => (Φ τ : ℂ)*d02PhysicalGaussianDiagonalIntegral L ρ ab τ) ∧
      ‖d02PhysicalGaussianDiagonalTimeMean L ρ ab Φ‖ ≤ B := by
  have hρK : ∀ k, HasCompactSupport (ρ k) := by
    intro k
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := 0) (b := a k))
    intro t ht
    exact hρcap k t ht
  choose b hb using fun k => (hρK k).exists_bound_of_continuous (hρc k)
  have hb0 : ∀ k, 0 ≤ b k := fun k => (norm_nonneg (ρ k 0)).trans (hb k 0)
  let K := (b 0*b 1*b 2*b 3*Real.exp (C*d02ProfileCapSum a))*
    Real.exp (d02ProfileCapSum a)*Real.exp (C+1)
  let A := ∫ _y : D01LogSpace, (1:ℝ) ∂d02TiltedLimitMeasure
  let m : ℂ := ((∫ τ : ℝ, Φ τ : ℝ) : ℂ)
  let B := 1+‖m‖*K*(A+1)
  have hprod0 : 0 ≤ b 0*b 1*b 2*b 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (hb0 0) (hb0 1)) (hb0 2)) (hb0 3)
  have hK0 : 0 ≤ K := mul_nonneg
    (mul_nonneg (mul_nonneg hprod0 (Real.exp_pos _).le) (Real.exp_pos _).le)
    (Real.exp_pos _).le
  have hA0 : 0 ≤ A := integral_nonneg (fun _ => by norm_num)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  have hmass := d02TiltedDiagonalMeasure_mass_tendsto.eventually_lt_const
    (show (∫ _y : D01LogSpace, (1:ℝ) ∂d02TiltedLimitMeasure) < A+1 by
      dsimp [A]; linarith)
  filter_upwards [hmass, eventually_gt_atTop (0:ℝ),
    d02PhysicalGaussianDiagonalTimeMean_sharp_uniform ρ a Φ hC hOffset
      hρc hρcap hΦc hΦs (by norm_num : (0:ℝ) < 1)] with L hMass hL hError
  intro ab ha hbshift
  have h := hError ab ha hbshift
  refine ⟨h.1,?_⟩
  let S := ∫ y, d01ComplexLaplaceWeight ab y*d02SharpLogTest (d02FourProfileProduct ρ) y
    ∂d01DiagonalMeasure L
  have hS : ‖S‖ ≤ K*(A+1) :=
    (d02DiagonalMeasure_shifted_four_profile_sharp_norm_bound ρ a b hC hL
      hρcap hb0 hb ab ha hbshift).trans
        (mul_le_mul_of_nonneg_left hMass.le hK0)
  have hE : ‖d02PhysicalGaussianDiagonalTimeMean L ρ ab Φ-m*S‖ ≤ 1 := h.2.le
  calc
    _ = ‖(d02PhysicalGaussianDiagonalTimeMean L ρ ab Φ-m*S)+m*S‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖d02PhysicalGaussianDiagonalTimeMean L ρ ab Φ-m*S‖+‖m*S‖ := norm_add_le _ _
    _ ≤ 1+‖m‖*(K*(A+1)) := by
      rw [norm_mul]
      exact add_le_add hE (mul_le_mul_of_nonneg_left hS (norm_nonneg m))
    _ = B := by dsimp [B]; ring

theorem d02GaussianDiagonalPhysicalHeight_integrable {T : ℝ} (hT : 0 < T)
    (ρ : Fin 4 → ℝ → ℂ) (ab : PolarShiftSpace) (Φ : ℝ → ℝ)
    (hi : Integrable (fun τ : ℝ =>
      (Φ τ : ℂ)*d02PhysicalGaussianDiagonalIntegral (Real.log T) ρ ab τ)) :
    Integrable (fun t : ℝ => (Φ (t/T) : ℂ)*
      (∫ y, d01ComplexLaplaceWeight ab y*d02FourProfileProduct ρ y*
        (d02GaussianV0 (2*Real.pi*Real.exp (Real.log T*d02LogCutCoordinate y)/t) : ℂ)
          ∂d01DiagonalMeasure (Real.log T))) := by
  have hden (t : ℝ) : Real.exp (Real.log T)*(t/T) = t := by
    rw [Real.exp_log hT]
    field_simp [hT.ne']
  apply (hi.comp_div hT.ne').congr
  exact ae_of_all _ (fun t => by simp only [d02PhysicalGaussianDiagonalIntegral,hden])

theorem d02GaussianDiagonalPhysicalHeightMean_eventually_uniform_norm_bound
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ) (Φ : ℝ → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hOffset : |Real.log (2*Real.pi)|+Real.log 2 ≤ C)
    (hρc : ∀ k, Continuous (ρ k))
    (hρcap : ∀ k t, ρ k t ≠ 0 → t ∈ Icc 0 (a k))
    (hΦc : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc (1:ℝ) 2) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ T : ℝ in atTop, ∀ ab : PolarShiftSpace,
      (∀ i, -C ≤ (ab.1 i).re) → (∀ i, -C ≤ (ab.2 i).re) →
      Integrable (fun t : ℝ => (Φ (t/T) : ℂ)*
        (∫ y, d01ComplexLaplaceWeight ab y*d02FourProfileProduct ρ y*
          (d02GaussianV0 (2*Real.pi*Real.exp (Real.log T*d02LogCutCoordinate y)/t) : ℂ)
            ∂d01DiagonalMeasure (Real.log T))) ∧
      ‖d02GaussianDiagonalPhysicalHeightMean T ρ ab Φ‖ ≤ B := by
  obtain ⟨B,hB,hevent⟩ := d02PhysicalGaussianDiagonalTimeMean_eventually_uniform_norm_bound
    ρ a Φ hC hOffset hρc hρcap hΦc hΦs
  refine ⟨B,hB,?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually hevent, eventually_gt_atTop (0:ℝ)]
    with T hBound hT
  intro ab ha hb
  have h := hBound ab ha hb
  refine ⟨d02GaussianDiagonalPhysicalHeight_integrable hT ρ ab Φ h.1,?_⟩
  rw [d02GaussianDiagonalPhysicalHeightMean_eq hT]
  exact h.2

def d02GaussianTruncatedFourProfile (δ : ℝ) (ρ : Fin 4 → ℝ → ℂ)
    (y : D01LogSpace) : ℂ :=
  {y : D01LogSpace | d02LogCutCoordinate y ≤ 1+δ}.indicator (d02FourProfileProduct ρ) y

theorem d02GaussianTruncatedLogRegion_measurable (δ : ℝ) :
    MeasurableSet {y : D01LogSpace | d02LogCutCoordinate y ≤ 1+δ} :=
  (isClosed_le d02LogCutCoordinate_continuous continuous_const).measurableSet

theorem d02GaussianTruncatedFourProfile_measurable (δ : ℝ) (ρ : Fin 4 → ℝ → ℂ)
    (hρc : ∀ k, Continuous (ρ k)) : Measurable (d02GaussianTruncatedFourProfile δ ρ) :=
  (d02FourProfileProduct_continuous ρ hρc).measurable.indicator
    (d02GaussianTruncatedLogRegion_measurable δ)

theorem d02GaussianTruncatedLogRegion_logPoint_iff {L : ℝ} (hL : 0 < L)
    (δ : ℝ) (x : DiagonalSixIndices) :
    d02LogCutCoordinate (d01LogPoint L x) ≤ 1+δ ↔
      (d01LeftIndices x 0 : ℝ)*(d01RightIndices x 0 : ℝ) ≤ Real.exp (L*(1+δ)) := by
  have hp : 0 < (d01LeftIndices x 0 : ℝ)*(d01RightIndices x 0 : ℝ) :=
    mul_pos (by exact_mod_cast d01LeftIndices_pos x 0)
      (by exact_mod_cast d01RightIndices_pos x 0)
  rw [d02LogCutCoordinate_logPoint, div_le_iff₀ hL, Real.log_le_iff_le_exp hp]
  rw [mul_comm (1+δ) L]

def d02PhysicalGaussianTruncatedDiagonalIntegral (δ L : ℝ) (ρ : Fin 4 → ℝ → ℂ)
    (ab : PolarShiftSpace) (τ : ℝ) : ℂ :=
  ∫ y, d01ComplexLaplaceWeight ab y*d02GaussianTruncatedFourProfile δ ρ y*
    (d02GaussianV0 (2*Real.pi*Real.exp (L*d02LogCutCoordinate y)/
      (Real.exp L*τ)) : ℂ) ∂d01DiagonalMeasure L

def d02PhysicalGaussianTruncatedDiagonalTimeMean (δ L : ℝ) (ρ : Fin 4 → ℝ → ℂ)
    (ab : PolarShiftSpace) (Φ : ℝ → ℝ) : ℂ :=
  ∫ τ : ℝ, (Φ τ : ℂ)*d02PhysicalGaussianTruncatedDiagonalIntegral δ L ρ ab τ

def d02GaussianTruncatedDiagonalPhysicalHeightMean (δ T : ℝ) (ρ : Fin 4 → ℝ → ℂ)
    (ab : PolarShiftSpace) (Φ : ℝ → ℝ) : ℂ :=
  (∫ t : ℝ, (Φ (t/T) : ℂ)*
    (∫ y, d01ComplexLaplaceWeight ab y*d02GaussianTruncatedFourProfile δ ρ y*
      (d02GaussianV0 (2*Real.pi*Real.exp (Real.log T*d02LogCutCoordinate y)/t) : ℂ)
        ∂d01DiagonalMeasure (Real.log T))) / (T : ℂ)

theorem d02PhysicalGaussianTruncatedDiagonalIntegral_tsum {L τ : ℝ} (hL : 0 < L)
    (hτ : 0 < τ) (δ : ℝ) (ρ : Fin 4 → ℝ → ℂ) (ab : PolarShiftSpace) :
    d02PhysicalGaussianTruncatedDiagonalIntegral δ L ρ ab τ =
      ∑' x : DiagonalSixIndices, d01AtomicWeight L x •
        (d01ComplexLaplaceWeight ab (d01LogPoint L x)*
          (if (d01LeftIndices x 0 : ℝ)*(d01RightIndices x 0 : ℝ) ≤ Real.exp (L*(1+δ))
            then d02FourProfileProduct ρ (d01LogPoint L x) else 0)*
            (d02GaussianV0 (2*Real.pi*((d01LeftIndices x 0 : ℝ)*
              (d01RightIndices x 0 : ℝ))/(Real.exp L*τ)) : ℂ)) := by
  rw [d02PhysicalGaussianTruncatedDiagonalIntegral, d01DiagonalMeasure_integral hL.le]
  apply tsum_congr
  intro x
  rw [d02GaussianV0_logarithmic_identity L _ hτ,
    ← d02GaussianPhysicalOffset_eq_log_ratio hτ,
    ← d02GaussianV0_physical_logPoint_identity hL hτ x]
  simp only [d02GaussianTruncatedFourProfile, Set.indicator_apply, Set.mem_ofPred_eq,
    d02GaussianTruncatedLogRegion_logPoint_iff hL]

theorem d02GaussianTruncatedDiagonalPhysicalHeightMean_eq {T : ℝ} (hT : 0 < T)
    (δ : ℝ) (ρ : Fin 4 → ℝ → ℂ) (ab : PolarShiftSpace) (Φ : ℝ → ℝ) :
    d02GaussianTruncatedDiagonalPhysicalHeightMean δ T ρ ab Φ =
      d02PhysicalGaussianTruncatedDiagonalTimeMean δ (Real.log T) ρ ab Φ := by
  have hden (t : ℝ) : Real.exp (Real.log T)*(t/T) = t := by
    rw [Real.exp_log hT]
    field_simp [hT.ne']
  have he : (∫ t : ℝ, (Φ (t/T) : ℂ)*
      (∫ y, d01ComplexLaplaceWeight ab y*d02GaussianTruncatedFourProfile δ ρ y*
        (d02GaussianV0 (2*Real.pi*Real.exp (Real.log T*d02LogCutCoordinate y)/t) : ℂ)
          ∂d01DiagonalMeasure (Real.log T))) =
      ∫ t : ℝ, (Φ (t/T) : ℂ)*
        d02PhysicalGaussianTruncatedDiagonalIntegral δ (Real.log T) ρ ab (t/T) := by
    apply integral_congr_ae
    exact ae_of_all _ (fun t => by simp only [d02PhysicalGaussianTruncatedDiagonalIntegral,hden])
  unfold d02GaussianTruncatedDiagonalPhysicalHeightMean
  rw [he, Measure.integral_comp_div
    (fun τ : ℝ => (Φ τ : ℂ)*d02PhysicalGaussianTruncatedDiagonalIntegral δ (Real.log T) ρ ab τ) T,
    abs_of_pos hT, Complex.real_smul]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hT.ne')

theorem d02PhysicalGaussianTruncatedDiagonalIntegral_measurable (δ L : ℝ)
    (ρ : Fin 4 → ℝ → ℂ) (ab : PolarShiftSpace)
    (hρc : ∀ k, Continuous (ρ k)) :
    Measurable (d02PhysicalGaussianTruncatedDiagonalIntegral δ L ρ ab) := by
  let _ : SFinite (d01DiagonalMeasure L) := by
    unfold d01DiagonalMeasure
    infer_instance
  have harg : Measurable (fun p : ℝ × D01LogSpace =>
      2*Real.pi*Real.exp (L*d02LogCutCoordinate p.2)/(Real.exp L*p.1)) := by
    apply Measurable.div
    · exact measurable_const.mul (Real.measurable_exp.comp
        (measurable_const.mul (d02LogCutCoordinate_continuous.measurable.comp measurable_snd)))
    · exact measurable_const.mul measurable_fst
  have hV : Measurable (fun p : ℝ × D01LogSpace =>
      (d02GaussianV0 (2*Real.pi*Real.exp (L*d02LogCutCoordinate p.2)/
        (Real.exp L*p.1)) : ℂ)) :=
    Complex.measurable_ofReal.comp (d02GaussianTail_antitone.measurable.comp
      ((Real.measurable_log.comp harg).div_const 2))
  have hf : Measurable (fun p : ℝ × D01LogSpace =>
      d01ComplexLaplaceWeight ab p.2*d02GaussianTruncatedFourProfile δ ρ p.2*
        (d02GaussianV0 (2*Real.pi*Real.exp (L*d02LogCutCoordinate p.2)/
          (Real.exp L*p.1)) : ℂ)) :=
    (((d01ComplexLaplaceWeight_continuous ab).measurable.comp measurable_snd).mul
      ((d02GaussianTruncatedFourProfile_measurable δ ρ hρc).comp measurable_snd)).mul hV
  exact hf.stronglyMeasurable.integral_prod_right'.measurable

theorem d02PhysicalGaussianTruncatedDiagonalIntegral_sharp_uniform
    {δ : ℝ} (hδ : 0 ≤ δ) (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hOffset : |Real.log (2*Real.pi)|+Real.log 2 ≤ C)
    (hρc : ∀ k, Continuous (ρ k))
    (hρcap : ∀ k t, ρ k t ≠ 0 → t ∈ Icc 0 (a k)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ (ab : PolarShiftSpace) (τ : ℝ),
      (∀ i, -C ≤ (ab.1 i).re) → (∀ i, -C ≤ (ab.2 i).re) → τ ∈ Icc (1:ℝ) 2 →
      ‖d02PhysicalGaussianTruncatedDiagonalIntegral δ L ρ ab τ-
        ∫ y, d01ComplexLaplaceWeight ab y*d02SharpLogTest (d02FourProfileProduct ρ) y
          ∂d01DiagonalMeasure L‖ < ε := by
  have hρK : ∀ k, HasCompactSupport (ρ k) := by
    intro k
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := 0) (b := a k))
    intro t ht
    exact hρcap k t ht
  choose b hb using fun k => (hρK k).exists_bound_of_continuous (hρc k)
  have hb0 : ∀ k, 0 ≤ b k := fun k => (norm_nonneg (ρ k 0)).trans (hb k 0)
  let B := b 0*b 1*b 2*b 3*Real.exp (C*d02ProfileCapSum a)
  have hprod0 : 0 ≤ b 0*b 1*b 2*b 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (hb0 0) (hb0 1)) (hb0 2)) (hb0 3)
  have hB0 : 0 ≤ B := mul_nonneg hprod0 (Real.exp_pos _).le
  filter_upwards [d02DiagonalMeasure_gaussian_sharp_profile_uniform a hB0 hC hε] with L hL
  intro ab τ ha hbshift hτ
  let F := fun y => d01ComplexLaplaceWeight ab y*d02FourProfileProduct ρ y
  let f := {y : D01LogSpace | d02LogCutCoordinate y ≤ 1+δ}.indicator F
  have hFm : Measurable F := (d01ComplexLaplaceWeight_continuous ab).measurable.mul
    (d02FourProfileProduct_continuous ρ hρc).measurable
  have hfm : Measurable f := hFm.indicator (d02GaussianTruncatedLogRegion_measurable δ)
  have hcap : d02FourCapSupport f a := by
    intro y hy
    have hp : d02FourProfileProduct ρ y ≠ 0 := by
      intro hp
      exact hy (by simp [f,F,hp])
    exact d02FourProfileProduct_cap_support ρ a hρcap y hp
  have hbound : ∀ y ∈ d01PositiveOrthant, ‖f y‖ ≤ B*Real.exp (C*d02LogCutCoordinate y) := by
    intro y hy
    by_cases hq : d02LogCutCoordinate y ≤ 1+δ
    · rw [show f y = F y from indicator_of_mem (show y ∈ {z : D01LogSpace | d02LogCutCoordinate z ≤ 1+δ} from hq) F]
      exact d02ShiftedFourProfile_growth ρ a b hC hρcap hb0 hb ab ha hbshift y hy
    · rw [show f y = 0 from indicator_of_notMem (show y ∉ {z : D01LogSpace | d02LogCutCoordinate z ≤ 1+δ} from hq) F,norm_zero]
      exact mul_nonneg hB0 (Real.exp_pos _).le
  have hc : |Real.log (2*Real.pi/τ)| ≤ C :=
    (d02GaussianPhysicalOffset_bound hτ).trans hOffset
  have h := hL f (Real.log (2*Real.pi/τ)) hfm hcap hbound hc
  have hsharp : d02SharpLogTest f = fun y =>
      d01ComplexLaplaceWeight ab y*d02SharpLogTest (d02FourProfileProduct ρ) y := by
    funext y
    by_cases hq : d02LogCutCoordinate y ≤ 1
    · have hqδ : d02LogCutCoordinate y ≤ 1+δ := by linarith
      simp [d02SharpLogTest,d02SharpLogRegion,f,F,hq,hqδ]
    · simp [d02SharpLogTest,d02SharpLogRegion,hq]
  have hgauss : (fun y => f y*(d02GaussianLogWeight L (d02LogCutCoordinate y)
      (Real.log (2*Real.pi/τ)) : ℂ)) = fun y =>
      d01ComplexLaplaceWeight ab y*d02GaussianTruncatedFourProfile δ ρ y*
        (d02GaussianV0 (2*Real.pi*Real.exp (L*d02LogCutCoordinate y)/(Real.exp L*τ)) : ℂ) := by
    funext y
    rw [d02GaussianV0_logarithmic_identity L _ (zero_lt_one.trans_le hτ.1)]
    by_cases hq : d02LogCutCoordinate y ≤ 1+δ <;>
      simp [f,F,d02GaussianTruncatedFourProfile,hq]
  rw [hsharp,hgauss] at h
  exact h

theorem d02PhysicalGaussianTruncatedDiagonalTimeMean_sharp_uniform
    {δ : ℝ} (hδ : 0 ≤ δ) (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ) (Φ : ℝ → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hOffset : |Real.log (2*Real.pi)|+Real.log 2 ≤ C)
    (hρc : ∀ k, Continuous (ρ k))
    (hρcap : ∀ k t, ρ k t ≠ 0 → t ∈ Icc 0 (a k))
    (hΦc : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc (1:ℝ) 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ ab : PolarShiftSpace,
      (∀ i, -C ≤ (ab.1 i).re) → (∀ i, -C ≤ (ab.2 i).re) →
      Integrable (fun τ : ℝ =>
        (Φ τ : ℂ)*d02PhysicalGaussianTruncatedDiagonalIntegral δ L ρ ab τ) ∧
      ‖d02PhysicalGaussianTruncatedDiagonalTimeMean δ L ρ ab Φ-
        ((∫ τ : ℝ, Φ τ : ℝ) : ℂ)*
          (∫ y, d01ComplexLaplaceWeight ab y*d02SharpLogTest (d02FourProfileProduct ρ) y
            ∂d01DiagonalMeasure L)‖ < ε := by
  let M := ∫ τ : ℝ, |Φ τ|
  have hM0 : 0 ≤ M := integral_nonneg (fun _ => abs_nonneg _)
  let η := ε/(M+1)
  have hη : 0 < η := div_pos hε (by linarith)
  filter_upwards [d02PhysicalGaussianTruncatedDiagonalIntegral_sharp_uniform hδ
    ρ a hC hOffset hρc hρcap hη] with L hL
  intro ab ha hbshift
  have h := d02_time_mean_error_bound (d02PhysicalGaussianTruncatedDiagonalIntegral δ L ρ ab)
    (∫ y, d01ComplexLaplaceWeight ab y*d02SharpLogTest (d02FourProfileProduct ρ) y
      ∂d01DiagonalMeasure L) Φ
    (d02PhysicalGaussianTruncatedDiagonalIntegral_measurable δ L ρ ab hρc)
    hΦc hΦs hη.le (fun τ hτ => (hL ab τ ha hbshift hτ).le)
  refine ⟨h.1,h.2.trans_lt ?_⟩
  change η*M < ε
  have he : η*(M+1) = ε := by
    dsimp [η]
    exact div_mul_cancel₀ ε (by linarith : M+1 ≠ 0)
  nlinarith

theorem d02PhysicalGaussianTruncatedDiagonalTimeMean_limit
    {δ : ℝ} (hδ : 0 ≤ δ) (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ)
    (ab : PolarShiftSpace) (Φ : ℝ → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hOffset : |Real.log (2*Real.pi)|+Real.log 2 ≤ C)
    (hρc : ∀ k, Continuous (ρ k))
    (hρcap : ∀ k t, ρ k t ≠ 0 → t ∈ Icc 0 (a k))
    (ha : ∀ i, -C ≤ (ab.1 i).re) (hbshift : ∀ i, -C ≤ (ab.2 i).re)
    (hΦc : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc (1:ℝ) 2) :
    Tendsto (fun L : ℝ => d02PhysicalGaussianTruncatedDiagonalTimeMean δ L ρ ab Φ) atTop
      (𝓝 (((∫ τ : ℝ, Φ τ : ℝ) : ℂ)*(arithmeticFactor : ℂ)*
        ∫ x : D01EdgeSpace, d01ComplexLaplaceWeight ab (d01RowColumnSums x)*
          d02SharpLogTest (d02FourProfileProduct ρ) (d01RowColumnSums x)
            ∂volume.restrict d01NonnegativeOrthant)) := by
  have herr : Tendsto (fun L : ℝ => d02PhysicalGaussianTruncatedDiagonalTimeMean δ L ρ ab Φ-
      ((∫ τ : ℝ, Φ τ : ℝ) : ℂ)*
        (∫ y, d01ComplexLaplaceWeight ab y*d02SharpLogTest (d02FourProfileProduct ρ) y
          ∂d01DiagonalMeasure L)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [d02PhysicalGaussianTruncatedDiagonalTimeMean_sharp_uniform hδ
      ρ a Φ hC hOffset hρc hρcap hΦc hΦs hε] with L hL
    simpa only [dist_zero_right] using (hL ab ha hbshift).2
  have hsharp := (d02DiagonalMeasure_four_profile_sharp_log_limit ρ a
    (d01ComplexLaplaceWeight ab) hρc hρcap (d01ComplexLaplaceWeight_continuous ab)).const_mul
      (((∫ τ : ℝ, Φ τ : ℝ) : ℂ))
  simpa only [sub_add_cancel,zero_add,mul_assoc] using herr.add hsharp

theorem d02GaussianTruncatedDiagonalPhysicalHeightMean_limit
    {δ : ℝ} (hδ : 0 ≤ δ) (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ)
    (ab : PolarShiftSpace) (Φ : ℝ → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hOffset : |Real.log (2*Real.pi)|+Real.log 2 ≤ C)
    (hρc : ∀ k, Continuous (ρ k))
    (hρcap : ∀ k t, ρ k t ≠ 0 → t ∈ Icc 0 (a k))
    (ha : ∀ i, -C ≤ (ab.1 i).re) (hbshift : ∀ i, -C ≤ (ab.2 i).re)
    (hΦc : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc (1:ℝ) 2) :
    Tendsto (fun T : ℝ => d02GaussianTruncatedDiagonalPhysicalHeightMean δ T ρ ab Φ) atTop
      (𝓝 (((∫ τ : ℝ, Φ τ : ℝ) : ℂ)*(arithmeticFactor : ℂ)*
        ∫ x : D01EdgeSpace, d01ComplexLaplaceWeight ab (d01RowColumnSums x)*
          d02SharpLogTest (d02FourProfileProduct ρ) (d01RowColumnSums x)
            ∂volume.restrict d01NonnegativeOrthant)) := by
  apply ((d02PhysicalGaussianTruncatedDiagonalTimeMean_limit hδ ρ a ab Φ hC hOffset
    hρc hρcap ha hbshift hΦc hΦs).comp Real.tendsto_log_atTop).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  exact (d02GaussianTruncatedDiagonalPhysicalHeightMean_eq hT δ ρ ab Φ).symm
theorem d02GaussianTruncatedDiagonalPhysicalHeightMean_limit_fixed_shifts
    {δ : ℝ} (hδ : 0 ≤ δ) (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ) (ab : PolarShiftSpace) (Φ : ℝ → ℝ)
    (hρc : ∀ k, Continuous (ρ k))
    (hρcap : ∀ k t, ρ k t ≠ 0 → t ∈ Icc 0 (a k))
    (hΦc : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc (1:ℝ) 2) :
    Tendsto (fun T : ℝ => d02GaussianTruncatedDiagonalPhysicalHeightMean δ T ρ ab Φ) atTop
      (𝓝 (((∫ τ : ℝ, Φ τ : ℝ) : ℂ)*(arithmeticFactor : ℂ)*
        ∫ x : D01EdgeSpace, d01ComplexLaplaceWeight ab (d01RowColumnSums x)*
          d02SharpLogTest (d02FourProfileProduct ρ) (d01RowColumnSums x)
            ∂volume.restrict d01NonnegativeOrthant)) := by
  let R := ∑ i : Fin 3, (|(ab.1 i).re|+|(ab.2 i).re|)
  let C := max (|Real.log (2*Real.pi)|+Real.log 2) R
  have hR0 : 0 ≤ R := Finset.sum_nonneg (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hRC : R ≤ C := le_max_right _ _
  have hC : 0 ≤ C := hR0.trans hRC
  have ha : ∀ i, -C ≤ (ab.1 i).re := by
    intro i
    have hs : |(ab.1 i).re|+|(ab.2 i).re| ≤ R :=
      Finset.single_le_sum
        (fun j _ => add_nonneg (abs_nonneg (ab.1 j).re) (abs_nonneg (ab.2 j).re))
        (Finset.mem_univ i)
    have hi : |(ab.1 i).re| ≤ R :=
      (le_add_of_nonneg_right (abs_nonneg (ab.2 i).re)).trans hs
    exact (neg_le_neg (hi.trans hRC)).trans (neg_abs_le _)
  have hb : ∀ i, -C ≤ (ab.2 i).re := by
    intro i
    have hs : |(ab.1 i).re|+|(ab.2 i).re| ≤ R :=
      Finset.single_le_sum
        (fun j _ => add_nonneg (abs_nonneg (ab.1 j).re) (abs_nonneg (ab.2 j).re))
        (Finset.mem_univ i)
    have hi : |(ab.2 i).re| ≤ R :=
      (le_add_of_nonneg_left (abs_nonneg (ab.1 i).re)).trans hs
    exact (neg_le_neg (hi.trans hRC)).trans (neg_abs_le _)
  exact d02GaussianTruncatedDiagonalPhysicalHeightMean_limit hδ ρ a ab Φ hC (le_max_left _ _)
    hρc hρcap ha hb hΦc hΦs


theorem d02PhysicalGaussianTruncatedDiagonalTimeMean_eventually_uniform_norm_bound
    {δ : ℝ} (hδ : 0 ≤ δ) (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ) (Φ : ℝ → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hOffset : |Real.log (2*Real.pi)|+Real.log 2 ≤ C)
    (hρc : ∀ k, Continuous (ρ k))
    (hρcap : ∀ k t, ρ k t ≠ 0 → t ∈ Icc 0 (a k))
    (hΦc : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc (1:ℝ) 2) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ L : ℝ in atTop, ∀ ab : PolarShiftSpace,
      (∀ i, -C ≤ (ab.1 i).re) → (∀ i, -C ≤ (ab.2 i).re) →
      Integrable (fun τ : ℝ =>
        (Φ τ : ℂ)*d02PhysicalGaussianTruncatedDiagonalIntegral δ L ρ ab τ) ∧
      ‖d02PhysicalGaussianTruncatedDiagonalTimeMean δ L ρ ab Φ‖ ≤ B := by
  obtain ⟨B,hB,hevent⟩ := d02PhysicalGaussianDiagonalTimeMean_eventually_uniform_norm_bound
    ρ a Φ hC hOffset hρc hρcap hΦc hΦs
  refine ⟨B+2,by linarith,?_⟩
  filter_upwards [hevent,
    d02PhysicalGaussianDiagonalTimeMean_sharp_uniform ρ a Φ hC hOffset
      hρc hρcap hΦc hΦs (by norm_num : (0:ℝ) < 1),
    d02PhysicalGaussianTruncatedDiagonalTimeMean_sharp_uniform hδ ρ a Φ hC hOffset
      hρc hρcap hΦc hΦs (by norm_num : (0:ℝ) < 1)] with L hBound hOriginal hTruncated
  intro ab ha hb
  have hB' := hBound ab ha hb
  have ho := hOriginal ab ha hb
  have ht := hTruncated ab ha hb
  refine ⟨ht.1,?_⟩
  let S := ((∫ τ : ℝ, Φ τ : ℝ) : ℂ)*
    (∫ y, d01ComplexLaplaceWeight ab y*d02SharpLogTest (d02FourProfileProduct ρ) y
      ∂d01DiagonalMeasure L)
  have hDiff : ‖d02PhysicalGaussianTruncatedDiagonalTimeMean δ L ρ ab Φ-
      d02PhysicalGaussianDiagonalTimeMean L ρ ab Φ‖ ≤ 2 := by
    have hTriangle := norm_sub_le_norm_sub_add_norm_sub
      (d02PhysicalGaussianTruncatedDiagonalTimeMean δ L ρ ab Φ) S
      (d02PhysicalGaussianDiagonalTimeMean L ρ ab Φ)
    have hReverse : ‖S-d02PhysicalGaussianDiagonalTimeMean L ρ ab Φ‖ < 1 := by
      simpa only [norm_sub_rev] using ho.2
    have hTr : ‖d02PhysicalGaussianTruncatedDiagonalTimeMean δ L ρ ab Φ-S‖ < 1 := ht.2
    exact hTriangle.trans (by linarith)
  calc
    _ = ‖(d02PhysicalGaussianTruncatedDiagonalTimeMean δ L ρ ab Φ-
        d02PhysicalGaussianDiagonalTimeMean L ρ ab Φ)+
          d02PhysicalGaussianDiagonalTimeMean L ρ ab Φ‖ := by rw [sub_add_cancel]
    _ ≤ ‖d02PhysicalGaussianTruncatedDiagonalTimeMean δ L ρ ab Φ-
        d02PhysicalGaussianDiagonalTimeMean L ρ ab Φ‖+
          ‖d02PhysicalGaussianDiagonalTimeMean L ρ ab Φ‖ := norm_add_le _ _
    _ ≤ 2+B := add_le_add hDiff hB'.2
    _ = B+2 := by ring

theorem d02GaussianTruncatedDiagonalPhysicalHeightMean_eventually_uniform_norm_bound
    {δ : ℝ} (hδ : 0 ≤ δ) (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ) (Φ : ℝ → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hOffset : |Real.log (2*Real.pi)|+Real.log 2 ≤ C)
    (hρc : ∀ k, Continuous (ρ k))
    (hρcap : ∀ k t, ρ k t ≠ 0 → t ∈ Icc 0 (a k))
    (hΦc : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc (1:ℝ) 2) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ T : ℝ in atTop, ∀ ab : PolarShiftSpace,
      (∀ i, -C ≤ (ab.1 i).re) → (∀ i, -C ≤ (ab.2 i).re) →
      Integrable (fun t : ℝ => (Φ (t/T) : ℂ)*
        (∫ y, d01ComplexLaplaceWeight ab y*d02GaussianTruncatedFourProfile δ ρ y*
          (d02GaussianV0 (2*Real.pi*Real.exp (Real.log T*d02LogCutCoordinate y)/t) : ℂ)
            ∂d01DiagonalMeasure (Real.log T))) ∧
      ‖d02GaussianTruncatedDiagonalPhysicalHeightMean δ T ρ ab Φ‖ ≤ B := by
  obtain ⟨B,hB,hevent⟩ :=
    d02PhysicalGaussianTruncatedDiagonalTimeMean_eventually_uniform_norm_bound hδ
      ρ a Φ hC hOffset hρc hρcap hΦc hΦs
  refine ⟨B,hB,?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually hevent,eventually_gt_atTop (0:ℝ)]
    with T hBound hT
  intro ab ha hb
  have h := hBound ab ha hb
  have hden (t : ℝ) : Real.exp (Real.log T)*(t/T) = t := by
    rw [Real.exp_log hT]
    field_simp [hT.ne']
  refine ⟨?_,?_⟩
  · apply (h.1.comp_div hT.ne').congr
    exact ae_of_all _ (fun t => by simp only [d02PhysicalGaussianTruncatedDiagonalIntegral,hden])
  · rw [d02GaussianTruncatedDiagonalPhysicalHeightMean_eq hT]
    exact h.2
theorem d02PhysicalGaussianTruncatedDiagonalIntegral_eventually_uniform_norm_bound
    {δ : ℝ} (hδ : 0 ≤ δ) (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hOffset : |Real.log (2*Real.pi)|+Real.log 2 ≤ C)
    (hρc : ∀ k, Continuous (ρ k))
    (hρcap : ∀ k t, ρ k t ≠ 0 → t ∈ Icc 0 (a k)) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ L : ℝ in atTop, ∀ (ab : PolarShiftSpace) (τ : ℝ),
      (∀ i, -C ≤ (ab.1 i).re) → (∀ i, -C ≤ (ab.2 i).re) → τ ∈ Icc (1:ℝ) 2 →
      ‖d02PhysicalGaussianTruncatedDiagonalIntegral δ L ρ ab τ‖ ≤ B := by
  have hρK : ∀ k, HasCompactSupport (ρ k) := by
    intro k
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := 0) (b := a k))
    intro t ht
    exact hρcap k t ht
  choose b hb using fun k => (hρK k).exists_bound_of_continuous (hρc k)
  have hb0 : ∀ k, 0 ≤ b k := fun k => (norm_nonneg (ρ k 0)).trans (hb k 0)
  let K := (b 0*b 1*b 2*b 3*Real.exp (C*d02ProfileCapSum a))*
    Real.exp (d02ProfileCapSum a)*Real.exp (C+1)
  let A := ∫ _y : D01LogSpace, (1:ℝ) ∂d02TiltedLimitMeasure
  let B := 1+K*(A+1)
  have hprod0 : 0 ≤ b 0*b 1*b 2*b 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (hb0 0) (hb0 1)) (hb0 2)) (hb0 3)
  have hK0 : 0 ≤ K := mul_nonneg
    (mul_nonneg (mul_nonneg hprod0 (Real.exp_pos _).le) (Real.exp_pos _).le)
    (Real.exp_pos _).le
  have hA0 : 0 ≤ A := integral_nonneg (fun _ => by norm_num)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  have hmass := d02TiltedDiagonalMeasure_mass_tendsto.eventually_lt_const
    (show (∫ _y : D01LogSpace, (1:ℝ) ∂d02TiltedLimitMeasure) < A+1 by
      dsimp [A]; linarith)
  filter_upwards [hmass, eventually_gt_atTop (0:ℝ),
    d02PhysicalGaussianTruncatedDiagonalIntegral_sharp_uniform hδ ρ a hC hOffset
      hρc hρcap (by norm_num : (0:ℝ) < 1)] with L hMass hL hError
  intro ab τ ha hbshift hτ
  let S := ∫ y, d01ComplexLaplaceWeight ab y*d02SharpLogTest (d02FourProfileProduct ρ) y
    ∂d01DiagonalMeasure L
  have hS : ‖S‖ ≤ K*(A+1) :=
    (d02DiagonalMeasure_shifted_four_profile_sharp_norm_bound ρ a b hC hL
      hρcap hb0 hb ab ha hbshift).trans
        (mul_le_mul_of_nonneg_left hMass.le hK0)
  have hE : ‖d02PhysicalGaussianTruncatedDiagonalIntegral δ L ρ ab τ-S‖ ≤ 1 :=
    (hError ab τ ha hbshift hτ).le
  calc
    _ = ‖(d02PhysicalGaussianTruncatedDiagonalIntegral δ L ρ ab τ-S)+S‖ := by rw [sub_add_cancel]
    _ ≤ ‖d02PhysicalGaussianTruncatedDiagonalIntegral δ L ρ ab τ-S‖+‖S‖ := norm_add_le _ _
    _ ≤ 1+K*(A+1) := add_le_add hE hS
    _ = B := rfl


end
end Sechstmoment
