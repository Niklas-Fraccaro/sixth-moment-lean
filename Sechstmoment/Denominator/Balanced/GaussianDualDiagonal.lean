import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Sechstmoment.Denominator.Balanced.GaussianPhysicalTimeMean
import Sechstmoment.Zeta.AFE.Two.DualPower

namespace Sechstmoment
open Complex Real Source MeasureTheory Filter Set
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 0

def d02PhysicalGaussianTruncatedDualDiagonalTimeMean (δ T : ℝ)
    (ρ : Fin 4 → ℝ → ℂ) (ab : PolarShiftSpace) (σ : SecondMomentShifts)
    (Φ : ℝ → ℝ) : ℂ :=
  ∫ τ : ℝ, (Φ τ : ℂ)*secondDualPower (T*τ) (rawSecondMomentShifts T σ)*
    d02PhysicalGaussianTruncatedDiagonalIntegral δ (Real.log T) ρ ab τ

def d02GaussianTruncatedDualDiagonalPhysicalHeightMean (δ T : ℝ)
    (ρ : Fin 4 → ℝ → ℂ) (ab : PolarShiftSpace) (σ : SecondMomentShifts)
    (Φ : ℝ → ℝ) : ℂ :=
  (∫ t : ℝ, (Φ (t/T) : ℂ)*secondDualPower t (rawSecondMomentShifts T σ)*
    (∫ y, d01ComplexLaplaceWeight ab y*d02GaussianTruncatedFourProfile δ ρ y*
      (d02GaussianV0 (2*Real.pi*Real.exp (Real.log T*d02LogCutCoordinate y)/t) : ℂ)
        ∂d01DiagonalMeasure (Real.log T))) / (T : ℂ)

theorem d02SecondDualPower_scaled_time_measurable (T : ℝ) (α : SecondMomentShifts) :
    Measurable (fun τ : ℝ => secondDualPower (T*τ) α) := by
  classical
  have hf : Measurable (fun τ : ℝ => ((T*τ/(2*Real.pi) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp ((measurable_const.mul measurable_id).div_const _)
  unfold secondDualPower
  simp_rw [Complex.cpow_def]
  exact Measurable.ite (measurableSet_eq_fun hf measurable_const) measurable_const
    (Complex.measurable_exp.comp ((Complex.measurable_log.comp hf).mul_const _))

theorem d02GaussianTruncatedDualDiagonalPhysicalHeightMean_eq {T : ℝ} (hT : 0<T)
    (δ : ℝ) (ρ : Fin 4 → ℝ → ℂ) (ab : PolarShiftSpace)
    (σ : SecondMomentShifts) (Φ : ℝ → ℝ) :
    d02GaussianTruncatedDualDiagonalPhysicalHeightMean δ T ρ ab σ Φ =
      d02PhysicalGaussianTruncatedDualDiagonalTimeMean δ T ρ ab σ Φ := by
  have hmul (t : ℝ) : T*(t/T)=t := mul_div_cancel₀ t hT.ne'
  have hden (t : ℝ) : Real.exp (Real.log T)*(t/T)=t := by
    rw [Real.exp_log hT,hmul]
  have he : (∫ t : ℝ, (Φ (t/T) : ℂ)*secondDualPower t (rawSecondMomentShifts T σ)*
      (∫ y, d01ComplexLaplaceWeight ab y*d02GaussianTruncatedFourProfile δ ρ y*
        (d02GaussianV0 (2*Real.pi*Real.exp (Real.log T*d02LogCutCoordinate y)/t) : ℂ)
          ∂d01DiagonalMeasure (Real.log T))) =
      ∫ t : ℝ, (Φ (t/T) : ℂ)*secondDualPower (T*(t/T)) (rawSecondMomentShifts T σ)*
        d02PhysicalGaussianTruncatedDiagonalIntegral δ (Real.log T) ρ ab (t/T) := by
    apply integral_congr_ae
    exact ae_of_all _ (fun t => by
      simp only [d02PhysicalGaussianTruncatedDiagonalIntegral,hden,hmul])
  unfold d02GaussianTruncatedDualDiagonalPhysicalHeightMean
  rw [he,Measure.integral_comp_div
    (fun τ : ℝ => (Φ τ : ℂ)*secondDualPower (T*τ) (rawSecondMomentShifts T σ)*
      d02PhysicalGaussianTruncatedDiagonalIntegral δ (Real.log T) ρ ab τ) T,
    abs_of_pos hT,Complex.real_smul]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hT.ne')

theorem d02PhysicalGaussianTruncatedDualDiagonalTimeMean_replacement_uniform
    {δ R C : ℝ} (hδ : 0≤δ) (hR : 0≤R) (hC : 0≤C)
    (hOffset : |Real.log (2*Real.pi)|+Real.log 2≤C)
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ) (Φ : ℝ → ℝ)
    (hρc : ∀ k,Continuous (ρ k))
    (hρcap : ∀ k t,ρ k t≠0 → t∈Icc 0 (a k))
    (hΦc : Continuous Φ) (hΦs : tsupport Φ⊆Icc (1:ℝ) 2)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ T : ℝ in atTop,∀ (σ : SecondMomentShifts) (ab : PolarShiftSpace),
      (∀ j,‖σ j‖≤R) → (∀ i,-C≤(ab.1 i).re) → (∀ i,-C≤(ab.2 i).re) →
      Integrable (fun τ : ℝ => (Φ τ : ℂ)*secondDualPower (T*τ) (rawSecondMomentShifts T σ)*
        d02PhysicalGaussianTruncatedDiagonalIntegral δ (Real.log T) ρ ab τ) ∧
      ‖d02PhysicalGaussianTruncatedDualDiagonalTimeMean δ T ρ ab σ Φ-
        Complex.exp (-(σ 0+σ 1))*
          d02PhysicalGaussianTruncatedDiagonalTimeMean δ (Real.log T) ρ ab Φ‖<ε := by
  obtain ⟨B,hB,hInner⟩ := d02PhysicalGaussianTruncatedDiagonalIntegral_eventually_uniform_norm_bound
    hδ ρ a hC hOffset hρc hρcap
  have hΦK : HasCompactSupport Φ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport Φ).trans hΦs)
  have hΦi : Integrable Φ := hΦc.integrable_of_hasCompactSupport hΦK
  let M := ∫ τ : ℝ, |Φ τ|
  have hM0 : 0≤M := integral_nonneg (fun _ => abs_nonneg _)
  let η := ε/(B*(M+1))
  have hη : 0<η := div_pos hε (mul_pos hB (by linarith))
  filter_upwards [Real.tendsto_log_atTop.eventually hInner,
    Real.tendsto_log_atTop.eventually
      (d02PhysicalGaussianTruncatedDiagonalTimeMean_sharp_uniform hδ ρ a Φ hC hOffset
        hρc hρcap hΦc hΦs (by norm_num : (0:ℝ)<1)),
    secondDualPower_uniform_normalized_window_tendsto hR hη] with T hI hBase hPower
  intro σ ab hσ ha hb
  let G := d02PhysicalGaussianTruncatedDiagonalIntegral δ (Real.log T) ρ ab
  let p := fun τ : ℝ => secondDualPower (T*τ) (rawSecondMomentShifts T σ)
  let c := Complex.exp (-(σ 0+σ 1))
  let E := fun τ : ℝ => (Φ τ : ℂ)*(p τ-c)*G τ
  have hGm : Measurable G :=
    d02PhysicalGaussianTruncatedDiagonalIntegral_measurable δ (Real.log T) ρ ab hρc
  have hpm : Measurable p := d02SecondDualPower_scaled_time_measurable T _
  have hEm : Measurable E :=
    ((Complex.measurable_ofReal.comp hΦc.measurable).mul (hpm.sub measurable_const)).mul hGm
  have hmajor : Integrable (fun τ : ℝ => (η*B)*|Φ τ|) := hΦi.abs.const_mul (η*B)
  have hdom : ∀ τ : ℝ,‖E τ‖≤(η*B)*|Φ τ| := by
    intro τ
    by_cases hΦτ : Φ τ=0
    · calc
        _ = 0 := by simp [E,hΦτ]
        _ ≤ _ := mul_nonneg (mul_pos hη hB).le (abs_nonneg _)
    have hτ : τ∈Icc (1:ℝ) 2 := hΦs (subset_tsupport Φ hΦτ)
    dsimp only [E]
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ (|Φ τ| * η)*B := mul_le_mul
        (mul_le_mul_of_nonneg_left (hPower τ hτ σ hσ).le (abs_nonneg _))
        (hI ab τ ha hb hτ) (norm_nonneg _) (mul_nonneg (abs_nonneg _) hη.le)
      _ = _ := by ring
  have hEi : Integrable E := hmajor.mono' hEm.aestronglyMeasurable (ae_of_all _ hdom)
  have hGi : Integrable (fun τ : ℝ => (Φ τ : ℂ)*G τ) := (hBase ab ha hb).1
  have hCi : Integrable (fun τ : ℝ => c*((Φ τ : ℂ)*G τ)) := hGi.const_mul c
  have hDual : Integrable (fun τ : ℝ => (Φ τ : ℂ)*p τ*G τ) := by
    apply (hEi.add hCi).congr
    exact ae_of_all _ (fun τ => by
      change (Φ τ : ℂ)*(p τ-c)*G τ+c*((Φ τ : ℂ)*G τ) = (Φ τ : ℂ)*p τ*G τ
      ring)
  refine ⟨hDual,?_⟩
  have he : d02PhysicalGaussianTruncatedDualDiagonalTimeMean δ T ρ ab σ Φ-
      c*d02PhysicalGaussianTruncatedDiagonalTimeMean δ (Real.log T) ρ ab Φ =
      ∫ τ : ℝ,E τ := by
    unfold d02PhysicalGaussianTruncatedDualDiagonalTimeMean
      d02PhysicalGaussianTruncatedDiagonalTimeMean
    rw [←integral_const_mul c (fun τ : ℝ => (Φ τ : ℂ)*G τ),←integral_sub hDual hCi]
    apply integral_congr_ae
    exact ae_of_all _ (fun τ => by
      change (Φ τ : ℂ)*p τ*G τ-c*((Φ τ : ℂ)*G τ) = (Φ τ : ℂ)*(p τ-c)*G τ
      ring)
  change ‖d02PhysicalGaussianTruncatedDualDiagonalTimeMean δ T ρ ab σ Φ-
    c*d02PhysicalGaussianTruncatedDiagonalTimeMean δ (Real.log T) ρ ab Φ‖<ε
  rw [he]
  apply lt_of_le_of_lt (norm_integral_le_of_norm_le hmajor (ae_of_all _ hdom))
  rw [integral_const_mul]
  change (η*B)*M<ε
  have heη : η*(B*(M+1))=ε := by
    dsimp [η]
    exact div_mul_cancel₀ ε (by positivity : B*(M+1)≠0)
  nlinarith [mul_pos hη hB]

theorem d02GaussianTruncatedDualDiagonalPhysicalHeightMean_replacement_uniform
    {δ R C : ℝ} (hδ : 0≤δ) (hR : 0≤R) (hC : 0≤C)
    (hOffset : |Real.log (2*Real.pi)|+Real.log 2≤C)
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ) (Φ : ℝ → ℝ)
    (hρc : ∀ k,Continuous (ρ k))
    (hρcap : ∀ k t,ρ k t≠0 → t∈Icc 0 (a k))
    (hΦc : Continuous Φ) (hΦs : tsupport Φ⊆Icc (1:ℝ) 2)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ T : ℝ in atTop,∀ (σ : SecondMomentShifts) (ab : PolarShiftSpace),
      (∀ j,‖σ j‖≤R) → (∀ i,-C≤(ab.1 i).re) → (∀ i,-C≤(ab.2 i).re) →
      Integrable (fun t : ℝ => (Φ (t/T) : ℂ)*secondDualPower t (rawSecondMomentShifts T σ)*
        (∫ y,d01ComplexLaplaceWeight ab y*d02GaussianTruncatedFourProfile δ ρ y*
          (d02GaussianV0 (2*Real.pi*Real.exp (Real.log T*d02LogCutCoordinate y)/t) : ℂ)
            ∂d01DiagonalMeasure (Real.log T))) ∧
      ‖d02GaussianTruncatedDualDiagonalPhysicalHeightMean δ T ρ ab σ Φ-
        Complex.exp (-(σ 0+σ 1))*d02GaussianTruncatedDiagonalPhysicalHeightMean δ T ρ ab Φ‖<ε := by
  filter_upwards [d02PhysicalGaussianTruncatedDualDiagonalTimeMean_replacement_uniform
    hδ hR hC hOffset ρ a Φ hρc hρcap hΦc hΦs hε,eventually_gt_atTop (0:ℝ)] with T hRep hT
  intro σ ab hσ ha hb
  have h := hRep σ ab hσ ha hb
  have hmul (t : ℝ) : T*(t/T)=t := mul_div_cancel₀ t hT.ne'
  have hden (t : ℝ) : Real.exp (Real.log T)*(t/T)=t := by rw [Real.exp_log hT,hmul]
  refine ⟨?_,?_⟩
  · apply (h.1.comp_div hT.ne').congr
    exact ae_of_all _ (fun t => by
      simp only [d02PhysicalGaussianTruncatedDiagonalIntegral,hden,hmul])
  · rw [d02GaussianTruncatedDualDiagonalPhysicalHeightMean_eq hT,
      d02GaussianTruncatedDiagonalPhysicalHeightMean_eq hT]
    exact h.2

theorem d02GaussianTruncatedDualDiagonalPhysicalHeightMean_replacement_tendsto
    {δ R C : ℝ} (hδ : 0≤δ) (hR : 0≤R) (hC : 0≤C)
    (hOffset : |Real.log (2*Real.pi)|+Real.log 2≤C)
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ) (Φ : ℝ → ℝ)
    (hρc : ∀ k,Continuous (ρ k))
    (hρcap : ∀ k t,ρ k t≠0 → t∈Icc 0 (a k))
    (hΦc : Continuous Φ) (hΦs : tsupport Φ⊆Icc (1:ℝ) 2)
    (σ : SecondMomentShifts) (ab : PolarShiftSpace)
    (hσ : ∀ j,‖σ j‖≤R) (ha : ∀ i,-C≤(ab.1 i).re) (hb : ∀ i,-C≤(ab.2 i).re) :
    Tendsto (fun T : ℝ => d02GaussianTruncatedDualDiagonalPhysicalHeightMean δ T ρ ab σ Φ-
      Complex.exp (-(σ 0+σ 1))*d02GaussianTruncatedDiagonalPhysicalHeightMean δ T ρ ab Φ)
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [d02GaussianTruncatedDualDiagonalPhysicalHeightMean_replacement_uniform
    hδ hR hC hOffset ρ a Φ hρc hρcap hΦc hΦs hε] with T hT
  simpa only [dist_zero_right] using (hT σ ab hσ ha hb).2

theorem d02GaussianTruncatedDualDiagonalPhysicalHeightMean_replacement_tendsto_fixed_shifts
    {δ : ℝ} (hδ : 0≤δ) (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ) (Φ : ℝ → ℝ)
    (hρc : ∀ k,Continuous (ρ k))
    (hρcap : ∀ k t,ρ k t≠0 → t∈Icc 0 (a k))
    (hΦc : Continuous Φ) (hΦs : tsupport Φ⊆Icc (1:ℝ) 2)
    (σ : SecondMomentShifts) (ab : PolarShiftSpace) :
    Tendsto (fun T : ℝ => d02GaussianTruncatedDualDiagonalPhysicalHeightMean δ T ρ ab σ Φ-
      Complex.exp (-(σ 0+σ 1))*d02GaussianTruncatedDiagonalPhysicalHeightMean δ T ρ ab Φ)
      atTop (𝓝 0) := by
  let R := ‖σ 0‖+‖σ 1‖
  have hR : 0≤R := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hσ : ∀ j,‖σ j‖≤R := by
    intro j
    fin_cases j
    · exact le_add_of_nonneg_right (norm_nonneg _)
    · exact le_add_of_nonneg_left (norm_nonneg _)
  let A := ∑ i : Fin 3, (|(ab.1 i).re|+|(ab.2 i).re|)
  let C := max (|Real.log (2*Real.pi)|+Real.log 2) A
  have hA0 : 0≤A := Finset.sum_nonneg (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hAC : A≤C := le_max_right _ _
  have hC : 0≤C := hA0.trans hAC
  have ha : ∀ i,-C≤(ab.1 i).re := by
    intro i
    have hi : |(ab.1 i).re|+|(ab.2 i).re|≤A := Finset.single_le_sum
      (fun j _ => add_nonneg (abs_nonneg (ab.1 j).re) (abs_nonneg (ab.2 j).re)) (Finset.mem_univ i)
    have hi' : |(ab.1 i).re|≤A :=
      (le_add_of_nonneg_right (abs_nonneg (ab.2 i).re)).trans hi
    exact (neg_le_neg (hi'.trans hAC)).trans (neg_abs_le _)
  have hb : ∀ i,-C≤(ab.2 i).re := by
    intro i
    have hi : |(ab.1 i).re|+|(ab.2 i).re|≤A := Finset.single_le_sum
      (fun j _ => add_nonneg (abs_nonneg (ab.1 j).re) (abs_nonneg (ab.2 j).re)) (Finset.mem_univ i)
    have hi' : |(ab.2 i).re|≤A :=
      (le_add_of_nonneg_left (abs_nonneg (ab.1 i).re)).trans hi
    exact (neg_le_neg (hi'.trans hAC)).trans (neg_abs_le _)
  exact d02GaussianTruncatedDualDiagonalPhysicalHeightMean_replacement_tendsto
    hδ hR hC (le_max_left _ _) ρ a Φ hρc hρcap hΦc hΦs σ ab hσ ha hb

theorem d02GaussianTruncatedDualDiagonalPhysicalHeightMean_eventually_uniform_norm_bound
    {δ R C : ℝ} (hδ : 0≤δ) (hR : 0≤R) (hC : 0≤C)
    (hOffset : |Real.log (2*Real.pi)|+Real.log 2≤C)
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ) (Φ : ℝ → ℝ)
    (hρc : ∀ k,Continuous (ρ k))
    (hρcap : ∀ k t,ρ k t≠0 → t∈Icc 0 (a k))
    (hΦc : Continuous Φ) (hΦs : tsupport Φ⊆Icc (1:ℝ) 2) :
    ∃ B : ℝ,0<B ∧ ∀ᶠ T : ℝ in atTop,∀ (σ : SecondMomentShifts) (ab : PolarShiftSpace),
      (∀ j,‖σ j‖≤R) → (∀ i,-C≤(ab.1 i).re) → (∀ i,-C≤(ab.2 i).re) →
      Integrable (fun t : ℝ => (Φ (t/T) : ℂ)*secondDualPower t (rawSecondMomentShifts T σ)*
        (∫ y,d01ComplexLaplaceWeight ab y*d02GaussianTruncatedFourProfile δ ρ y*
          (d02GaussianV0 (2*Real.pi*Real.exp (Real.log T*d02LogCutCoordinate y)/t) : ℂ)
            ∂d01DiagonalMeasure (Real.log T))) ∧
      ‖d02GaussianTruncatedDualDiagonalPhysicalHeightMean δ T ρ ab σ Φ‖≤B := by
  obtain ⟨B,hB,hevent⟩ := d02GaussianTruncatedDiagonalPhysicalHeightMean_eventually_uniform_norm_bound
    hδ ρ a Φ hC hOffset hρc hρcap hΦc hΦs
  refine ⟨1+Real.exp (2*R)*B,by positivity,?_⟩
  filter_upwards [hevent,d02GaussianTruncatedDualDiagonalPhysicalHeightMean_replacement_uniform
    hδ hR hC hOffset ρ a Φ hρc hρcap hΦc hΦs (by norm_num : (0:ℝ)<1)] with T hBase hRep
  intro σ ab hσ ha hb
  have h := hRep σ ab hσ ha hb
  refine ⟨h.1,?_⟩
  have hc : ‖Complex.exp (-(σ 0+σ 1))‖≤Real.exp (2*R) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    apply (Complex.re_le_norm _).trans
    rw [norm_neg]
    exact (norm_add_le _ _).trans (by linarith [hσ 0,hσ 1])
  calc
    _ = ‖(d02GaussianTruncatedDualDiagonalPhysicalHeightMean δ T ρ ab σ Φ-
        Complex.exp (-(σ 0+σ 1))*d02GaussianTruncatedDiagonalPhysicalHeightMean δ T ρ ab Φ)+
          Complex.exp (-(σ 0+σ 1))*d02GaussianTruncatedDiagonalPhysicalHeightMean δ T ρ ab Φ‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖d02GaussianTruncatedDualDiagonalPhysicalHeightMean δ T ρ ab σ Φ-
        Complex.exp (-(σ 0+σ 1))*d02GaussianTruncatedDiagonalPhysicalHeightMean δ T ρ ab Φ‖+
          ‖Complex.exp (-(σ 0+σ 1))*d02GaussianTruncatedDiagonalPhysicalHeightMean δ T ρ ab Φ‖ :=
      norm_add_le _ _
    _ ≤ 1+Real.exp (2*R)*B := by
      rw [norm_mul]
      exact add_le_add h.2.le (mul_le_mul hc (hBase ab ha hb).2 (norm_nonneg _) (Real.exp_pos _).le)

end
end Sechstmoment
